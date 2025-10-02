import time  
import threading  
import random  
import tkinter as tk  
from tkinter import ttk, messagebox  
from collections import namedtuple, defaultdict  
  
# -------------------------  
# 基础常量与转换  
# -------------------------  
def rc_to_sq(r, c): return r * 9 + c  
def sq_to_rc(sq): return divmod(sq, 9)  
  
KING, ADVISOR, ELEPHANT, HORSE, ROOK, CANNON, PAWN = 1,2,3,4,5,6,7  
  
ORTH = [(-1,0),(1,0),(0,-1),(0,1)]  
KNIGHT_JUMPS = [(-2,-1),(-2,1),(-1,-2),(-1,2),(1,-2),(1,2),(2,-1),(2,1)]  
ELE_PH = [(-2,-2),(-2,2),(2,-2),(2,2)]  
ADVS = [(-1,-1),(-1,1),(1,-1),(1,1)]  
  
# 初始局面（90字符 FEN-like）  
START_FEN = (  
    "rheakaehr"  
    "........."  
    ".c.....c."  
    "p.p.p.p.p"  
    "........."  
    "........."  
    "P.P.P.P.P"  
    ".C.....C."  
    "........."  
    "RHEAKAEHR"  
)  
  
PIECE_CHAR_TO_CODE = {  
    'k': -KING, 'a': -ADVISOR, 'e': -ELEPHANT, 'h': -HORSE, 'r': -ROOK, 'c': -CANNON, 'p': -PAWN,  
    'K': KING,  'A': ADVISOR,  'E': ELEPHANT,  'H': HORSE,  'R': ROOK,  'C': CANNON,  'P': PAWN,  
    '.': 0  
}  
CODE_TO_CHAR = {v:k for k,v in PIECE_CHAR_TO_CODE.items()}  
  
CODE_TO_TEXT = {  
    KING: '帅', -KING: '将',  
    ADVISOR: '仕', -ADVISOR: '士',  
    ELEPHANT: '相', -ELEPHANT: '象',  
    HORSE: '马', -HORSE: '馬',  
    ROOK: '车', -ROOK: '車',  
    CANNON: '炮', -CANNON: '砲',  
    PAWN: '兵', -PAWN: '卒',  
    0: ''  
}  
  
# -------------------------  
# 评估参数（可调整）  
# -------------------------  
PIECE_VALUES = {  
    KING:  100000,  
    ADVISOR:  110,  
    ELEPHANT: 110,  
    HORSE:  300,  
    ROOK:  600,  
    CANNON: 350,  
    PAWN:  70  
}  
  
# 简单 PSQT（示例性权重，90 长度）  
# 为可读性，使用小的示范表——可扩展为更精细的 90 元素表  
def make_constant_psqt(val):  
    return [val]*90  
  
PSQT = {  
    KING: make_constant_psqt(0),  
    ADVISOR: make_constant_psqt(3),  
    ELEPHANT: make_constant_psqt(2),  
    HORSE: make_constant_psqt(10),  
    ROOK: make_constant_psqt(20),  
    CANNON: make_constant_psqt(12),  
    PAWN: make_constant_psqt(5)  
}  
  
# -------------------------  
# Zobrist 哈希（用于置换表）  
# -------------------------  
_random = random.Random(0xC0FFEE)  
ZOBRIST_PIECE = [[_random.getrandbits(64) for _ in range(90)] for __ in range(15)]  
# piece index mapping: map piece code to index 0..14 (positive red pieces 1..7 -> 0..6, black -1..-7 -> 7..13)  
def piece_to_index(piece):  
    if piece == 0: return None  
    if piece > 0: return piece - 1  
    return 7 + (-piece - 1)  
  
ZOBRIST_SIDE = _random.getrandbits(64)  
  
def compute_zobrist(squares, red_to_move):  
    h = 0  
    for sq, p in enumerate(squares):  
        if p != 0:  
            idx = piece_to_index(p)  
            h ^= ZOBRIST_PIECE[idx][sq]  
    if not red_to_move:  
        h ^= ZOBRIST_SIDE  
    return h  
  
# -------------------------  
# 置换表条目  
# -------------------------  
TTEntry = namedtuple('TTEntry', ['zkey','depth','score','flag','best','pv'])  
  
# -------------------------  
# 棋盘类（含 is_attacked, 合法着法过滤等）  
# -------------------------  
class Board:  
    def __init__(self, fen=START_FEN, red_to_move=True):  
        self.squares = [0]*90  
        if len(fen) == 90:  
            for i,ch in enumerate(fen):  
                self.squares[i] = PIECE_CHAR_TO_CODE.get(ch,0)  
        else:  
            raise ValueError("FEN 长度应为90")  
        self.red_to_move = red_to_move  
        self.history = []  # list of (frm,to,piece,captured,zkey)  
        self.zkey = compute_zobrist(self.squares, self.red_to_move)  
        self.tt = {}  # zobrist -> TTEntry  
        self.nodes = 0  
        # heuristics  
        self.killer = defaultdict(lambda: [None, None])  # killer[depth] = [move1, move2]  
        self.history_table = defaultdict(int)  # history[(piece,from,to)] = score  
  
    def clone(self):  
        b = Board()  
        b.squares = self.squares[:]  
        b.red_to_move = self.red_to_move  
        b.history = self.history[:]  
        b.zkey = self.zkey  
        b.tt = self.tt  
        b.nodes = self.nodes  
        b.killer = self.killer  
        b.history_table = self.history_table  
        return b  
  
    def in_board(self, r,c):  
        return 0 <= r < 10 and 0 <= c < 9  
  
    def in_palace(self, r, c, is_red):  
        if is_red:  
            return 7 <= r <= 9 and 3 <= c <= 5  
        else:  
            return 0 <= r <= 2 and 3 <= c <= 5  
  
    def crossed_river(self, r, is_red):  
        return r <= 4 if is_red else r >= 5  
  
    def piece_at(self, sq): return self.squares[sq]  
  
    def find_king(self, is_red):  
        target = KING if is_red else -KING  
        for i,p in enumerate(self.squares):  
            if p == target: return i  
        return None  
  
    def make_move(self, mv):  
        frm, to = mv  
        piece = self.squares[frm]  
        captured = self.squares[to]  
        # update zkey incrementally  
        idx_from = piece_to_index(piece)  
        if idx_from is not None:  
            self.zkey ^= ZOBRIST_PIECE[idx_from][frm]  
        if captured != 0:  
            idx_cap = piece_to_index(captured)  
            self.zkey ^= ZOBRIST_PIECE[idx_cap][to]  
        # put piece to 'to'  
        self.squares[to] = piece  
        self.squares[frm] = 0  
        idx_to = piece_to_index(piece)  
        if idx_to is not None:  
            self.zkey ^= ZOBRIST_PIECE[idx_to][to]  
        # side to move flip  
        self.red_to_move = not self.red_to_move  
        self.zkey ^= ZOBRIST_SIDE  
        self.history.append((frm,to,piece,captured))  
  
    def undo_move(self):  
        frm,to,piece,captured = self.history.pop()  
        # flip side and zobrist back  
        self.zkey ^= ZOBRIST_SIDE  
        self.red_to_move = not self.red_to_move  
        # remove piece from to  
        idx_to = piece_to_index(piece)  
        if idx_to is not None:  
            self.zkey ^= ZOBRIST_PIECE[idx_to][to]  
        self.squares[frm] = piece  
        # restore captured  
        self.squares[to] = captured  
        if captured != 0:  
            idx_cap = piece_to_index(captured)  
            self.zkey ^= ZOBRIST_PIECE[idx_cap][to]  
        if piece != 0:  
            idx_from = piece_to_index(piece)  
            if idx_from is not None:  
                self.zkey ^= ZOBRIST_PIECE[idx_from][frm]  
  
    # is_attacked(sq, by_red)  
    def is_attacked(self, sq, by_red):  
        tr, tc = sq_to_rc(sq)  
        # pawn attacks: check pawn origins that could move to sq  
        if by_red:  
            # red pawn origins: forward origin (tr+1,tc)  
            orr, orc = tr+1, tc  
            if self.in_board(orr,orc) and self.squares[rc_to_sq(orr,orc)] == PAWN:  
                return True  
            # sideways if pawn has crossed river (origin must be on red side of river: orr <=4)  
            for orc in (tc-1, tc+1):  
                orr = tr  
                if self.in_board(orr, orc) and self.squares[rc_to_sq(orr,orc)] == PAWN:  
                    # ensure this pawn could move sideways (i.e., it's already crossed)  
                    if orr <= 4:  
                        return True  
        else:  
            orr, orc = tr-1, tc  
            if self.in_board(orr,orc) and self.squares[rc_to_sq(orr,orc)] == -PAWN:  
                return True  
            for orc in (tc-1, tc+1):  
                orr = tr  
                if self.in_board(orr,orc) and self.squares[rc_to_sq(orr,orc)] == -PAWN:  
                    if orr >= 5:  
                        return True  
  
        # horse: check origins and leg empty  
        for dr,dc in KNIGHT_JUMPS:  
            orr = tr - dr; orc = tc - dc  
            if not self.in_board(orr,orc): continue  
            p = self.squares[rc_to_sq(orr,orc)]  
            if by_red and p == HORSE:  
                # leg  
                leg_r = orr + (dr//2) if abs(dr)==2 else orr + dr  
                leg_c = orc + (dc//2) if abs(dc)==2 else orc + dc  
                if self.in_board(leg_r,leg_c) and self.squares[rc_to_sq(leg_r,leg_c)]==0:  
                    return True  
            if (not by_red) and p == -HORSE:  
                leg_r = orr + (dr//2) if abs(dr)==2 else orr + dr  
                leg_c = orc + (dc//2) if abs(dc)==2 else orc + dc  
                if self.in_board(leg_r,leg_c) and self.squares[rc_to_sq(leg_r,leg_c)]==0:  
                    return True  
  
        # rook/king orthogonal sliding  
        for dr,dc in ORTH:  
            nr,nc = tr+dr, tc+dc  
            while self.in_board(nr,nc):  
                p = self.squares[rc_to_sq(nr,nc)]  
                if p != 0:  
                    if by_red and (p == ROOK or p == KING):  
                        return True  
                    if (not by_red) and (p == -ROOK or p == -KING):  
                        return True  
                    break  
                nr += dr; nc += dc  
  
        # cannon (need exactly one screen)  
        for dr,dc in ORTH:  
            nr,nc = tr+dr, tc+dc  
            screen = False  
            while self.in_board(nr,nc):  
                p = self.squares[rc_to_sq(nr,nc)]  
                if p != 0:  
                    if not screen:  
                        screen = True  
                    else:  
                        if by_red and p == CANNON: return True  
                        if (not by_red) and p == -CANNON: return True  
                        break  
                nr += dr; nc += dc  
  
        # advisor diagonal one-step  
        for dr,dc in ADVS:  
            orr, orc = tr - dr, tc - dc  
            if not self.in_board(orr,orc): continue  
            p = self.squares[rc_to_sq(orr,orc)]  
            if by_red and p == ADVISOR: return True  
            if (not by_red) and p == -ADVISOR: return True  
  
        # elephant: two-step diagonal with middle empty  
        for dr,dc in ELE_PH:  
            orr, orc = tr - dr, tc - dc  
            mr,mc = tr - dr//2, tc - dc//2  
            if not self.in_board(orr,orc): continue  
            if not self.in_board(mr,mc): continue  
            if self.squares[rc_to_sq(mr,mc)] != 0: continue  
            p = self.squares[rc_to_sq(orr,orc)]  
            if by_red and p == ELEPHANT: return True  
            if (not by_red) and p == -ELEPHANT: return True  
  
        return False  
  
    def is_in_check(self, is_red):  
        ksq = self.find_king(is_red)  
        if ksq is None: return True  
        return self.is_attacked(ksq, by_red = not is_red)  
  
    # 生成所有粗略走法（不过滤使自身被将的走法）  
    def generate_pseudo_legal(self):  
        moves = []  
        stm_red = self.red_to_move  
        for sq, piece in enumerate(self.squares):  
            if piece == 0: continue  
            if (piece>0) != stm_red: continue  
            r,c = sq_to_rc(sq)  
            ap = abs(piece)  
            if ap == ROOK:  
                for dr,dc in ORTH:  
                    nr,nc = r+dr, c+dc  
                    while self.in_board(nr,nc):  
                        nsq = rc_to_sq(nr,nc)  
                        if self.squares[nsq]==0:  
                            moves.append((sq,nsq))  
                        else:  
                            if (self.squares[nsq]>0)!=(piece>0):  
                                moves.append((sq,nsq))  
                            break  
                        nr+=dr; nc+=dc  
            elif ap == CANNON:  
                for dr,dc in ORTH:  
                    nr,nc = r+dr,c+dc  
                    while self.in_board(nr,nc):  
                        nsq=rc_to_sq(nr,nc)  
                        if self.squares[nsq]==0:  
                            moves.append((sq,nsq))  
                        else:  
                            break  
                        nr+=dr; nc+=dc  
                for dr,dc in ORTH:  
                    nr,nc = r+dr,c+dc  
                    while self.in_board(nr,nc) and self.squares[rc_to_sq(nr,nc)]==0:  
                        nr+=dr; nc+=dc  
                    if not self.in_board(nr,nc): continue  
                    nr+=dr; nc+=dc  
                    while self.in_board(nr,nc):  
                        nsq=rc_to_sq(nr,nc)  
                        if self.squares[nsq]!=0:  
                            if (self.squares[nsq]>0)!=(piece>0):  
                                moves.append((sq,nsq))  
                            break  
                        nr+=dr; nc+=dc  
            elif ap == HORSE:  
                for dr,dc in KNIGHT_JUMPS:  
                    nr, nc = r+dr, c+dc  
                    if not self.in_board(nr,nc): continue  
                    leg_r = r + (dr//2) if abs(dr)==2 else r + dr  
                    leg_c = c + (dc//2) if abs(dc)==2 else c + dc  
                    if not self.in_board(leg_r,leg_c): continue  
                    if self.squares[rc_to_sq(leg_r,leg_c)] != 0: continue  
                    nsq = rc_to_sq(nr,nc)  
                    if self.squares[nsq]==0 or (self.squares[nsq]>0)!=(piece>0):  
                        moves.append((sq,nsq))  
            elif ap == ELEPHANT:  
                for dr,dc in ELE_PH:  
                    nr,nc = r+dr,c+dc  
                    if not self.in_board(nr,nc): continue  
                    mr,mc = r+dr//2, c+dc//2  
                    if self.squares[rc_to_sq(mr,mc)] != 0: continue  
                    # 象不能过河  
                    if piece>0 and nr <= 4: continue  
                    if piece<0 and nr >= 5: continue  
                    nsq = rc_to_sq(nr,nc)  
                    if self.squares[nsq]==0 or (self.squares[nsq]>0)!=(piece>0):  
                        moves.append((sq,nsq))  
            elif ap == ADVISOR:  
                for dr,dc in ADVS:  
                    nr,nc = r+dr,c+dc  
                    if not self.in_board(nr,nc): continue  
                    if not self.in_palace(nr,nc,piece>0): continue  
                    nsq = rc_to_sq(nr,nc)  
                    if self.squares[nsq]==0 or (self.squares[nsq]>0)!=(piece>0):  
                        moves.append((sq,nsq))  
            elif ap == KING:  
                for dr,dc in ORTH:  
                    nr,nc = r+dr,c+dc  
                    if not self.in_board(nr,nc): continue  
                    if not self.in_palace(nr,nc,piece>0): continue  
                    nsq=rc_to_sq(nr,nc)  
                    if self.squares[nsq]==0 or (self.squares[nsq]>0)!=(piece>0):  
                        moves.append((sq,nsq))  
            elif ap == PAWN:  
                forward = -1 if piece>0 else 1  
                nr, nc = r+forward, c  
                if self.in_board(nr,nc):  
                    nsq=rc_to_sq(nr,nc)  
                    if self.squares[nsq]==0 or (self.squares[nsq]>0)!=(piece>0):  
                        moves.append((sq,nsq))  
                if self.crossed_river(r,piece>0):  
                    for dc in (-1,1):  
                        nr, nc = r, c+dc  
                        if not self.in_board(nr,nc): continue  
                        nsq=rc_to_sq(nr,nc)  
                        if self.squares[nsq]==0 or (self.squares[nsq]>0)!=(piece>0):  
                            moves.append((sq,nsq))  
        return moves  
  
    # 过滤掉会使己方被将的走法（合法走法）  
    def generate_moves(self):  
        moves = self.generate_pseudo_legal()  
        legal = []  
        for mv in moves:  
            self.make_move(mv)  
            illegal = False  
            # kings face  
            pos = [i for i,p in enumerate(self.squares) if abs(p)==KING]  
            if len(pos)==2:  
                r1,c1 = sq_to_rc(pos[0]); r2,c2 = sq_to_rc(pos[1])  
                if c1 == c2:  
                    a = min(pos[0],pos[1])+1; b = max(pos[0],pos[1])  
                    blocked=False  
                    for s in range(a,b):  
                        if self.squares[s] != 0:  
                            blocked=True; break  
                    if not blocked:  
                        illegal=True  
            if not illegal:  
                # if the side who just moved (opponent now) can capture our king -> illegal  
                if self.is_in_check(not self.red_to_move):  
                    illegal = True  
            self.undo_move()  
            if not illegal:  
                legal.append(mv)  
        return legal  
  
    # 评估：子力 + PSQT + 简单活跃/兵推进/王安全  
    def evaluate(self):  
        score = 0  
        for sq,p in enumerate(self.squares):  
            if p==0: continue  
            val = PIECE_VALUES.get(abs(p),0)  
            val += PSQT.get(abs(p), [0]*90)[sq]  
            # pawn advancement bonus  
            if abs(p)==PAWN:  
                r,c = sq_to_rc(sq)  
                if p>0:  
                    val += (9 - r)  # 红兵越往前分越高  
                else:  
                    val += r  # 黑卒越往下分越高  
            score += val if p>0 else -val  
        # mobility small bonus  
        try:  
            mob = len(self.generate_moves())  
            score += 0.1 * mob if self.red_to_move else -0.1 * mob  
        except Exception:  
            pass  
        # final: return score from side-to-move perspective  
        return score if self.red_to_move else -score  
  
    def is_terminal(self):  
        kings = sum(1 for p in self.squares if abs(p)==KING)  
        if kings < 2: return True  
        if len(self.generate_moves()) == 0: return True  
        return False  
  
    def pretty(self):  
        out=[]  
        for r in range(10):  
            row=[]  
            for c in range(9):  
                ch = CODE_TO_CHAR.get(self.squares[rc_to_sq(r,c)], '.')  
                row.append(ch)  
            out.append(''.join(row))  
        return '\n'.join(out)  
  
# -------------------------  
# 搜索：iterative deepening + alpha-beta + qsearch + move ordering + TT + PV  
# -------------------------  
INF = 10**9  
  
# MVV/LVA ordering score for captures  
MVV_LVA = {}  
# attacker piece type (abs) 1..7, victim 1..7 -> value  
for attacker in range(1,8):  
    for victim in range(1,8):  
        MVV_LVA[(attacker, victim)] = PIECE_VALUES[victim]*100 - PIECE_VALUES[attacker]  
  
def score_move(board, mv, tt_move, depth):  
    frm,to = mv  
    victim = board.squares[to]  
    attacker = board.squares[frm]  
    # TT move highest priority  
    if tt_move and mv == tt_move: return 1000000  
    # captures  
    if victim != 0:  
        return 100000 + MVV_LVA[(abs(attacker), abs(victim))]  
    # killer heuristic  
    killers = board.killer.get(depth, [None, None])  
    if killers[0] == mv: return 90000  
    if killers[1] == mv: return 80000  
    # history heuristic  
    return board.history_table.get((abs(attacker), frm, to), 0)  
  
def quiescence(board, alpha, beta):  
    stand = board.evaluate()  
    if stand >= beta: return beta  
    if alpha < stand: alpha = stand  
    # generate captures only  
    moves = []  
    for mv in board.generate_moves():  
        if board.squares[mv[1]] != 0:  
            moves.append(mv)  
    # order captures  
    moves.sort(key=lambda m: MVV_LVA.get((abs(board.squares[m[0]]), abs(board.squares[m[1]])), 0), reverse=True)  
    for mv in moves:  
        board.make_move(mv)  
        val = -quiescence(board, -beta, -alpha)  
        board.undo_move()  
        if val >= beta: return beta  
        if val > alpha: alpha = val  
    return alpha  
  
# principal variation helper: extract pv from TT  
def extract_pv(board, depth):  
    pv=[]  
    cur = board.clone()  
    for _ in range(depth):  
        tt = cur.tt.get(cur.zkey)  
        if not tt or not tt.best: break  
        mv = tt.best  
        pv.append(mv)  
        cur.make_move(mv)  
    return pv  
  
# negamax alpha-beta with TT and move ordering  
def alphabeta(board, depth, alpha, beta, ply, max_depth, start_time, time_limit, stop_flag):  
    # time cutoff  
    if stop_flag and stop_flag.is_set():  
        raise TimeoutError()  
    if time_limit and (time.time() - start_time) > time_limit:  
        if stop_flag:  
            stop_flag.set()  
        raise TimeoutError()  
  
    board.nodes += 1  
    # TT lookup  
    tt = board.tt.get(board.zkey)  
    if tt and tt.depth >= depth:  
        if tt.flag == 0:  
            return tt.score  
        if tt.flag < 0:  
            alpha = max(alpha, tt.score)  
        else:  
            beta = min(beta, tt.score)  
        if alpha >= beta:  
            return tt.score  
  
    if depth == 0:  
        return quiescence(board, alpha, beta)  
  
    legal = board.generate_moves()  
    if not legal:  
        return -INF + ply  
  
    # move ordering: score each  
    tt_move = tt.best if tt else None  
    legal.sort(key=lambda m: score_move(board, m, tt_move, ply), reverse=True)  
  
    best_score = -INF  
    best_move = None  
  
    for mv in legal:  
        board.make_move(mv)  
        try:  
            val = -alphabeta(board, depth-1, -beta, -alpha, ply+1, max_depth, start_time, time_limit, stop_flag)  
        except TimeoutError:  
            board.undo_move()  
            raise  
        board.undo_move()  
  
        if val > best_score:  
            best_score = val; best_move = mv  
        if val > alpha:  
            alpha = val  
        if alpha >= beta:  
            # store killer / history  
            killers = board.killer.get(ply, [None, None])  
            if killers[0] != mv:  
                killers[1] = killers[0]; killers[0] = mv  
                board.killer[ply] = killers  
            # history score  
            attacker = abs(board.squares[mv[0]]) if board.squares[mv[0]]!=0 else 0  
            board.history_table[(attacker, mv[0], mv[1])] += 2 ** depth  
            break  
  
    # store in TT  
    # 修正海象运算符用法
    alpha_orig = alpha
    flag = 0  
    if best_score <= alpha_orig: flag = -1  
    if best_score >= beta: flag = 1  
    if alpha_orig < best_score < beta: flag = 0  
    # But alpha may have been modified; adjust flags correctly:  
    if best_score <= alpha: flag = -1  
    elif best_score >= beta: flag = 1  
    else: flag = 0  
  
    # PV extraction (shallow)  
    pv = []  
    if best_move:  
        # store best move + try to build pv from child table  
        board_tt_clone = board.clone()  
        board_tt_clone.make_move(best_move)  
        child_tt = board.tt.get(board_tt_clone.zkey)  
        if child_tt and child_tt.pv:  
            pv = [best_move] + child_tt.pv  
        else:  
            pv = [best_move]  
  
    board.tt[board.zkey] = TTEntry(board.zkey, depth, best_score, flag, best_move, pv)  
    return best_score  
  
# iterative deepening wrapper  
def search_best_move(board, max_depth=4, time_limit=None, stop_flag=None, info_callback=None):  
    best = None  
    start = time.time()  
    for d in range(1, max_depth+1):  
        try:  
            score = alphabeta(board, d, -INF, INF, 0, d, start, time_limit, stop_flag)  
        except TimeoutError:  
            break  
        # read best from TT  
        tt = board.tt.get(board.zkey)  
        if tt and tt.best:  
            best = tt.best  
        # call info callback with current info (depth, score, pv, nodes)  
        if info_callback:  
            pv = extract_pv(board, d)  
            info_callback(depth=d, score=score, pv=pv, nodes=board.nodes, time_spent = time.time()-start)  
        # time cutoff check  
        if time_limit and (time.time() - start) > time_limit:  
            break  
    return best  
  
# -------------------------  
# GUI (Tkinter)  
# -------------------------  
class XiangqiGUI:  
    CELL = 60  
    ANIMATION_STEPS = 12  # 动画帧数
    ANIMATION_DELAY = 20  # 每帧毫秒

    def __init__(self, master):  
        self.master = master  
        master.title("Xiangqi Strong AI")  
        self.board = Board()  
        self.selected = None  
        self.engine_thread = None  
        self.engine_stop = threading.Event()  
        self.engine_thinking = False  
  
        # engine settings  
        self.engine_time = tk.DoubleVar(value=2.0)  # seconds  
        self.engine_depth = tk.IntVar(value=4)  
        self.show_pv = tk.StringVar(value="")  
  
        # UI layout  
        left = tk.Frame(master); left.pack(side=tk.LEFT, padx=10, pady=10)  
        right = tk.Frame(master); right.pack(side=tk.RIGHT, padx=10, pady=10, fill=tk.Y)  
  
        self.canvas = tk.Canvas(left, width=9*self.CELL, height=10*self.CELL, bg='#f5deb3')  
        self.canvas.pack()  
        self.canvas.bind("<Button-1>", self.on_click)  
        self.draw_board()  
  
        ctl = tk.Frame(right); ctl.pack()  
        ttk.Label(ctl, text="思考时间(s)：").grid(row=0,column=0)  
        ttk.Entry(ctl, textvariable=self.engine_time, width=6).grid(row=0,column=1)  
        ttk.Label(ctl, text="最大深度：").grid(row=1,column=0)  
        ttk.Entry(ctl, textvariable=self.engine_depth, width=6).grid(row=1,column=1)  
  
        ttk.Button(ctl, text="电脑走子", command=self.engine_move_now).grid(row=2,column=0, columnspan=2, pady=4)  
        ttk.Button(ctl, text="中断思考", command=self.interrupt_engine).grid(row=3,column=0, columnspan=2, pady=4)  
        ttk.Button(ctl, text="悔棋", command=self.undo).grid(row=4,column=0, columnspan=2, pady=4)  
        ttk.Button(ctl, text="新局", command=self.new_game).grid(row=5,column=0, columnspan=2, pady=4)  
  
        self.status_var = tk.StringVar(value="红方先行（你执红）")  
        ttk.Label(ctl, textvariable=self.status_var).grid(row=6, column=0, columnspan=2, pady=6)  
  
        ttk.Label(ctl, text="引擎信息：").grid(row=7,column=0, columnspan=2, pady=(6,0))  
        self.info_text = tk.Text(ctl, width=36, height=10, state=tk.DISABLED)  
        self.info_text.grid(row=8,column=0, columnspan=2)  
  
        hist_frame = tk.LabelFrame(right, text="走子记录", padx=5, pady=5)  
        hist_frame.pack(fill=tk.BOTH, expand=True, pady=6)  
        self.hist_list = tk.Listbox(hist_frame, width=36, height=20)  
        self.hist_list.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)  
        scroll = ttk.Scrollbar(hist_frame, orient=tk.VERTICAL, command=self.hist_list.yview)  
        scroll.pack(side=tk.RIGHT, fill=tk.Y)  
        self.hist_list.config(yscrollcommand=scroll.set)  
  
        self.update_ui()  

    def on_click(self, event):
        if self.engine_thinking:
            return
        # 获取点击的格子
        cell = self.CELL
        c = int(round((event.x - cell/2) / cell))
        r = int(round((event.y - cell/2) / cell))
        if not (0 <= r < 10 and 0 <= c < 9):
            return
        sq = rc_to_sq(r, c)
        piece = self.board.squares[sq]
        print(f"点击位置: r={r}, c={c}, sq={sq}, piece={piece}, selected={self.selected}")
        if self.selected is None:
            if piece != 0 and (piece > 0) == self.board.red_to_move:
                self.selected = sq
                self.update_ui()
        else:
            mv = (self.selected, sq)
            legal = self.board.generate_moves()
            print(f"尝试走子: {mv}, 合法着法: {legal}")
            if mv in legal:
                frm, to = mv
                moving_piece = self.board.squares[frm]
                def after_anim():
                    self.board.make_move(mv)
                    self.hist_list.insert(tk.END, self.move_to_uci(mv, human=True))
                    self.selected = None
                    self.update_ui()
                    self.master.after(10, self.engine_move_now)
                self.animate_move(frm, to, moving_piece, callback=after_anim)
            else:
                if piece != 0 and (piece > 0) == self.board.red_to_move:
                    self.selected = sq
                else:
                    self.selected = None
                self.update_ui()

    def draw_board(self):
        self.canvas.delete("all")
        cell = self.CELL
        # 宫区底色
        palace_color = "#f0e68c"
        self.canvas.create_rectangle(3*cell+cell/2, 0*cell+cell/2, 5*cell+cell/2, 2*cell+cell/2, fill=palace_color, outline="")
        self.canvas.create_rectangle(3*cell+cell/2, 7*cell+cell/2, 5*cell+cell/2, 9*cell+cell/2, fill=palace_color, outline="")
        # 棋盘线条
        for i in range(10):
            y = i*cell + cell/2
            x1 = cell/2; x2 = 8*cell + cell/2
            self.canvas.create_line(x1, y, x2, y, width=3, fill="#8b4513")
        for j in range(9):
            x = j*cell + cell/2
            y1 = cell/2; y2 = 9*cell + cell/2
            self.canvas.create_line(x, y1, x, y2, width=3, fill="#8b4513")
        # 河界
        self.canvas.create_text(4*cell+cell/2, 4.5*cell+cell/2, text="楚河", font=("KaiTi", 24, "bold"), fill="#4682b4")
        self.canvas.create_text(4*cell+cell/2, 5.5*cell+cell/2, text="汉界", font=("KaiTi", 24, "bold"), fill="#b22222")
        # 宫区斜线
        self.canvas.create_line(3*cell+cell/2, 0*cell+cell/2, 5*cell+cell/2, 2*cell+cell/2, width=2)
        self.canvas.create_line(3*cell+cell/2, 2*cell+cell/2, 5*cell+cell/2, 0*cell+cell/2, width=2)
        self.canvas.create_line(3*cell+cell/2, 7*cell+cell/2, 5*cell+cell/2, 9*cell+cell/2, width=2)
        self.canvas.create_line(3*cell+cell/2, 9*cell+cell/2, 5*cell+cell/2, 7*cell+cell/2, width=2)
        # 棋子圆圈
        for r in range(10):
            for c in range(9):
                x = c*cell + cell/2; y = r*cell + cell/2
                self.canvas.create_oval(x-26,y-26,x+26,y+26, fill="#fffaf0", outline="#8b4513", width=2)

    def uidraw_pieces(self, highlight=None):
        self.canvas.delete("piece")
        cell = self.CELL
        for r in range(10):
            for c in range(9):
                sq = rc_to_sq(r,c)
                p = self.board.squares[sq]
                if p != 0:
                    txt = CODE_TO_TEXT.get(p, '')
                    x = c*cell + cell/2; y = r*cell + cell/2
                    color = "red" if p>0 else "black"
                    self.canvas.create_text(x, y, text=txt, font=("KaiTi", 24, "bold"), fill=color, tags="piece")
        self.canvas.delete("sel")
        if self.selected is not None:
            r,c = sq_to_rc(self.selected)
            x = c*cell + cell/2; y = r*cell + cell/2
            self.canvas.create_oval(x-28,y-28,x+28,y+28, outline="blue", width=3, tags="sel")
        # 高亮走棋前后位置
        if highlight:
            frm, to = highlight
            fr_r, fr_c = sq_to_rc(frm)
            to_r, to_c = sq_to_rc(to)
            x0 = fr_c*cell + cell/2; y0 = fr_r*cell + cell/2
            x1 = to_c*cell + cell/2; y1 = to_r*cell + cell/2
            self.canvas.create_oval(x0-32, y0-32, x0+32, y0+32, outline="#00FF00", width=4, tags="hl")
            self.canvas.create_oval(x1-32, y1-32, x1+32, y1+32, outline="#FFD700", width=4, tags="hl")

    def animate_move(self, frm, to, piece, callback=None):
        # 动画移动棋子，起点绿色高亮，终点金色高亮
        fr_r, fr_c = sq_to_rc(frm)
        to_r, to_c = sq_to_rc(to)
        cell = self.CELL
        x0 = fr_c*cell + cell/2
        y0 = fr_r*cell + cell/2
        x1 = to_c*cell + cell/2
        y1 = to_r*cell + cell/2
        txt = CODE_TO_TEXT.get(piece, '')
        color = "red" if piece > 0 else "black"
        # 高亮起点和终点
        self.uidraw_pieces(highlight=(frm, to))
        # 创建动画棋子
        anim_id = self.canvas.create_text(x0, y0, text=txt, font=("KaiTi", 24, "bold"), fill=color, tags="anim")
        def step(i):
            if i > self.ANIMATION_STEPS:
                self.canvas.delete(anim_id)
                self.uidraw_pieces()
                if callback: callback()
                return
            x = x0 + (x1 - x0) * i / self.ANIMATION_STEPS
            y = y0 + (y1 - y0) * i / self.ANIMATION_STEPS
            self.canvas.coords(anim_id, x, y)
            self.master.after(self.ANIMATION_DELAY, lambda: step(i+1))
        step(0)

    def update_ui(self):
        self.draw_board()
        self.uidraw_pieces()
        side = "红" if self.board.red_to_move else "黑"
        self.status_var.set(f"{side}方行棋    节点={self.board.nodes}")
        self.master.update_idletasks()

    def move_to_uci(self, mv, human=False):  
        fr,to = mv  
        fr_r,fr_c = sq_to_rc(fr); to_r,to_c = sq_to_rc(to)  
        s = f"{chr(fr_c+ord('a'))}{fr_r}{chr(to_c+ord('a'))}{to_r}"  
        return f"{s}  ({'红' if human else ('红' if not self.board.red_to_move else '黑')})"  
  
    def new_game(self):  
        if self.engine_thinking:  
            messagebox.showinfo("请等待", "引擎仍在思考")  
            return  
        self.board = Board()  
        self.selected = None  
        self.hist_list.delete(0, tk.END)  
        self.info_text.configure(state=tk.NORMAL); self.info_text.delete('1.0', tk.END); self.info_text.configure(state=tk.DISABLED)  
        self.update_ui()  
  
    def undo(self):  
        if self.engine_thinking:  
            messagebox.showinfo("请等待", "引擎仍在思考")  
            return  
        if not self.board.history: return  
        # undo last move  
        self.board.undo_move()  
        # try undo one more (so human gets move back)  
        if self.board.history:  
            self.board.undo_move()  
            if self.hist_list.size() > 0:  
                self.hist_list.delete(tk.END)  
                if self.hist_list.size() > 0:  
                    self.hist_list.delete(tk.END)  
        self.update_ui()  
  
    def engine_move_now(self):  
        if self.engine_thinking: return  
        if self.board.is_terminal():  
            messagebox.showinfo("结束", "局面已结束")  
            return  
        # start engine thread  
        self.engine_stop.clear()  
        self.engine_thread = threading.Thread(target=self._engine_worker, daemon=True)  
        self.engine_thread.start()  
  
    def interrupt_engine(self):  
        if self.engine_thinking:  
            self.engine_stop.set()  
  
    def _engine_worker(self):  
        self.engine_thinking = True  
        self.update_ui()  
        time_limit = float(self.engine_time.get())  
        max_depth = int(self.engine_depth.get())  
        start = time.time()  
        # info callback to update UI progressively  
        def info_callback(depth, score, pv, nodes, time_spent):  
            s = f"深度 {depth}  估分 {score:.1f}  节点 {nodes}  时间 {time_spent:.2f}s\nPV: " + " ".join([self.mv_to_str(m) for m in pv]) + "\n\n"  
            self.info_text.configure(state=tk.NORMAL)  
            self.info_text.delete('1.0', tk.END)  
            self.info_text.insert(tk.END, s)  
            self.info_text.configure(state=tk.DISABLED)  
            self.show_pv.set(s)  
        try:  
            best = search_best_move(self.board, max_depth=max_depth, time_limit=time_limit, stop_flag=self.engine_stop, info_callback=info_callback)  
        except Exception as e:  
            best = None  
        # apply result in main thread  
        def apply():  
            nonlocal best  
            if best:  
                frm, to = best
                moving_piece = self.board.squares[frm]
                def after_anim():
                    self.board.make_move(best)
                    self.hist_list.insert(tk.END, self.move_to_uci(best, human=False))
                    self.engine_thinking = False
                    self.update_ui()
                self.animate_move(frm, to, moving_piece, callback=after_anim)
            else:  
                messagebox.showinfo("信息", "引擎未找到着法或被中断")  
                self.engine_thinking = False
                self.update_ui()
        self.master.after(10, apply)  
  
    def mv_to_str(self, mv):  
        if not mv: return ""  
        fr,to = mv  
        fr_r,fr_c = sq_to_rc(fr); to_r,to_c = sq_to_rc(to)  
        return f"{chr(fr_c+ord('a'))}{fr_r}{chr(to_c+ord('a'))}{to_r}"  
  
# -------------------------  
# 运行  
# -------------------------  
def main():  
    root = tk.Tk()  
    gui = XiangqiGUI(root)  
    root.mainloop()  
  
if __name__ == "__main__":  
    main()

# --- 评估函数（替换为更强版本） ---
def evaluate(board):
    score = 0
    for piece, pos in board.get_pieces():
        score += piece_values.get(piece, 0)
        # 兵过河加分
        if piece == "P" and pos[1] < 5:
            score += 30
        if piece == "p" and pos[1] > 4:
            score -= 30
    return score

# --- αβ剪枝（替换/增强） ---
def alpha_beta(board, depth, alpha, beta, maximizing_player, start_time, time_limit=3):
    if time.time() - start_time > time_limit:
        return evaluate(board), None
    if depth == 0 or board.is_game_over():
        return evaluate(board), None

    board_key = board.get_hash()
    if (board_key, depth) in transposition_table:
        return transposition_table[(board_key, depth)]

    best_move = None
    if maximizing_player:
        max_eval = float("-inf")
        for move in board.generate_legal_moves():
            board.push(move)
            eval, _ = alpha_beta(board, depth - 1, alpha, beta, False, start_time, time_limit)
            board.pop()
            if eval > max_eval:
                max_eval = eval
                best_move = move
            alpha = max(alpha, eval)
            if beta <= alpha:
                break
        transposition_table[(board_key, depth)] = (max_eval, best_move)
        return max_eval, best_move
    else:
        min_eval = float("inf")
        for move in board.generate_legal_moves():
            board.push(move)
            eval, _ = alpha_beta(board, depth - 1, alpha, beta, True, start_time, time_limit)
            board.pop()
            if eval < min_eval:
                min_eval = eval
                best_move = move
            beta = min(beta, eval)
            if beta <= alpha:
                break
        transposition_table[(board_key, depth)] = (min_eval, best_move)
        return min_eval, best_move

# --- 迭代加深 ---
def iterative_deepening(board, max_depth=4, time_limit=3):
    start_time = time.time()
    best_move = None
    best_eval = 0
    for depth in range(1, max_depth + 1):
        if time.time() - start_time > time_limit:
            break
        eval, move = alpha_beta(board, depth, float('-inf'), float('inf'),
                                board.turn == "r", start_time, time_limit)
        if move:
            best_eval, best_move = eval, move
    return best_eval, best_move

# --- AI 执行（在 Tkinter 引擎调用处使用） ---
def ai_move(board):
    eval, move = iterative_deepening(board, max_depth=4, time_limit=3)
    if move:
        board.push(move)

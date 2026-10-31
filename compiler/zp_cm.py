"""Z_P as a counter-machine program (mirrors ref/zp_ref.py exactly).

Variants used by the test-suite:
  truth='L'         the real NP-complete language (default)
  truth='nonempty'  P-language swap: s in L'  iff  s != eps
  truth='odd'       P-language swap: s in L'  iff  s ends in '1'
  candidates=[...]  controlled candidate enumeration (list of J values);
                    after the list is exhausted the machine idles silently.

Register usage (all registers are 0 at the labels 'inst' and 'cand' except
J, S): see docs/spec.md §5.
"""
from cm import CM


def build(truth='L', candidates=None):
    b = CM()

    # ---------------------------------------------------------- outer loop
    if candidates is None:
        b.inc('J')                          # J = 1
    else:
        _load_candidate(b, candidates)
    b.label('cand')
    b.inc('S')                              # S = 1
    b.label('inst')

    # N = |s|   (and K = S, the certificate countdown)
    b.move('S', ['U_lenS', 'K', 'T_inst'])
    b.move('T_inst', ['S'])
    if truth != 'L':
        b.clear('K')
    L, D = b.fresh('lenS'), b.fresh('lenSd')
    b.label(L)
    b.pop('U_lenS', D)
    b.inc('N')
    b.jmp(L)
    b.label(D)

    # ------------------------------------------------- truth -> TR in {0,1}
    if truth == 'L':
        b.label('cert')
        b.dec('K', z='certdone')
        b.inc('C')
        b.clear('P')
        b.clear('Tb')
        b.copy('S', 'P')
        b.copy('C', 'X')
        b.copy('N', 'Tb')
        b.inc('F')                          # F = 1: verifier call site
        b.jmp('run')
        b.label('ver_acc')
        b.inc('TR')
        b.clear('K')
        b.label('certdone')
        b.clear('C')
    elif truth == 'nonempty':
        b.copy('S', 'U_ne')
        b.dec('U_ne')
        b.dec('U_ne', z='tr_done')
        b.inc('TR')
        b.clear('U_ne')
        b.label('tr_done')
    elif truth == 'odd':                    # S odd and S > 1
        b.copy('S', 'U_odd')
        b.pop('U_odd', 'tr_done', B='TR')
        b.clear('U_odd')
        b.label('tr_done')
    else:
        raise ValueError(truth)

    # ----------------------------------------------- decider: run(J, S, T)
    b.copy('J', 'U_lenJ')                        # E = |code(J)|
    L, D = b.fresh('lenJ'), b.fresh('lenJd')
    b.label(L)
    b.pop('U_lenJ', D)
    b.inc('E')
    b.jmp(L)
    b.label(D)
    b.clear('P')
    b.clear('Tb')
    b.copy('N', 'Bs')                       # Bs = N + 2 ; Tb = Bs ** E
    b.inc('Bs')
    b.inc('Bs')
    b.inc('Tb')
    b.label('pow')
    b.dec('E', z='powd')
    b.move('Tb', ['V_mul'])
    b.label('mul')
    b.dec('V_mul', z='pow')
    b.copy('Bs', 'Tb')
    b.jmp('mul')
    b.label('powd')
    b.clear('Bs')
    b.copy('J', 'P')
    b.copy('S', 'X')
    b.jmp('run')                            # F = 0: decider call site

    b.label('dec_acc')
    b.dec('TR', z='bad')
    b.jmp('ok')
    b.label('dec_rej')
    b.dec('TR', z='ok')
    b.jmp('bad')
    b.label('dec_timeout')
    b.clear('TR')
    b.label('bad')
    b.beep()
    if candidates is None:
        b.inc('J')
    else:
        b.clear('J')
        b.inc('CI')
        b.jmp('load')
    b.clear('S')
    b.clear('N')
    b.jmp('cand')
    b.label('ok')
    b.clear('N')
    b.inc('S')
    b.jmp('inst')

    # ------------------------------------------------- run(P, X, Tb) ; F
    # Guest tape: R = head cell + right part, Lt = left part (LSB nearest).
    # O = current offset (state).  P, Tb, X are inputs; X is consumed.
    b.label('run')
    for r in ('R', 'R1', 'Lt', 'O', 'A'):
        b.clear(r)
    b.label('enc')                          # R := enc(X)
    b.pop('X', 'step', B='w')
    b.move('R', ['U_enc', 'U_enc'])
    b.move('w', ['U_enc'])
    b.move('U_enc', ['R', 'R'])
    b.inc('R')
    b.jmp('enc')

    b.label('step')
    b.dec('Tb', z='o_timeout')
    L, A0 = b.fresh('hR'), b.fresh('a0')    # R1 = R // 2 ; O += R mod 2
    b.label(L)
    b.dec('R', z=A0)
    b.dec('R', z='a1')
    b.inc('R1')
    b.jmp(L)
    b.label('a1')
    b.inc('O')
    b.label(A0)
    b.copy('P', 'Pc')
    # scan entries: skip O entries, accumulate the next one in A
    b.label('parse')
    b.pop('Pc', 'o_rej', B='w')
    b.dec('w', z='bit0')
    b.dec('O', z='bit1t')
    b.inc('O')
    b.jmp('parse')
    b.label('bit1t')
    b.inc('A')
    b.jmp('parse')
    b.label('bit0')
    b.dec('O', z='decode')
    b.jmp('parse')

    b.label('decode')                       # A = 4k + 2d + w
    b.clear('Pc')
    L, D0 = b.fresh('hA'), b.fresh('w0')
    b.label(L)
    b.dec('A', z=D0)
    b.dec('A', z='w1')
    b.inc('A2')
    b.jmp(L)
    b.label('w1')
    b.inc('w')
    b.label(D0)
    L = b.fresh('hA2')
    b.label(L)
    b.dec('A2', z='left')
    b.dec('A2', z='right')
    b.inc('A')
    b.jmp(L)

    b.label('right')                        # Lt = 2 Lt + w ; R = R1
    b.dec('A', z='halt')
    b.move('A', ['O'])
    b.move('Lt', ['U_right', 'U_right'])
    b.move('w', ['U_right'])
    b.move('U_right', ['Lt'])
    b.move('R1', ['R'])
    b.jmp('step')

    b.label('left')                         # R = 2(2 R1 + w) + Lt mod 2
    b.dec('A', z='halt')
    b.move('A', ['O'])
    L, E0 = b.fresh('hL'), b.fresh('l0')
    b.label(L)
    b.dec('Lt', z=E0)
    b.dec('Lt', z='l1')
    b.inc('V_left')
    b.jmp(L)
    b.label('l1')
    b.inc('R')
    b.label(E0)
    b.move('V_left', ['Lt'])
    b.move('R1', ['U_left', 'U_left'])
    b.move('w', ['U_left'])
    b.move('U_left', ['R', 'R'])
    b.jmp('step')

    # ----------------------------------------------------------- outcomes
    b.label('halt')                         # output w
    b.dec('w', z='o_rej')
    b.label('o_acc')
    b.dec('F', z='dec_acc')
    b.jmp('ver_acc' if truth == 'L' else 'never')
    b.label('o_rej')
    b.dec('F', z='dec_rej')
    b.jmp('cert' if truth == 'L' else 'never')
    b.label('o_timeout')
    b.dec('F', z='dec_timeout')
    b.jmp('cert' if truth == 'L' else 'never')

    if truth != 'L':
        b.label('never')                    # unreachable (F is always 0)
        b.jmp('never_')
        b.label('never_')
        b.dec('F', nz='never_', z='never_')
    if candidates is not None:
        _candidate_table(b, candidates)
    return b


def _cleanup(b):
    for r in ('w', 'd', 'A', 'Pc', 'cnt', 'R1', 'R', 'Lt', 'q', 'Tb', 'P'):
        b.clear(r)


def _load_candidate(b, candidates):
    b.jmp('load')


def _candidate_table(b, cands):
    """J := cands[CI] (CI preserved); idle silently past the end."""
    b.label('load')
    b.copy('CI', 'V_ld')
    for i, J in enumerate(cands):
        nxt = b.fresh('ld')
        b.dec('V_ld', z=nxt)
        b.jmp(nxt + 'skip')
        b.label(nxt)
        for bit in bin(J)[2:]:              # J = 2 J + bit, MSB first
            b.move('J', ['V_ld', 'V_ld'])
            b.move('V_ld', ['J'])
            if bit == '1':
                b.inc('J')
        b.clear('S')
        b.clear('N')
        b.jmp('cand')
        b.label(nxt + 'skip')
    b.clear('V_ld')
    b.label('idle')
    b.dec('V_ld', nz='idle', z='idle')

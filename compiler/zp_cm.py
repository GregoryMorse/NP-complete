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

    # N = |s|
    b.copy('S', 'U')
    L, D = b.fresh('lenS'), b.fresh('lenSd')
    b.label(L)
    b.pop('U', D)
    b.inc('N')
    b.jmp(L)
    b.label(D)

    # ------------------------------------------------- truth -> TR in {0,1}
    if truth == 'L':
        b.copy('S', 'K')                    # countdown over C = 1..S
        b.label('cert')
        b.dec('K', z='certdone')
        b.inc('C')
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
        b.copy('S', 'U')
        b.dec('U')
        b.dec('U', z='tr_done')
        b.inc('TR')
        b.clear('U')
        b.label('tr_done')
    elif truth == 'odd':                    # S odd and S > 1
        b.copy('S', 'U')
        b.pop('U', 'tr_done', B='TR')
        b.clear('U')
        b.label('tr_done')
    else:
        raise ValueError(truth)

    # ----------------------------------------------- decider: run(J, S, T)
    # E = |code(J)|
    b.copy('J', 'U')
    L, D = b.fresh('lenJ'), b.fresh('lenJd')
    b.label(L)
    b.pop('U', D)
    b.inc('E')
    b.jmp(L)
    b.label(D)
    # Bs = N + 2 ; Tb = Bs ** E
    b.copy('N', 'Bs')
    b.inc('Bs')
    b.inc('Bs')
    b.inc('Tb')
    b.label('pow')
    b.dec('E', z='powd')
    b.move('Tb', ['V'])
    b.label('mul')
    b.dec('V', z='pow')
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
    # workspace R R1 Lt q cnt Pc w d k B is zero on entry, U V T zero.
    b.label('run')
    # R := enc(X)
    b.label('enc')
    b.pop('X', 'step', B='B')
    b.move('R', ['U', 'U'])
    b.move('B', ['U'])
    b.move('U', ['R', 'R'])
    b.inc('R')
    b.jmp('enc')

    b.label('step')
    b.dec('Tb', z='o_timeout')
    # a = R mod 2 ; R1 = R // 2 ; cnt = 2q + a
    L, A0, A1 = b.fresh('hR'), b.fresh('a0'), b.fresh('a1')
    b.label(L)
    b.dec('R', z=A0)
    b.dec('R', z=A1)
    b.inc('R1')
    b.jmp(L)
    b.label(A1)
    b.inc('cnt')
    b.label(A0)
    b.move('q', ['cnt', 'cnt', 'T'])
    b.move('T', ['q'])
    b.copy('P', 'Pc')
    # parse entries 0..cnt
    b.label('parse')
    b.pop('Pc', 'o_fail', B='w')
    b.pop('Pc', 'o_fail', B='d')
    b.label('un')
    b.pop('Pc', 'o_fail', B='B')
    b.dec('B', z='und')
    b.inc('k')
    b.jmp('un')
    b.label('und')
    b.dec('cnt', z='use')
    b.clear('w')
    b.clear('d')
    b.clear('k')
    b.jmp('parse')

    b.label('use')
    b.clear('Pc')
    b.dec('k', z='halt')
    b.clear('q')
    b.move('k', ['q'])
    b.dec('d', z='left')
    # move right: Lt = 2 Lt + w ; R = R1
    b.move('Lt', ['U', 'U'])
    b.move('w', ['U'])
    b.move('U', ['Lt'])
    b.move('R1', ['R'])
    b.jmp('step')
    b.label('left')
    # R = 2 (2 R1 + w) + (Lt mod 2) ; Lt = Lt // 2
    L, E0, E1 = b.fresh('hL'), b.fresh('l0'), b.fresh('l1')
    b.label(L)
    b.dec('Lt', z=E0)
    b.dec('Lt', z=E1)
    b.inc('V')
    b.jmp(L)
    b.label(E1)
    b.inc('R')
    b.label(E0)
    b.move('V', ['Lt'])
    b.move('R1', ['U', 'U'])
    b.move('w', ['U'])
    b.move('U', ['R', 'R'])
    b.jmp('step')

    # ----------------------------------------------------------- outcomes
    b.label('halt')                         # k was 0; output w
    b.dec('w', z='o_rej')
    b.label('o_acc')
    _cleanup(b)
    b.dec('F', z='dec_acc')
    b.jmp('ver_acc' if truth == 'L' else 'never')
    b.label('o_fail')
    b.label('o_rej')
    _cleanup(b)
    b.dec('F', z='dec_rej')
    b.jmp('cert' if truth == 'L' else 'never')
    b.label('o_timeout')
    _cleanup(b)
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
    for r in ('w', 'd', 'k', 'Pc', 'cnt', 'R1', 'R', 'Lt', 'q', 'Tb', 'P'):
        b.clear(r)


def _load_candidate(b, candidates):
    b.jmp('load')


def _candidate_table(b, cands):
    """J := cands[CI] (CI preserved); idle silently past the end."""
    b.label('load')
    b.copy('CI', 'V')
    for i, J in enumerate(cands):
        nxt = b.fresh('ld')
        b.dec('V', z=nxt)
        b.jmp(nxt + 'skip')
        b.label(nxt)
        for _ in range(J):
            b.inc('J')
        b.clear('S')
        b.clear('N')
        b.jmp('cand')
        b.label(nxt + 'skip')
    b.clear('V')
    b.label('idle')
    b.dec('V', nz='idle', z='idle')

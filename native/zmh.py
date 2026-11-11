"""Multihead read-only guest on the zp2 interpreter: the parts shared by the
L = P machine (zlp.py) and the L = NL machine (zlnl.py).  Reference model:
ref/zmh_ref.py.

During a multihead run the tape is

    Q gap c H M_g J M_1 s M_2 .. fuel B storage

The countdown cell c holds the symbol under the current head (blank at the
end markers).  The storage holds one unit per head,  M M 0 x_1 .. x_n 0
(x = s), with a marker cell after the scanned cell: B for the current head,
M for the others.  The first 0 is position 0, the last one position n+1.

Act (peek  w d 1, entered as G2wd right of M_g):  w = 1 moves the current
marker right or left (staying at the end cells), w = 0 moves the current mark
to the next or previous unit (staying at the last / first).  The new scanned
symbol is carried into c, then the entry is recorded (RTW).
"""
B, M = 'B', 'M'
BITS = '01'
NB = '01M'


def act(t):
    for w in BITS:
        for d in BITS:
            o = w + d
            t('G2' + o, NB, '.', 'R', 'G2' + o)
            t('G2' + o, B, '.', 'R', 'G3' + o)      # the separator
            t('G3' + o, NB, '.', 'R', 'G3' + o)
    # move right: swap the marker with the next cell unless that is the end
    t('G311', B, '.', 'R', 'MR2')
    t('MR2', 'MB', '.', 'L', 'RB1')                 # at position n+1: blank
    for b in BITS:
        t('MR2', b, B, 'L', 'MR3' + b)
        t('MR3' + b, B, b, 'R', 'RD')
    # move left: unless the cell before the scanned one is the unit's M
    t('G310', B, '.', 'L', 'ML1')
    t('ML1', BITS, '.', 'L', 'ML2')
    t('ML2', M, '.', 'R', 'ML3')                    # at position 0: stay
    t('ML3', BITS, '.', 'R', 'RD')
    t('ML2', BITS, '.', 'R', 'ML4')
    for b in BITS:
        t('ML4', b, B, 'R', 'ML5' + b)
        t('ML5' + b, B, b, 'L', 'RD')
    # next head
    t('G301', B, '.', 'R', 'NX1')
    t('NX1', BITS, '.', 'R', 'NX1')
    t('NX1', B, '.', 'L', 'NXB')                    # last head: stay
    t('NX1', M, '.', 'R', 'NX2')
    t('NX2', M, '.', 'R', 'NX3')
    t('NX3', BITS, '.', 'R', 'NX3')
    t('NX3', M, B, 'L', 'NX4')                      # its marker becomes current
    t('NX4', NB, '.', 'L', 'NX4')
    t('NX4', B, M, 'R', 'NX5')
    t('NX5', NB, '.', 'R', 'NX5')
    t('NX5', B, '.', 'R', 'RR')
    t('NXB', NB, '.', 'L', 'NXB')
    t('NXB', B, '.', 'R', 'RR')
    # previous head
    t('G300', B, '.', 'L', 'PV1')
    t('PV1', BITS, '.', 'L', 'PV1')
    t('PV1', M, '.', 'L', 'PV2')
    t('PV2', M, '.', 'L', 'PV3')
    t('PV3', BITS, '.', 'L', 'PV3')
    t('PV3', B, '.', 'R', 'NX5')                    # first head: stay
    t('PV3', M, B, 'R', 'PV4')
    t('PV4', NB, '.', 'R', 'PV4')
    t('PV4', B, M, 'L', 'NXB')
    # read the scanned symbol (head on the marker) and carry it into c
    t('RD', B, '.', 'R', 'RR')
    t('RR', 'MB', '.', 'L', 'RB1')                  # position n+1
    t('RR', BITS, '.', 'L', 'RR2')
    t('RB1', B, '.', 'L', 'KB')
    t('RR2', B, '.', 'L', 'RL1')
    t('RL1', BITS, '.', 'L', 'RL2')
    t('RL2', M, '.', 'L', 'KB')                     # position 0
    t('RL2', BITS, '.', 'R', 'RL4')
    for b in BITS:
        t('RL4', b, '.', 'L', 'K' + b)
    for a in BITS + B:
        k = 'K' + a if a != B else 'KB'
        t(k, NB, '.', 'L', k)
        t(k, B, '.', 'L', 'K2' + a)
        t('K2' + a, NB, '.', 'L', 'K2' + a)
        t('K2' + a, B, a, 'L', 'RTW')               # c, then record the entry


def halt(t):
    """Outcome into H, erase the storage, then zp2's erase of the left side."""
    for w in BITS:
        t('GHH' + w, M, w, 'R', 'ESP')
    t('ESP', NB, '.', 'R', 'ESP')
    t('ESP', B, '.', 'R', 'ES1')
    t('ES1', NB, B, 'R', 'ES1')
    t('ES1', B, '.', 'R', 'ES2')
    t('ES2', NB, B, 'R', 'ES1')
    t('ES2', B, '.', 'L', 'ESB')
    t('ESB', B, '.', 'L', 'ESB')
    t('ESB', BITS, '.', 'L', 'ESN')                 # last fuel cell
    t('ESN', NB, '.', 'L', 'ESN')
    t('ESN', B, '.', 'L', 'EL2')                    # c


def units(t, back):
    """Append a unit  M M 0 M s 0  at the far right (entered as U0 left of the
    fuel's end), then return to the far left and continue in state back."""
    t('DW3', M, '.', 'R', 'U0')                     # decider: walker at M_1
    for j in BITS:
        t('WB3' + j, M, j, 'R', 'U0')               # and per step back
    t('UDW', BITS, '.', 'R', 'UDW')
    t('UDW', M, '.', 'L', 'WB2')
    t('U0', NB, '.', 'R', 'U0')
    t('U0', B, '.', 'R', 'U1')
    t('U1', NB, '.', 'R', 'U1')
    t('U1', B, M, 'R', 'U2')
    t('U2', B, M, 'R', 'U3')
    t('U3', B, '0', 'R', 'U4')
    t('U4', B, M, 'L', 'U5')
    t('U5', NB, '.', 'L', 'U5')
    t('U5', B, '.', 'L', 'U6')
    t('U6', NB, '.', 'L', 'U6')
    t('U6', B, '.', 'R', 'UB2')
    t('UB2', BITS, '.', 'R', 'UB2')
    t('UB2', M, '.', 'R', 'UB3')
    t('UB3', BITS, '.', 'R', 'UB3')
    t('UB3', M, '.', 'R', 'UCP')
    for b in BITS:
        t('UCP', b, B, 'R', 'UC' + b)
        t('UC' + b, NB, '.', 'R', 'UC' + b)
        t('UC' + b, B, '.', 'R', 'UC2' + b)
        t('UC2' + b, NB, '.', 'R', 'UC2' + b)
        t('UC2' + b, B, b, 'L', 'UK' + b)
        t('UK' + b, NB, '.', 'L', 'UK' + b)
        t('UK' + b, B, '.', 'L', 'UK2' + b)
        t('UK2' + b, NB, '.', 'L', 'UK2' + b)
        t('UK2' + b, B, b, 'R', 'UCP')
    t('UCP', M, '.', 'R', 'UE1')
    t('UE1', NB, '.', 'R', 'UE1')
    t('UE1', B, '.', 'R', 'UE2')
    t('UE2', NB, '.', 'R', 'UE2')
    t('UE2', B, '0', 'L', 'UL1')
    t('UL1', NB, '.', 'L', 'UL1')
    t('UL1', B, '.', 'L', 'UL2')
    t('UL2', NB, '.', 'L', 'UL2')
    t('UL2', B, '.', 'R', back)


def setup(t):
    """Run setup from GCD at the start of the source field: make the first
    marker current, put c (placeholder M) and the gap separator left of H,
    then zp2's code copy (GRM, QN2, QC, QE, QE3)."""
    t('GCD', BITS, '.', 'R', 'GCD')
    t('GCD', M, B, 'R', 'S1')                       # mark the end of the source
    t('S1', NB, '.', 'R', 'S1')
    t('S1', B, '.', 'R', 'S2')
    t('S2', M, '.', 'R', 'S2')
    t('S2', '0', '.', 'R', 'S5')
    t('S5', M, B, 'L', 'S6')
    t('S6', NB, '.', 'L', 'S6')
    t('S6', B, '.', 'L', 'S7')
    t('S7', NB, '.', 'L', 'S7')
    t('S7', B, '.', 'L', 'GLMD')
    t('GLMD', NB, '.', 'L', 'GLMD')
    t('GLMD', B, M, 'L', 'GLM2')                    # c (blanked before the run)
    t('GLM2', B, M, 'R', 'GRM')                     # gap separator
    t('QE3', M, B, 'R', 'QE4')
    t('QE4', M, B, 'L', 'TW')

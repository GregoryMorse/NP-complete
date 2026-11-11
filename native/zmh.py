"""Multihead read-only guest on the zp2 interpreter: the parts shared by the
L = P machine (zlp.py) and the L = NL machine (zlnl.py).  Reference model:
ref/zmh_ref.py.

During a multihead run the tape is

    Q gap c H M_g J M_1 s M_2 F M_3 fuel B storage

The countdown cell c holds the symbol under the current head (blank at the
end markers).  The storage holds one unit per head,  M x_1 .. x_n 0  (x = s),
with a marker cell after the scanned cell: B for the current head, M for the
others.  The unit's M is position 0, its last cell 0 position n+1.  Head 0 is
the last (rightmost) unit, head i+1 the unit left of head i.

Act (peek  w d 1, entered as G2wd right of H):  w = 1 moves the current
marker right or left (staying at the end cells), w = 0 makes the unit to the
left (d = 1) or to the right (d = 0) current, staying at the first / last
unit.  The new scanned symbol is carried into c (WC0, WC1, RGQ1), then the
entry is recorded (RTW).
"""
B, M = 'B', 'M'
BITS = '01'
NB = '01M'


def act(t):
    for w in BITS:
        for d in BITS:
            o = w + d
            t('G2' + o, NB, '.', 'R', 'G2' + o)
            t('G2' + o, B, '.', 'R', 'G3' + o)      # the end of the fuel
            t('G3' + o, NB, '.', 'R', 'G3' + o)
    t('G311', B, '.', 'R', 'MR')
    t('G310', B, '.', 'L', 'ML')
    t('G301', B, M, 'L', 'LS1')                     # next head: the unit to the left
    t('G300', B, M, 'R', 'RS1')                     # previous head: the unit to the right
    # move right: swap the marker with the next cell unless that is the end
    t('MR', 'MB', '.', 'L', 'RB1')                  # at position n+1: blank
    for b in BITS:
        t('MR', b, B, 'L', 'MR' + b)
        t('MR' + b, B, b, 'R', 'RD')
    # move left: unless the scanned cell is the unit's M
    t('ML', M, '.', 'L', 'KB')                      # at position 0: blank
    for b in BITS:
        t('ML', b, B, 'R', 'ML' + b)
        t('ML' + b, B, b, 'L', 'RD')
    # head switch (the old marker is already M): find the neighbour's marker
    t('LS1', BITS, '.', 'L', 'LS1')
    t('LS1', M, '.', 'L', 'LS3')                    # the unit's M
    t('LS3', BITS, '.', 'L', 'LS3')
    t('LS3', M, B, 'R', 'RR')
    t('LS3', B, '.', 'R', 'RS1')                    # first unit: back to the old marker
    t('RS1', BITS, '.', 'R', 'RS1')
    t('RS1', M, '.', 'R', 'RS3')                    # the next unit's M
    t('RS1', B, '.', 'L', 'LS3')                    # last unit: back to the old marker
    t('RS3', BITS, '.', 'R', 'RS3')
    t('RS3', M, B, 'R', 'RR')
    # read the scanned symbol (RR right of the marker) and carry it into c
    t('RD', B, '.', 'R', 'RR')
    t('RR', 'MB', '.', 'L', 'RB1')                  # position n+1
    t('RR', BITS, '.', 'L', 'RR2')
    t('RB1', B, '.', 'L', 'KB')
    t('RR2', B, '.', 'L', 'RL')
    t('RL', M, '.', 'L', 'KB')                      # position 0
    for b in BITS:
        t('RL', b, '.', 'L', 'K' + b)
    for a in BITS + B:
        t('K' + a, NB, '.', 'L', 'K' + a)
        t('K' + a, B, '.', 'L', 'WC' + a if a != B else 'RGQ1')
    for b in BITS:
        t('WC' + b, NB, '.', 'L', 'WC' + b)
        t('WC' + b, B, b, 'L', 'RGQ1')              # c, then record the entry
    t('RGQ1', M, '.', 'L', 'RGQ1')                  # zp2's RGQ1 skips bits


def units(t, back):
    """Append a unit  M M x 0  at the far right (entered as U0 left of the
    fuel's end): the old current marker becomes M on the way, the new unit's
    marker becomes current at the end.  Then return to the far left and
    continue in state back."""
    t('U0', NB, '.', 'R', 'U0')
    t('U0', B, '.', 'R', 'U1')
    t('U1', NB, '.', 'R', 'U1')
    t('U1', B, M, 'R', 'U2')
    t('U2', NB, '.', 'R', 'U1')                     # that was the current marker
    t('U2', B, M, 'L', 'U5')                        # the new unit's M and marker
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
    t('UE2', B, '0', 'L', 'V')
    t('V', BITS, '.', 'L', 'V')
    t('V', M, B, 'L', 'UL1')                        # the new marker is current
    t('UL1', NB, '.', 'L', 'UL1')
    t('UL1', B, '.', 'L', 'UL2')
    t('UL2', NB, '.', 'L', 'UL2')
    t('UL2', B, '.', 'R', back)


def erase(t, at, nxt, name):
    """Extend the erase loop  at  (NB -> B, R; B -> L nxt) across the storage."""
    t(at, B, '.', 'R', name)
    t(name, NB, B, 'R', at)
    t(name, B, '.', 'L', nxt)

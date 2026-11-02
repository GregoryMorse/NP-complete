"""Native machine for linear-size NTT circuits (reference: ref/zntt_ref.py).

Tape:  B W M P M K M C M Nn MM rec_0 MM rec_1 .. MM rec_{N-1} B

* C = c and Nn = n in unary; K = 1111 (the loop over the four p-wide fields of
  a record); P = p ones, p the least prime = 1 (mod n); W = c n + 1 ones.
  P and W grow at the left edge.  During the evaluation P is the register S
  (value: number of marked cells, mod p).
* Record:  MM F G O P M acc M E M z M b M u , fields 1^k 0^(w-k) (value k-1;
  marking turns leading 1s into 0s and never the last 1).  F: column cursor,
  G: column entry done, O: output (last n records), P: input of this pass.
  u has width W and points to record k-3 (k <= 2: none): every pass starts with
  one decrement of all pointers and every column decrements the pointers of the
  later records, so u is *captured* (exactly two 1s left) in column u.
* p:  P := 1, then P += n until prime.  The test grows D = 2, 3, .. at the left
  edge; d | p is tested by marking D once per cell of P (D is reset when full
  and a reset writes a marker M at the left of D).  D full at the end and no
  marker: d = p, prime; with a marker: composite.
* Records: for each cell of C (a round; existing records get O := 0) and each
  cell of Nn one record: header 0 0 1 0, four copies of P, one of W.  A copy
  marks the ruler; the ruler being copied is the first marked field.
* Evaluation of one assignment of (z, b, u) (the odometer runs through all):
  for each pass t < n, the push evaluation of node_j = x_j + node_{j-1} +
  b_j node_{u_j} in column order; at an output, acc = E is checked and
  E := z acc, S += z acc; after passes t < n-1, S = 0 (power sums
  p_1 .. p_{n-1} vanish); at the end E = 1 for all outputs.
"""
import logic

B, M = 'B', 'M'
BITS = '01'
NB = '01M'


def build():
    m = logic.LTM('I0')
    t = m.t

    def skip(q, nxt, d='R', syms=BITS):        # cross a field, then step over its M
        t(q, syms, '.', d, q)
        t(q, M, '.', d, nxt)

    def scan(q, d, nxt, w='.', mv=None):        # run to the blank end, turn back
        t(q, NB, '.', d, q)
        t(q, B, w, mv or ('L' if d == 'R' else 'R'), nxt)
    # ---------------- init: K C Nn = 1111 M 1 M 1, P = 1 ----------------
    for i in range(4):
        t(f'I{i}', B, '1', 'R', f'I{i + 1}')
    t('I4', B, M, 'R', 'I5')
    t('I5', B, '1', 'R', 'I6')
    t('I6', B, M, 'R', 'I7')
    t('I7', B, '1', 'L', 'I8')
    scan('I8', 'L', 'I9', M, 'L')                    # I8 writes the P|K separator
    t('I9', B, '1', 'R', 'PA0')
    # ---------------- P += n ----------------
    scan('PA0', 'R', 'PA1')
    t('PA1', '0', '.', 'L', 'PA1')
    t('PA1', '1', '0', 'L', 'PA2')
    t('PA1', M, '.', 'R', 'PAU')
    scan('PA2', 'L', 'PA0', '1')
    t('PAU', '0', '1', 'R', 'PAU')
    t('PAU', B, '.', 'L', 'PT0')
    scan('PT0', 'L', 'PT1', M, 'L')
    t('PT1', B, '1', 'L', 'PT2')
    t('PT2', B, '1', 'R', 'TQ')                 # D = 11
    # ---------------- d | p ? ----------------
    skip('TQ', 'TP')
    t('TP', '0', '.', 'R', 'TP')
    t('TP', '1', '0', 'L', 'TD')
    t('TP', M, '.', 'L', 'TE')                  # P used up
    scan('TD', 'L', 'TD2')
    t('TD2', M, '.', 'R', 'TD3')
    t('TD2', '0', '.', 'R', 'TD3')
    t('TD2', '1', '0', 'R', 'TQ')
    t('TD3', '0', '.', 'R', 'TD3')
    t('TD3', '1', '0', 'R', 'TQ')
    t('TD3', M, '.', 'L', 'TR')                 # D full: reset
    t('TR', '0', '1', 'L', 'TR')
    t('TR', B, M, 'R', 'TR2')                   # reset marker
    t('TR', M, '.', 'R', 'TR2')
    t('TR2', '1', '0', 'R', 'TQ')
    scan('TE', 'L', 'TE2')
    t('TE2', M, '.', 'R', 'TEm')
    t('TE2', '0', '.', 'R', 'TEn')
    t('TE2', '1', '.', 'L', 'ND0')
    for q, done in (('TEn', 'PZ1'), ('TEm', 'CO1')):
        t(q, '0', '.', 'R', q)
        t(q, '1', '.', 'L', 'ND0')
        t(q, M, B, 'L', done)                   # erase the D|P separator
    # not divisible: restore D and P, d += 1 (the marker becomes the new cell)
    scan('ND0', 'L', 'ND1')
    t('ND1', M, '.', 'R', 'ND2')
    t('ND1', BITS, '1', 'R', 'ND2')
    t('ND2', BITS, '1', 'R', 'ND2')
    t('ND2', M, '.', 'R', 'ND3')
    t('ND3', '0', '1', 'R', 'ND3')
    t('ND3', M, '.', 'L', 'G1')
    scan('G1', 'L', 'G2')
    t('G2', M, '1', 'R', 'TQ')
    t('G2', '1', '.', 'L', 'G3')
    t('G3', B, '1', 'R', 'TQ')
    # divisible: erase D, restore P; composite: P += n, prime: build W
    for q, done in (('PZ1', 'WS0'), ('CO1', 'PA0')):
        t(q, NB, B, 'L', q)
        t(q, B, '.', 'R', q + 'b')
        t(q + 'b', B, '.', 'R', q + 'b')
        t(q + 'b', '0', '1', 'R', q + 'c')
        t(q + 'c', '0', '1', 'R', q + 'c')
        t(q + 'c', M, '.', 'L' if done == 'WS0' else 'R', done)
    # ---------------- W = c n + 1 at the left edge ----------------
    scan('WS0', 'L', 'WS1', M, 'L')
    t('WS1', B, '1', 'R', 'WSR')
    scan('WSR', 'R', 'WC0')
    scan('WB0', 'R', 'WB1')
    t('WB1', '0', '.', 'L', 'WB1')
    t('WB1', '1', '0', 'L', 'WB2')
    t('WB1', M, '.', 'R', 'WNU')
    scan('WB2', 'L', 'WB0', '1')
    t('WNU', '0', '1', 'R', 'WNU')
    t('WNU', B, '.', 'L', 'WC0')
    t('WC0', '1', '.', 'L', 'WC0')
    t('WC0', M, '.', 'L', 'WC1')
    t('WC1', '0', '.', 'L', 'WC1')
    t('WC1', '1', '0', 'R', 'WB0')
    t('WC1', M, '.', 'R', 'WCU')
    t('WCU', '0', '1', 'R', 'WCU')
    t('WCU', M, '.', 'L', 'RC1')
    # ---------------- records ----------------
    t('RC1', '0', '.', 'L', 'RC1')              # next cell of C: a round
    t('RC1', '1', '0', 'R', 'RO0')
    t('RC1', M, '.', 'R', 'RCU')
    t('RO0', BITS, '.', 'R', 'RO0')             # O := 0 in the records so far
    t('RO0', M, '.', 'R', 'RO1')
    t('RO0', B, '.', 'L', 'RNL')
    t('RO1', M, '.', 'R', 'RO2')
    t('RO1', BITS, '.', 'R', 'RO0')
    t('RO2', BITS, '.', 'R', 'RO3')
    t('RO3', BITS, '.', 'R', 'RO4')
    t('RO4', BITS, '0', 'R', 'RO0')
    scan('RNL', 'L', 'RN0')
    t('RN0', BITS, '.', 'R', 'RN0')             # to the end of Nn
    t('RN0', M, '.', 'R', 'RN1')
    t('RN0', B, '.', 'L', 'RN2')
    t('RN1', BITS, '.', 'R', 'RN0')
    t('RN1', M, '.', 'L', 'RN1b')
    t('RN1b', M, '.', 'L', 'RN2')
    t('RN2', '0', '.', 'L', 'RN2')
    t('RN2', '1', '0', 'R', 'RSR')
    t('RN2', M, '.', 'R', 'RNU')
    scan('RSR', 'R', 'RS1', M, 'R')
    t('RS1', B, M, 'R', 'RS2')
    for a, b_, w in (('RS2', 'RS3', '0'), ('RS3', 'RS4', '0'), ('RS4', 'RS5', '1')):
        t(a, B, w, 'R', b_)
    t('RS5', B, '0', 'L', 'KS')
    scan('KS', 'L', 'KS1')
    skip('KS1', 'KX1')
    skip('KX1', 'KX2')
    t('KX2', '0', '.', 'R', 'KX2')
    t('KX2', '1', '0', 'R', 'SPR')
    t('KX2', M, '.', 'L', 'KR')
    scan('SPR', 'R', 'SP1', M)
    scan('SP1', 'L', 'SP2')
    skip('SP2', 'SP3')
    t('SP3', '1', '0', 'R', 'SW3')
    scan('SW3', 'R', 'CL0', '1')
    scan('CL0', 'L', 'CL1')
    t('CL1', '1M', '.', 'R', 'CL1')
    t('CL1', '0', '.', 'R', 'CL2')
    t('CL2', '0', '.', 'R', 'CL2')
    t('CL2', '1', '0', 'R', 'CW0')
    t('CL2', M, '.', 'L', 'CRs')
    scan('CW0', 'R', 'CL0', '0')
    t('CRs', '0', '1', 'L', 'CRs')
    t('CRs', M, '.', 'R', 'KX1')                # P copied: next cell of K
    t('CRs', B, '.', 'R', 'RN0')                # W copied: record done
    t('KR', '0', '1', 'L', 'KR')
    t('KR', M, '.', 'R', 'SWR')
    scan('SWR', 'R', 'SW1', M)
    scan('SW1', 'L', 'SW2')
    t('SW2', '1', '0', 'R', 'SW3')
    t('RNU', '0', '1', 'R', 'RNU')
    for s in (M, B):
        t('RNU', s, '.', 'L', 'RC0')
    t('RC0', '1', '.', 'L', 'RC0')
    t('RC0', M, '.', 'L', 'RC1')
    t('RCU', '0', '1', 'R', 'RCU')
    t('RCU', M, '.', 'L', 'WI0')
    evaluation(m)
    return m


def evaluation(m):
    t = m.t

    def skip(q, nxt, d='R'):
        t(q, BITS, '.', d, q)
        t(q, M, '.', d, nxt)

    def left(q, nxt):                           # to the left blank, then step right
        t(q, NB, '.', 'L', q)
        t(q, B, '.', 'R', nxt)

    def mm(q, nxt, other=None):                 # q scans right for MM; nxt at the header
        t(q, BITS, '.', 'R', q)
        t(q, M, '.', 'R', q + 'm')
        t(q + 'm', M, '.', 'R', nxt)
        t(q + 'm', BITS, '.', 'R', q)
    FAIL = 'ODL'
    # ---------------- witness init: params restored, P := [rec 0], E := 1 ----------------
    left('WI0', 'WI1')
    t('WI1', '0', '1', 'R', 'WI1')
    t('WI1', '1', '.', 'R', 'WI1')
    t('WI1', M, '.', 'R', 'WI2')
    t('WI2', '0', '1', 'R', 'WI1')
    t('WI2', '1', '.', 'R', 'WI1')
    t('WI2', M, '.', 'R', 'WH1')
    for x in BITS:
        t('WH' + x, BITS, '.', 'R', 'WH' + x)
        t('WH' + x, M, '.', 'L', 'WP' + x)
        t('WP' + x, BITS, x, 'R', 'WE0')
    t('WE0', M, '.', 'R', 'WAc')
    skip('WAc', 'WE1')
    t('WE1', BITS, '1', 'R', 'WE2')
    t('WE2', BITS, '1', 'R', 'WE3')
    t('WE3', BITS, '0', 'R', 'WE3')
    t('WE3', M, '.', 'R', 'WS')
    t('WS', BITS, '.', 'R', 'WS')
    t('WS', M, '.', 'R', 'WS2')
    t('WS', B, '.', 'L', 'RZ0')
    t('WS2', M, '.', 'R', 'WH0')
    t('WS2', BITS, '.', 'R', 'WS')
    # ---------------- pass start: F G := 0, acc := 0, pointers restored ----------------
    left('RZ0', 'RZ1')
    mm('RZ1', 'RH0')
    t('RH0', BITS, '0', 'R', 'RH1')
    t('RH1', BITS, '0', 'R', 'RH2')
    skip('RH2', 'RA0')
    t('RA0', BITS, '1', 'R', 'RA1')
    t('RA1', BITS, '0', 'R', 'RA1')
    t('RA1', M, '.', 'R', 'RSE')
    skip('RSE', 'RSZ')
    skip('RSZ', 'RSB')
    skip('RSB', 'RU')
    t('RU', '0', '1', 'R', 'RU')
    t('RU', '1', '.', 'R', 'RU2')
    t('RU2', BITS, '.', 'R', 'RU2')
    t('RU2', M, '.', 'R', 'RN')
    t('RU2', B, '.', 'L', 'FAL')
    t('RN', M, '.', 'R', 'RH0')
    left('FAL', 'FAs')
    mm('FAs', 'FA0')
    # ---------------- F advance into a record: inject x, decrement later pointers ----------------
    t('FA0', BITS, '1', 'R', 'FA1')
    t('FA1', BITS, '.', 'R', 'FA1')
    t('FA1', M, '.', 'L', 'FA2')
    t('FA2', '1', '.', 'R', 'FAi')
    t('FA2', '0', '.', 'R', 'FAn')
    t('FAi', M, '.', 'R', 'FI0')
    t('FAn', M, '.', 'R', 'DAc')
    t('FI0', '1', '.', 'R', 'FI0')              # acc += 1 (mod p)
    t('FI0', '0', '1', 'R', 'DAc')
    t('FI0', M, '.', 'L', 'FIW')
    t('FIW', '1', '0', 'L', 'FIW')
    t('FIW', M, '.', 'R', 'FIW2')
    t('FIW2', '0', '1', 'R', 'DAc')
    skip('DAc', 'DE')
    skip('DE', 'DZ')
    skip('DZ', 'DB')
    skip('DB', 'DU0')
    t('DU0', '0', '.', 'R', 'DU0')
    t('DU0', '1', '.', 'R', 'DU1')
    t('DU1', '1', '.', 'L', 'DU2')
    t('DU1', '0', '.', 'R', 'DN0')
    t('DU1', M, '.', 'R', 'DN1')
    t('DU1', B, '.', 'L', 'RFL')
    t('DU2', '1', '0', 'R', 'DN0')
    t('DN0', BITS, '.', 'R', 'DN0')
    t('DN0', M, '.', 'R', 'DN1')
    t('DN0', B, '.', 'L', 'RFL')
    t('DN1', M, '.', 'R', 'DH')
    skip('DH', 'DAc')
    # ---------------- find the cursor, dispatch ----------------
    left('RFL', 'RF0')
    mm('RF0', 'RF2')
    t('RF2', '1', '.', 'R', 'RF3')
    t('RF2', '0', '.', 'R', 'RF0')
    t('RF3', '1', '.', 'R', 'RFo')              # output, entry done
    t('RF3', '0', '.', 'R', 'RF4')
    t('RF4', '1', '.', 'L', 'RF5')              # output entry: G := 1, compare
    t('RF4', '0', '.', 'R', 'RFn')
    t('RF5', '0', '1', 'R', 'RF6')
    t('RF6', '1', '.', 'R', 'RFc')
    skip('RFo', 'BU0o')
    skip('RFn', 'BU0n')
    skip('RFc', 'CP0')
    # ---------------- compare acc = E, destroying E ----------------
    t('CP0', '0', '.', 'R', 'CP0')
    t('CP0', '1', '.', 'R', 'CP1')
    t('CP1', '1', '.', 'L', 'CP2')
    t('CP1', '0', '.', 'R', 'CPE')
    t('CP1', M, '.', 'R', 'CPE2')
    t('CP2', '1', '0', 'R', 'CP3')
    skip('CP3', 'CP4')
    t('CP4', '1', '.', 'R', 'CP5')
    t('CP5', '1', '.', 'R', 'CP6')
    t('CP5', '0' + M, '.', 'L', FAIL)
    t('CP6', '1', '.', 'R', 'CP6')
    t('CP6', '0' + M, '.', 'L', 'CP7')
    t('CP7', '1', '0', 'L', 'CP8')
    t('CP8', '1', '.', 'L', 'CP8')
    t('CP8', M, '.', 'L', 'CP9')
    t('CP9', BITS, '.', 'L', 'CP9')
    t('CP9', M, '.', 'R', 'CP0')
    t('CPE', '0', '.', 'R', 'CPE')
    t('CPE', M, '.', 'R', 'CPE2')
    t('CPE2', '1', '.', 'R', 'CPE3')
    t('CPE3', '1', '.', 'L', FAIL)
    t('CPE3', '0' + M, '.', 'L', 'CPE4')
    t('CPE4', '1', '.', 'L', 'CPE4')
    t('CPE4', M, '.', 'L', 'CPE5')
    t('CPE5', BITS, '.', 'L', 'CPE5')
    t('CPE5', M, '.', 'R', 'CPE6')
    t('CPE6', '0', '1', 'R', 'CPE6')            # unmark acc
    t('CPE6', '1', '.', 'L', 'CPE7')
    t('CPE7', '1', '.', 'L', 'CPE7')
    t('CPE7', M, '.', 'R', 'BU0o')
    # ---------------- broadcast, one unit of acc at a time ----------------
    for o in 'on':
        t('BU0' + o, '0', '.', 'R', 'BU0' + o)
        t('BU0' + o, '1', '.', 'R', 'BU1' + o)
        t('BU1' + o, '0' + M, '.', 'L', 'CA0')  # no unit left: next column
    t('BU1n', '1', '.', 'L', 'BU2n')
    t('BU2n', '1', '0', 'R', 'BS0')
    t('BU1o', '1', '.', 'R', 'BZ0')             # output: E += z, S += z first
    skip('BZ0', 'BZ1')
    skip('BZ1', 'BZ2')
    t('BZ2', '0', '.', 'R', 'BZ2')
    t('BZ2', '1', '.', 'R', 'BZ3')
    t('BZ3', '1', '.', 'L', 'BZ4')
    t('BZ3', '0' + M, '.', 'L', 'BZR')
    t('BZ4', '1', '0', 'L', 'BZ5')
    t('BZ5', '0', '.', 'L', 'BZ5')
    t('BZ5', M, '.', 'L', 'IE0')
    t('IE0', '1', '0', 'L', 'IEW')              # E += 1 (mod p), from the right
    t('IE0', '0', '.', 'L', 'IE1')
    t('IE1', '0', '.', 'L', 'IE1')
    t('IE1', '1', '.', 'R', 'IE2')
    t('IE2', '0', '1', 'L', 'TS0')
    t('IEW', '1', '0', 'L', 'IEW')
    t('IEW', M, '.', 'R', 'IEW2')
    t('IEW2', '0', '1', 'L', 'TS0')
    left('TS0', 'TS1')
    skip('TS1', 'TS2')
    t('TS2', '0', '.', 'R', 'TS2')              # S += 1 (mod p)
    t('TS2', '1', '0', 'R', 'TS3')
    t('TS3', '1', '.', 'L', 'RFL')
    t('TS3', M, '.', 'L', 'TSW')
    t('TSW', '0', '1', 'L', 'TSW')
    t('TSW', M, '.', 'L', 'RFL')
    t('BZR', BITS, '.', 'L', 'BZR')             # z used up: restore it, mark the unit
    t('BZR', M, '.', 'R', 'BZR2')
    t('BZR2', '0', '1', 'R', 'BZR2')
    t('BZR2', '1', '.', 'L', 'BZR3')
    t('BZR3', '1', '.', 'L', 'BZR3')
    t('BZR3', M, '.', 'L', 'BZR4')
    t('BZR4', BITS, '.', 'L', 'BZR4')
    t('BZR4', M, '.', 'L', 'BZR5')
    t('BZR5', BITS, '.', 'L', 'BZR5')
    t('BZR5', M, '.', 'R', 'BZR6')
    t('BZR6', '0', '.', 'R', 'BZR6')
    t('BZR6', '1', '0', 'R', 'BS0')
    # sweep: the next record gets +1, every captured record + b
    t('BS0', BITS, '.', 'R', 'BS0')
    t('BS0', M, '.', 'R', 'BS1')
    t('BS0', B, '.', 'L', 'RFL')
    t('BS1', M, '.', 'R', 'BSh')
    t('BS1', BITS, '.', 'R', 'BS0')
    skip('BSh', 'IA0')
    t('IA0', '1', '.', 'R', 'IA0')
    t('IA0', '0', '1', 'R', 'LA')
    t('IA0', M, '.', 'L', 'IAW')
    t('IAW', '1', '0', 'L', 'IAW')
    t('IAW', M, '.', 'R', 'IAW2')
    t('IAW2', '0', '1', 'R', 'LA')
    skip('LA', 'LE')
    skip('LE', 'LZ')
    skip('LZ', 'LB')
    skip('LB', 'CU0')
    t('CU0', '0', '.', 'R', 'CU0')
    t('CU0', '1', '.', 'R', 'CU1')
    t('CU1', '1', '.', 'R', 'CU2')
    t('CU1', '0', '.', 'R', 'LN0')
    t('CU1', M, '.', 'R', 'LN1')
    t('CU1', B, '.', 'L', 'RFL')
    t('CU2', '1', '.', 'R', 'LN0')
    t('CU2', '0' + M + B, '.', 'L', 'AB0')     # captured
    t('LN0', BITS, '.', 'R', 'LN0')
    t('LN0', M, '.', 'R', 'LN1')
    t('LN0', B, '.', 'L', 'RFL')
    t('LN1', M, '.', 'R', 'LH')
    skip('LH', 'LA')
    t('AB0', BITS, '.', 'L', 'AB0')
    t('AB0', M, '.', 'L', 'AB1')
    t('AB1', BITS, '.', 'L', 'AB1')
    t('AB1', M, '.', 'R', 'AB2')
    t('AB2', '0', '.', 'R', 'AB2')
    t('AB2', '1', '.', 'R', 'AB3')
    t('AB3', '1', '.', 'L', 'AB4')
    t('AB3', '0' + M, '.', 'L', 'ABR')
    t('AB4', '1', '0', 'L', 'AB5')
    t('AB5', '0', '.', 'L', 'AB5')
    t('AB5', M, '.', 'L', 'AB6')
    skip('AB6', 'AB7', 'L')
    skip('AB7', 'IR0', 'L')
    t('IR0', '1', '0', 'L', 'IRW')              # acc += 1 (mod p), from the right
    t('IR0', '0', '.', 'L', 'IR1')
    t('IR1', '0', '.', 'L', 'IR1')
    t('IR1', '1', '.', 'R', 'IR2')
    t('IR2', '0', '1', 'R', 'AB8')
    t('IRW', '1', '0', 'L', 'IRW')
    t('IRW', M, '.', 'R', 'IRW2')
    t('IRW2', '0', '1', 'R', 'AB8')
    skip('AB8', 'AB9')
    skip('AB9', 'AB10')
    skip('AB10', 'AB2')
    t('ABR', BITS, '.', 'L', 'ABR')
    t('ABR', M, '.', 'R', 'ABR2')
    t('ABR2', '0', '1', 'R', 'ABR2')
    t('ABR2', '1', '.', 'R', 'ABR3')
    skip('ABR3', 'LN0')
    # ---------------- next column ----------------
    t('CA0', BITS, '.', 'L', 'CA0')
    t('CA0', M, '.', 'L', 'CA1')
    t('CA1', BITS, '.', 'L', 'CA1')
    t('CA1', M, '.', 'R', 'CA2')
    t('CA2', BITS, '0', 'R', 'CA3')
    t('CA3', BITS, '0', 'R', 'CA4')
    t('CA4', BITS, '.', 'R', 'CA4')
    t('CA4', M, '.', 'R', 'CA5')
    t('CA4', B, '.', 'L', 'PE0')
    t('CA5', M, '.', 'R', 'FA0')
    t('CA5', BITS, '.', 'R', 'CA4')
    # ---------------- pass end ----------------
    left('PE0', 'PE1')
    t('PE1', BITS, '.', 'R', 'PE1')
    t('PE1', M, '.', 'R', 'PE2')
    t('PE2', M, '.', 'L', 'PE3')
    t('PE2', BITS, '.', 'R', 'PE1')
    t('PE3', M, '.', 'L', 'PE4')
    t('PE4', '0', '.', 'L', 'PE4')
    t('PE4', '1', '0', 'L', 'PE5')
    t('PE5', '1', '.', 'L', 'SC')               # more passes: S must be 0
    t('PE5', M, '.', 'R', 'FC0')                # last pass: final check
    left('SC', 'SC1')
    skip('SC1', 'SC2')
    t('SC2', '1', '.', 'R', 'SC2')
    t('SC2', '0', '.', 'L', FAIL)
    t('SC2', M, '.', 'R', 'PM0')
    mm('PM0', 'PM2')                            # move P to the next record
    t('PM2', BITS, '.', 'R', 'PM2')
    t('PM2', M, '.', 'L', 'PM3')
    t('PM3', '1', '0', 'R', 'PM4')
    t('PM3', '0', '.', 'R', 'PM0')
    mm('PM4', 'PM6')
    t('PM6', BITS, '.', 'R', 'PM6')
    t('PM6', M, '.', 'L', 'PM7')
    t('PM7', BITS, '1', 'L', 'RZ0')
    mm('FC0', 'FC2')                            # outputs: E = 1
    t('FC0', B, '.', 'L', 'SU0')
    t('FC2', BITS, '.', 'R', 'FC3')
    t('FC3', BITS, '.', 'R', 'FC4')
    t('FC4', '1', '.', 'R', 'FC5')
    t('FC4', '0', '.', 'R', 'FC0')
    skip('FC5', 'FC7')
    skip('FC7', 'FC8')
    t('FC8', '1', '.', 'R', 'FC9')
    t('FC9', '1', '.', 'R', 'FC10')
    t('FC9', '0' + M, '.', 'L', FAIL)
    t('FC10', '0', '.', 'R', 'FC0')
    t('FC10', M, '.', 'R', 'FC0')
    t('FC10', '1', '.', 'L', FAIL)
    # ---------------- odometer over (z, b, u) ----------------
    left('ODL', 'OD0')
    mm('OD0', 'ODH')
    skip('ODH', 'ODa')
    skip('ODa', 'ODe')
    skip('ODe', 'ODI')
    t('ODI', '0', '.', 'R', 'ODI')
    t('ODI', '1', '.', 'R', 'ODJ')
    t('ODJ', '1', '.', 'R', 'ODJ')
    t('ODJ', '0', '1', 'L', 'WI0')
    t('ODJ', M + B, '.', 'L', 'ODR')
    t('ODR', BITS, '0', 'L', 'ODR')
    t('ODR', M, '.', 'R', 'ODW')
    t('ODW', '0', '1', 'R', 'ODN')
    t('ODN', '0', '.', 'R', 'ODN')
    t('ODN', M, '.', 'R', 'ODM')
    t('ODN', B, '.', 'L', 'BEEP')
    t('ODM', M, '.', 'R', 'ODH')
    t('ODM', '0', '.', 'R', 'ODI')
    t('ODM', '1', '.', 'R', 'ODJ')
    # ---------------- n += 1 ----------------
    left('SU0', 'SU1')
    t('SU1', BITS, '.', 'R', 'SU1')
    t('SU1', M, '.', 'R', 'SU2')
    t('SU2', BITS, '.', 'R', 'SU1')
    t('SU2', M, B, 'R', 'SU3')
    t('SU3', NB, B, 'R', 'SU3')                 # erase the records
    t('SU3', B, '.', 'L', 'SU4')
    t('SU4', B, '.', 'L', 'SU4')
    t('SU4', M, '1', 'L', 'SU5')                # Nn += 1
    skip('SU5', 'SU6', 'L')
    skip('SU6', 'SU7', 'L')                     # C
    skip('SU7', 'SU8', 'L')                     # K
    t('SU8', NB, B, 'L', 'SU8')                 # erase P and W
    t('SU8', B, '.', 'R', 'SU9')
    t('SU9', B, '.', 'R', 'SU9')
    t('SU9', M, '.', 'L', 'SU10')
    t('SU10', B, '1', 'R', 'PA0')               # P := 1
    # ---------------- beep: c += 1, n := 1 ----------------
    t('BEEP', NB + B, '.', 'L', 'BP0')
    m.beep = 'BEEP'
    left('BP0', 'BP1')
    t('BP1', BITS, '.', 'R', 'BP1')
    t('BP1', M, '.', 'R', 'BP2')
    t('BP2', BITS, '.', 'R', 'BP1')
    t('BP2', M, B, 'R', 'BP3')
    t('BP3', NB, B, 'R', 'BP3')
    t('BP3', B, '.', 'L', 'BP4')
    t('BP4', B, '.', 'L', 'BP4')
    t('BP4', M, B, 'L', 'BP5')
    t('BP5', '1', B, 'L', 'BP5')                # erase Nn
    t('BP5', M, '1', 'R', 'BP6')                # C += 1
    t('BP6', B, M, 'R', 'BP7')
    t('BP7', B, '1', 'L', 'BP8')                # Nn := 1
    t('BP8', M, '.', 'L', 'SU6')


if __name__ == '__main__':
    print(len(build().states()), 'logical states')

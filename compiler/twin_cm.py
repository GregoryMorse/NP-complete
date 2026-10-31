"""Twin-prime beeper (brief §11): beeps once for every twin-prime pair
(m-2, m).  It quasihalts iff there are only finitely many twin primes.

    M = 2, P1 = P2 = 0          P1 = [M-1 prime], P2 = [M-2 prime]
    loop:  F = [M prime]  (trial division by D = 2..M-1)
           if F and P2: BEEP
           P2, P1 = P1, F ;  M += 1
"""
from cm import CM


def build():
    b = CM()
    b.inc('M')
    b.inc('M')
    b.label('main')
    # ---- F = [M is prime] ; trials d = 2 .. M-1
    b.copy('M', 'Q')
    b.dec('Q')
    b.dec('Q')
    b.inc('D')                              # D = 1, incremented before use
    b.label('trial')
    b.dec('Q', z='isprime')
    b.inc('D')
    b.copy('M', 'X')
    b.label('modl')                         # X -= D repeatedly
    b.copy('D', 'Y')
    b.label('sub')
    b.dec('Y', z='subdone')
    b.dec('X', z='notdiv')
    b.jmp('sub')
    b.label('subdone')
    b.dec('X', z='div')
    b.inc('X')
    b.jmp('modl')
    b.label('notdiv')
    b.clear('Y')
    b.jmp('trial')
    b.label('div')                          # composite
    b.clear('Q')
    b.clear('D')
    b.jmp('noF')
    b.label('isprime')
    b.clear('D')
    # ---- F = 1 here
    b.dec('P2', z='nob')
    b.beep()
    b.label('nob')
    b.move('P1', ['P2'])
    b.inc('P1')
    b.jmp('next')
    b.label('noF')
    b.clear('P2')
    b.move('P1', ['P2'])
    b.label('next')
    b.inc('M')
    b.jmp('main')
    return b

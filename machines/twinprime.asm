; entry 0
   0                INC M        -> 1
   1                INC M        -> 2
   2 main:          DEC M        nz-> 3  z-> 5
   3                INC Q        -> 4
   4                INC D        -> 2
   5                DEC D        nz-> 6  z-> 7
   6                INC M        -> 5
   7                DEC Q        nz-> 8  z-> 8
   8                DEC Q        nz-> 9  z-> 9
   9                INC D        -> 10
  10 trial:         DEC Q        nz-> 11  z-> 29
  11                INC D        -> 12
  12                DEC M        nz-> 13  z-> 15
  13                INC X        -> 14
  14                INC Y        -> 12
  15                DEC Y        nz-> 16  z-> 17
  16                INC M        -> 15
  17 modl:          DEC D        nz-> 18  z-> 20
  18                INC Y        -> 19
  19                INC _t_D11   -> 17
  20                DEC _t_D11   nz-> 21  z-> 22
  21                INC D        -> 20
  22 sub:           DEC Y        nz-> 23  z-> 24
  23                DEC X        nz-> 22  z-> 26
  24 subdone:       DEC X        nz-> 25  z-> 27
  25                INC X        -> 17
  26 notdiv:        DEC Y        nz-> 26  z-> 10
  27 div:           DEC Q        nz-> 27  z-> 28
  28                DEC D        nz-> 28  z-> 35
  29 isprime:       DEC D        nz-> 29  z-> 30
  30                DEC P2       nz-> 31  z-> 32
  31                BEEP         -> 32
  32 nob:           DEC P1       nz-> 33  z-> 34
  33                INC P2       -> 32
  34                INC P1       -> 38
  35 noF:           DEC P2       nz-> 35  z-> 36
  36                DEC P1       nz-> 37  z-> 38
  37                INC P2       -> 36
  38 next:          INC M        -> 2

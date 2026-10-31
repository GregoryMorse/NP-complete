; entry 0
   0                INC J        -> 1
   1 cand:          INC S        -> 2
   2 inst:          DEC S        nz-> 3  z-> 6
   3                INC A2       -> 4
   4                INC K        -> 5
   5                INC Bs       -> 2
   6                DEC Bs       nz-> 7  z-> 8
   7                INC S        -> 6
   8                DEC K        nz-> 8  z-> 9
   9                DEC A2       nz-> 10  z-> 14
  10                DEC A2       nz-> 11  z-> 12
  11                INC Bs       -> 9
  12                DEC Bs       nz-> 13  z-> 17
  13                INC A2       -> 14
  14                DEC Bs       nz-> 15  z-> 16
  15                INC A2       -> 14
  16                INC K        -> 9
  17                DEC S        nz-> 18  z-> 20
  18                INC A2       -> 19
  19                INC Bs       -> 17
  20                DEC Bs       nz-> 21  z-> 22
  21                INC S        -> 20
  22                DEC A2       nz-> 23  z-> 23
  23                DEC A2       nz-> 24  z-> 26
  24                INC TR       -> 25
  25                DEC A2       nz-> 25  z-> 26
  26 tr_done:       DEC J        nz-> 27  z-> 29
  27                INC Bs       -> 28
  28                INC A2       -> 26
  29                DEC A2       nz-> 30  z-> 31
  30                INC J        -> 29
  31                DEC Bs       nz-> 32  z-> 36
  32                DEC Bs       nz-> 33  z-> 34
  33                INC A2       -> 31
  34                DEC A2       nz-> 35  z-> 39
  35                INC Bs       -> 36
  36                DEC A2       nz-> 37  z-> 38
  37                INC Bs       -> 36
  38                INC E        -> 31
  39                DEC P        nz-> 39  z-> 40
  40                DEC Tb       nz-> 40  z-> 41
  41                DEC K        nz-> 42  z-> 44
  42                INC Bs       -> 43
  43                INC A2       -> 41
  44                DEC A2       nz-> 45  z-> 46
  45                INC K        -> 44
  46                INC Bs       -> 47
  47                INC Bs       -> 48
  48                INC Tb       -> 49
  49 pow:           DEC E        nz-> 50  z-> 58
  50                DEC Tb       nz-> 51  z-> 52
  51                INC P        -> 50
  52 mul:           DEC P        nz-> 53  z-> 49
  53                DEC Bs       nz-> 54  z-> 56
  54                INC Tb       -> 55
  55                INC A2       -> 53
  56                DEC A2       nz-> 57  z-> 52
  57                INC Bs       -> 56
  58 powd:          DEC Bs       nz-> 58  z-> 59
  59                DEC J        nz-> 60  z-> 62
  60                INC P        -> 61
  61                INC A2       -> 59
  62                DEC A2       nz-> 63  z-> 64
  63                INC J        -> 62
  64                DEC S        nz-> 65  z-> 67
  65                INC Bs       -> 66
  66                INC A2       -> 64
  67                DEC A2       nz-> 68  z-> 78
  68                INC S        -> 67
  69 dec_acc:       DEC TR       nz-> 76  z-> 72
  70 dec_rej:       DEC TR       nz-> 72  z-> 76
  71 dec_timeout:   DEC TR       nz-> 71  z-> 72
  72 bad:           BEEP         -> 73
  73                INC J        -> 74
  74                DEC S        nz-> 74  z-> 75
  75                DEC K        nz-> 75  z-> 1
  76 ok:            DEC K        nz-> 76  z-> 77
  77                INC S        -> 2
  78 run:           DEC R        nz-> 78  z-> 79
  79                DEC R1       nz-> 79  z-> 80
  80                DEC Lt       nz-> 80  z-> 81
  81                DEC O        nz-> 81  z-> 82
  82                DEC A        nz-> 82  z-> 83
  83 enc:           DEC Bs       nz-> 84  z-> 89
  84                DEC Bs       nz-> 85  z-> 86
  85                INC A2       -> 83
  86                DEC A2       nz-> 87  z-> 100
  87                INC Bs       -> 88
  88                INC w        -> 89
  89                DEC A2       nz-> 90  z-> 91
  90                INC Bs       -> 89
  91                DEC R        nz-> 92  z-> 94
  92                INC A2       -> 93
  93                INC A2       -> 91
  94                DEC w        nz-> 95  z-> 96
  95                INC A2       -> 94
  96                DEC A2       nz-> 97  z-> 99
  97                INC R        -> 98
  98                INC R        -> 96
  99                INC R        -> 83
 100 step:          DEC Tb       nz-> 101  z-> 163
 101                DEC R        nz-> 102  z-> 105
 102                DEC R        nz-> 103  z-> 104
 103                INC R1       -> 101
 104 a1:            INC O        -> 105
 105                DEC P        nz-> 106  z-> 108
 106                INC A2       -> 107
 107                INC Bs       -> 105
 108                DEC Bs       nz-> 109  z-> 110
 109                INC P        -> 108
 110 parse:         DEC A2       nz-> 111  z-> 116
 111                DEC A2       nz-> 112  z-> 113
 112                INC Bs       -> 110
 113                DEC Bs       nz-> 114  z-> 162
 114                INC A2       -> 115
 115                INC w        -> 116
 116                DEC Bs       nz-> 117  z-> 118
 117                INC A2       -> 116
 118                DEC w        nz-> 119  z-> 122
 119                DEC O        nz-> 120  z-> 121
 120                INC O        -> 110
 121 bit1t:         INC A        -> 110
 122 bit0:          DEC O        nz-> 110  z-> 123
 123 decode:        DEC A2       nz-> 123  z-> 124
 124                DEC A        nz-> 125  z-> 128
 125                DEC A        nz-> 126  z-> 127
 126                INC A2       -> 124
 127 w1:            INC w        -> 128
 128                DEC A2       nz-> 129  z-> 143
 129                DEC A2       nz-> 130  z-> 131
 130                INC A        -> 128
 131 right:         DEC A        nz-> 132  z-> 160
 132                DEC A        nz-> 133  z-> 134
 133                INC O        -> 132
 134                DEC Lt       nz-> 135  z-> 137
 135                INC A2       -> 136
 136                INC A2       -> 134
 137                DEC w        nz-> 138  z-> 139
 138                INC A2       -> 137
 139                DEC A2       nz-> 140  z-> 141
 140                INC Lt       -> 139
 141                DEC R1       nz-> 142  z-> 100
 142                INC R        -> 141
 143 left:          DEC A        nz-> 144  z-> 160
 144                DEC A        nz-> 145  z-> 146
 145                INC O        -> 144
 146                DEC Lt       nz-> 147  z-> 150
 147                DEC Lt       nz-> 148  z-> 149
 148                INC A2       -> 146
 149 l1:            INC R        -> 150
 150                DEC A2       nz-> 151  z-> 152
 151                INC Lt       -> 150
 152                DEC R1       nz-> 153  z-> 155
 153                INC A2       -> 154
 154                INC A2       -> 152
 155                DEC w        nz-> 156  z-> 157
 156                INC A2       -> 155
 157                DEC A2       nz-> 158  z-> 100
 158                INC R        -> 159
 159                INC R        -> 157
 160 halt:          DEC w        nz-> 161  z-> 162
 161 o_acc:         DEC A2       nz-> 164  z-> 69
 162 o_rej:         DEC A2       nz-> 164  z-> 70
 163 o_timeout:     DEC A2       nz-> 164  z-> 71
 164 never:         DEC A2       nz-> 164  z-> 164

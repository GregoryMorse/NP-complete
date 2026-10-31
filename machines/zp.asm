; entry 0
   0                INC J        -> 1
   1 cand:          INC S        -> 2
   2 inst:          DEC S        nz-> 3  z-> 6
   3                INC A2       -> 4
   4                INC K        -> 5
   5                INC Bs       -> 2
   6                DEC Bs       nz-> 7  z-> 8
   7                INC S        -> 6
   8                DEC A2       nz-> 9  z-> 13
   9                DEC A2       nz-> 10  z-> 11
  10                INC Bs       -> 8
  11                DEC Bs       nz-> 12  z-> 16
  12                INC A2       -> 13
  13                DEC Bs       nz-> 14  z-> 15
  14                INC A2       -> 13
  15                INC N        -> 8
  16 cert:          DEC K        nz-> 17  z-> 38
  17                INC C        -> 18
  18                DEC P        nz-> 18  z-> 19
  19                DEC Tb       nz-> 19  z-> 20
  20                DEC S        nz-> 21  z-> 23
  21                INC P        -> 22
  22                INC A2       -> 20
  23                DEC A2       nz-> 24  z-> 25
  24                INC S        -> 23
  25                DEC C        nz-> 26  z-> 28
  26                INC Bs       -> 27
  27                INC A2       -> 25
  28                DEC A2       nz-> 29  z-> 30
  29                INC C        -> 28
  30                DEC N        nz-> 31  z-> 33
  31                INC Tb       -> 32
  32                INC A2       -> 30
  33                DEC A2       nz-> 34  z-> 35
  34                INC N        -> 33
  35                INC F        -> 91
  36 ver_acc:       INC TR       -> 37
  37                DEC K        nz-> 37  z-> 38
  38 certdone:      DEC C        nz-> 38  z-> 39
  39                DEC J        nz-> 40  z-> 42
  40                INC A2       -> 41
  41                INC Bs       -> 39
  42                DEC Bs       nz-> 43  z-> 44
  43                INC J        -> 42
  44                DEC A2       nz-> 45  z-> 49
  45                DEC A2       nz-> 46  z-> 47
  46                INC Bs       -> 44
  47                DEC Bs       nz-> 48  z-> 52
  48                INC A2       -> 49
  49                DEC Bs       nz-> 50  z-> 51
  50                INC A2       -> 49
  51                INC C        -> 44
  52                DEC P        nz-> 52  z-> 53
  53                DEC Tb       nz-> 53  z-> 54
  54                DEC N        nz-> 55  z-> 57
  55                INC Bs       -> 56
  56                INC A2       -> 54
  57                DEC A2       nz-> 58  z-> 59
  58                INC N        -> 57
  59                INC Bs       -> 60
  60                INC Bs       -> 61
  61                INC Tb       -> 62
  62 pow:           DEC C        nz-> 63  z-> 71
  63                DEC Tb       nz-> 64  z-> 65
  64                INC P        -> 63
  65 mul:           DEC P        nz-> 66  z-> 62
  66                DEC Bs       nz-> 67  z-> 69
  67                INC Tb       -> 68
  68                INC A2       -> 66
  69                DEC A2       nz-> 70  z-> 65
  70                INC Bs       -> 69
  71 powd:          DEC Bs       nz-> 71  z-> 72
  72                DEC J        nz-> 73  z-> 75
  73                INC P        -> 74
  74                INC A2       -> 72
  75                DEC A2       nz-> 76  z-> 77
  76                INC J        -> 75
  77                DEC S        nz-> 78  z-> 80
  78                INC Bs       -> 79
  79                INC A2       -> 77
  80                DEC A2       nz-> 81  z-> 91
  81                INC S        -> 80
  82 dec_acc:       DEC TR       nz-> 89  z-> 85
  83 dec_rej:       DEC TR       nz-> 85  z-> 89
  84 dec_timeout:   DEC TR       nz-> 84  z-> 85
  85 bad:           BEEP         -> 86
  86                INC J        -> 87
  87                DEC S        nz-> 87  z-> 88
  88                DEC N        nz-> 88  z-> 1
  89 ok:            DEC N        nz-> 89  z-> 90
  90                INC S        -> 2
  91 run:           DEC R        nz-> 91  z-> 92
  92                DEC R1       nz-> 92  z-> 93
  93                DEC Lt       nz-> 93  z-> 94
  94                DEC O        nz-> 94  z-> 95
  95                DEC A        nz-> 95  z-> 96
  96 enc:           DEC Bs       nz-> 97  z-> 102
  97                DEC Bs       nz-> 98  z-> 99
  98                INC A2       -> 96
  99                DEC A2       nz-> 100  z-> 113
 100                INC Bs       -> 101
 101                INC w        -> 102
 102                DEC A2       nz-> 103  z-> 104
 103                INC Bs       -> 102
 104                DEC R        nz-> 105  z-> 107
 105                INC A2       -> 106
 106                INC A2       -> 104
 107                DEC w        nz-> 108  z-> 109
 108                INC A2       -> 107
 109                DEC A2       nz-> 110  z-> 112
 110                INC R        -> 111
 111                INC R        -> 109
 112                INC R        -> 96
 113 step:          DEC Tb       nz-> 114  z-> 176
 114                DEC R        nz-> 115  z-> 118
 115                DEC R        nz-> 116  z-> 117
 116                INC R1       -> 114
 117 a1:            INC O        -> 118
 118                DEC P        nz-> 119  z-> 121
 119                INC A2       -> 120
 120                INC R        -> 118
 121                DEC R        nz-> 122  z-> 123
 122                INC P        -> 121
 123 parse:         DEC A2       nz-> 124  z-> 129
 124                DEC A2       nz-> 125  z-> 126
 125                INC R        -> 123
 126                DEC R        nz-> 127  z-> 175
 127                INC A2       -> 128
 128                INC w        -> 129
 129                DEC R        nz-> 130  z-> 131
 130                INC A2       -> 129
 131                DEC w        nz-> 132  z-> 135
 132                DEC O        nz-> 133  z-> 134
 133                INC O        -> 123
 134 bit1t:         INC A        -> 123
 135 bit0:          DEC O        nz-> 123  z-> 136
 136 decode:        DEC A2       nz-> 136  z-> 137
 137                DEC A        nz-> 138  z-> 141
 138                DEC A        nz-> 139  z-> 140
 139                INC A2       -> 137
 140 w1:            INC w        -> 141
 141                DEC A2       nz-> 142  z-> 156
 142                DEC A2       nz-> 143  z-> 144
 143                INC A        -> 141
 144 right:         DEC A        nz-> 145  z-> 173
 145                DEC A        nz-> 146  z-> 147
 146                INC O        -> 145
 147                DEC Lt       nz-> 148  z-> 150
 148                INC A2       -> 149
 149                INC A2       -> 147
 150                DEC w        nz-> 151  z-> 152
 151                INC A2       -> 150
 152                DEC A2       nz-> 153  z-> 154
 153                INC Lt       -> 152
 154                DEC R1       nz-> 155  z-> 113
 155                INC R        -> 154
 156 left:          DEC A        nz-> 157  z-> 173
 157                DEC A        nz-> 158  z-> 159
 158                INC O        -> 157
 159                DEC Lt       nz-> 160  z-> 163
 160                DEC Lt       nz-> 161  z-> 162
 161                INC A2       -> 159
 162 l1:            INC R        -> 163
 163                DEC A2       nz-> 164  z-> 165
 164                INC Lt       -> 163
 165                DEC R1       nz-> 166  z-> 168
 166                INC A2       -> 167
 167                INC A2       -> 165
 168                DEC w        nz-> 169  z-> 170
 169                INC A2       -> 168
 170                DEC A2       nz-> 171  z-> 113
 171                INC R        -> 172
 172                INC R        -> 170
 173 halt:          DEC w        nz-> 174  z-> 175
 174 o_acc:         DEC F        nz-> 36  z-> 82
 175 o_rej:         DEC F        nz-> 16  z-> 83
 176 o_timeout:     DEC F        nz-> 16  z-> 84

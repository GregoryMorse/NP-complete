; entry 0
   0                INC J        -> 1
   1 cand:          INC S        -> 2
   2 inst:          DEC S        nz-> 3  z-> 6
   3                INC A2       -> 4
   4                INC K        -> 5
   5                INC E        -> 2
   6                DEC E        nz-> 7  z-> 8
   7                INC S        -> 6
   8                DEC K        nz-> 8  z-> 9
   9                DEC A2       nz-> 10  z-> 14
  10                DEC A2       nz-> 11  z-> 12
  11                INC K        -> 9
  12                DEC K        nz-> 13  z-> 17
  13                INC A2       -> 14
  14                DEC K        nz-> 15  z-> 16
  15                INC A2       -> 14
  16                INC N        -> 9
  17                DEC S        nz-> 18  z-> 20
  18                INC K        -> 19
  19                INC A2       -> 17
  20                DEC A2       nz-> 21  z-> 22
  21                INC S        -> 20
  22                DEC K        nz-> 23  z-> 28
  23                DEC K        nz-> 24  z-> 25
  24                INC A2       -> 22
  25                DEC A2       nz-> 26  z-> 31
  26                INC K        -> 27
  27                INC TR       -> 28
  28                DEC A2       nz-> 29  z-> 30
  29                INC K        -> 28
  30                DEC K        nz-> 30  z-> 31
  31 tr_done:       DEC J        nz-> 32  z-> 34
  32                INC A2       -> 33
  33                INC K        -> 31
  34                DEC K        nz-> 35  z-> 36
  35                INC J        -> 34
  36                DEC A2       nz-> 37  z-> 41
  37                DEC A2       nz-> 38  z-> 39
  38                INC K        -> 36
  39                DEC K        nz-> 40  z-> 44
  40                INC A2       -> 41
  41                DEC K        nz-> 42  z-> 43
  42                INC A2       -> 41
  43                INC E        -> 36
  44                DEC P        nz-> 44  z-> 45
  45                DEC Tb       nz-> 45  z-> 46
  46                DEC N        nz-> 47  z-> 49
  47                INC A2       -> 48
  48                INC K        -> 46
  49                DEC K        nz-> 50  z-> 51
  50                INC N        -> 49
  51                INC A2       -> 52
  52                INC A2       -> 53
  53                INC Tb       -> 54
  54 pow:           DEC E        nz-> 55  z-> 63
  55                DEC Tb       nz-> 56  z-> 57
  56                INC P        -> 55
  57 mul:           DEC P        nz-> 58  z-> 54
  58                DEC A2       nz-> 59  z-> 61
  59                INC Tb       -> 60
  60                INC K        -> 58
  61                DEC K        nz-> 62  z-> 57
  62                INC A2       -> 61
  63 powd:          DEC A2       nz-> 63  z-> 64
  64                DEC J        nz-> 65  z-> 67
  65                INC P        -> 66
  66                INC A2       -> 64
  67                DEC A2       nz-> 68  z-> 69
  68                INC J        -> 67
  69                DEC S        nz-> 70  z-> 72
  70                INC K        -> 71
  71                INC A2       -> 69
  72                DEC A2       nz-> 73  z-> 83
  73                INC S        -> 72
  74 dec_acc:       DEC TR       nz-> 81  z-> 77
  75 dec_rej:       DEC TR       nz-> 77  z-> 81
  76 dec_timeout:   DEC TR       nz-> 76  z-> 77
  77 bad:           BEEP         -> 78
  78                INC J        -> 79
  79                DEC S        nz-> 79  z-> 80
  80                DEC N        nz-> 80  z-> 1
  81 ok:            DEC N        nz-> 81  z-> 82
  82                INC S        -> 2
  83 run:           DEC R        nz-> 83  z-> 84
  84                DEC R1       nz-> 84  z-> 85
  85                DEC Lt       nz-> 85  z-> 86
  86                DEC O        nz-> 86  z-> 87
  87                DEC A        nz-> 87  z-> 88
  88 enc:           DEC K        nz-> 89  z-> 94
  89                DEC K        nz-> 90  z-> 91
  90                INC A2       -> 88
  91                DEC A2       nz-> 92  z-> 105
  92                INC K        -> 93
  93                INC w        -> 94
  94                DEC A2       nz-> 95  z-> 96
  95                INC K        -> 94
  96                DEC R        nz-> 97  z-> 99
  97                INC A2       -> 98
  98                INC A2       -> 96
  99                DEC w        nz-> 100  z-> 101
 100                INC A2       -> 99
 101                DEC A2       nz-> 102  z-> 104
 102                INC R        -> 103
 103                INC R        -> 101
 104                INC R        -> 88
 105 step:          DEC Tb       nz-> 106  z-> 168
 106                DEC R        nz-> 107  z-> 110
 107                DEC R        nz-> 108  z-> 109
 108                INC R1       -> 106
 109 a1:            INC O        -> 110
 110                DEC P        nz-> 111  z-> 113
 111                INC A2       -> 112
 112                INC K        -> 110
 113                DEC K        nz-> 114  z-> 115
 114                INC P        -> 113
 115 parse:         DEC A2       nz-> 116  z-> 121
 116                DEC A2       nz-> 117  z-> 118
 117                INC K        -> 115
 118                DEC K        nz-> 119  z-> 167
 119                INC A2       -> 120
 120                INC w        -> 121
 121                DEC K        nz-> 122  z-> 123
 122                INC A2       -> 121
 123                DEC w        nz-> 124  z-> 127
 124                DEC O        nz-> 125  z-> 126
 125                INC O        -> 115
 126 bit1t:         INC A        -> 115
 127 bit0:          DEC O        nz-> 115  z-> 128
 128 decode:        DEC A2       nz-> 128  z-> 129
 129                DEC A        nz-> 130  z-> 133
 130                DEC A        nz-> 131  z-> 132
 131                INC A2       -> 129
 132 w1:            INC w        -> 133
 133                DEC A2       nz-> 134  z-> 148
 134                DEC A2       nz-> 135  z-> 136
 135                INC A        -> 133
 136 right:         DEC A        nz-> 137  z-> 165
 137                DEC A        nz-> 138  z-> 139
 138                INC O        -> 137
 139                DEC Lt       nz-> 140  z-> 142
 140                INC A2       -> 141
 141                INC A2       -> 139
 142                DEC w        nz-> 143  z-> 144
 143                INC A2       -> 142
 144                DEC A2       nz-> 145  z-> 146
 145                INC Lt       -> 144
 146                DEC R1       nz-> 147  z-> 105
 147                INC R        -> 146
 148 left:          DEC A        nz-> 149  z-> 165
 149                DEC A        nz-> 150  z-> 151
 150                INC O        -> 149
 151                DEC Lt       nz-> 152  z-> 155
 152                DEC Lt       nz-> 153  z-> 154
 153                INC A2       -> 151
 154 l1:            INC R        -> 155
 155                DEC A2       nz-> 156  z-> 157
 156                INC Lt       -> 155
 157                DEC R1       nz-> 158  z-> 160
 158                INC A2       -> 159
 159                INC A2       -> 157
 160                DEC w        nz-> 161  z-> 162
 161                INC A2       -> 160
 162                DEC A2       nz-> 163  z-> 105
 163                INC R        -> 164
 164                INC R        -> 162
 165 halt:          DEC w        nz-> 166  z-> 167
 166 o_acc:         DEC A2       nz-> 169  z-> 74
 167 o_rej:         DEC A2       nz-> 169  z-> 75
 168 o_timeout:     DEC A2       nz-> 169  z-> 76
 169 never:         DEC A2       nz-> 169  z-> 169

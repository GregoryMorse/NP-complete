; entry 0
   0                INC J        -> 1
   1 cand:          INC S        -> 2
   2 inst:          DEC S        nz-> 3  z-> 6
   3                INC Pc       -> 4
   4                INC K        -> 5
   5                INC A2       -> 2
   6                DEC A2       nz-> 7  z-> 8
   7                INC S        -> 6
   8                DEC K        nz-> 8  z-> 9
   9                DEC Pc       nz-> 10  z-> 14
  10                DEC Pc       nz-> 11  z-> 12
  11                INC A2       -> 9
  12                DEC A2       nz-> 13  z-> 17
  13                INC Pc       -> 14
  14                DEC A2       nz-> 15  z-> 16
  15                INC Pc       -> 14
  16                INC N        -> 9
  17                INC C        -> 18
  18                DEC N        nz-> 19  z-> 21
  19                INC Pc       -> 20
  20                INC A2       -> 18
  21                DEC A2       nz-> 22  z-> 23
  22                INC N        -> 21
  23                DEC Pc       nz-> 24  z-> 29
  24                DEC C        nz-> 25  z-> 27
  25                INC A2       -> 26
  26                INC A2       -> 24
  27                DEC A2       nz-> 28  z-> 23
  28                INC C        -> 27
  29                DEC C        nz-> 30  z-> 32
  30                INC K        -> 31
  31                INC A2       -> 29
  32                DEC A2       nz-> 33  z-> 34
  33                INC C        -> 32
  34                DEC C        nz-> 35  z-> 35
  35 cert:          DEC K        nz-> 36  z-> 57
  36                INC C        -> 37
  37                DEC P        nz-> 37  z-> 38
  38                DEC Tb       nz-> 38  z-> 39
  39                DEC S        nz-> 40  z-> 42
  40                INC P        -> 41
  41                INC A2       -> 39
  42                DEC A2       nz-> 43  z-> 44
  43                INC S        -> 42
  44                DEC C        nz-> 45  z-> 47
  45                INC Pc       -> 46
  46                INC A2       -> 44
  47                DEC A2       nz-> 48  z-> 49
  48                INC C        -> 47
  49                DEC N        nz-> 50  z-> 52
  50                INC Tb       -> 51
  51                INC A2       -> 49
  52                DEC A2       nz-> 53  z-> 54
  53                INC N        -> 52
  54                INC F        -> 116
  55 ver_acc:       INC PA       -> 35
  56 ver_rej:       INC PR       -> 35
  57 certdone:      DEC C        nz-> 57  z-> 58
  58                DEC PR       nz-> 59  z-> 60
  59                DEC PA       nz-> 58  z-> 62
  60                DEC PA       nz-> 61  z-> 62
  61                INC TR       -> 62
  62                DEC PA       nz-> 62  z-> 63
  63                DEC PR       nz-> 63  z-> 64
  64                DEC J        nz-> 65  z-> 67
  65                INC Pc       -> 66
  66                INC A2       -> 64
  67                DEC A2       nz-> 68  z-> 69
  68                INC J        -> 67
  69                DEC Pc       nz-> 70  z-> 74
  70                DEC Pc       nz-> 71  z-> 72
  71                INC A2       -> 69
  72                DEC A2       nz-> 73  z-> 77
  73                INC Pc       -> 74
  74                DEC A2       nz-> 75  z-> 76
  75                INC Pc       -> 74
  76                INC C        -> 69
  77                DEC P        nz-> 77  z-> 78
  78                DEC Tb       nz-> 78  z-> 79
  79                DEC N        nz-> 80  z-> 82
  80                INC A2       -> 81
  81                INC Pc       -> 79
  82                DEC Pc       nz-> 83  z-> 84
  83                INC N        -> 82
  84                INC A2       -> 85
  85                INC A2       -> 86
  86                INC Tb       -> 87
  87 pow:           DEC C        nz-> 88  z-> 96
  88                DEC Tb       nz-> 89  z-> 90
  89                INC K        -> 88
  90 mul:           DEC K        nz-> 91  z-> 87
  91                DEC A2       nz-> 92  z-> 94
  92                INC Tb       -> 93
  93                INC Pc       -> 91
  94                DEC Pc       nz-> 95  z-> 90
  95                INC A2       -> 94
  96 powd:          DEC A2       nz-> 96  z-> 97
  97                DEC J        nz-> 98  z-> 100
  98                INC P        -> 99
  99                INC A2       -> 97
 100                DEC A2       nz-> 101  z-> 102
 101                INC J        -> 100
 102                DEC S        nz-> 103  z-> 105
 103                INC Pc       -> 104
 104                INC A2       -> 102
 105                DEC A2       nz-> 106  z-> 116
 106                INC S        -> 105
 107 dec_acc:       DEC TR       nz-> 114  z-> 110
 108 dec_rej:       DEC TR       nz-> 110  z-> 114
 109 dec_timeout:   DEC TR       nz-> 109  z-> 110
 110 bad:           BEEP         -> 111
 111                INC J        -> 112
 112                DEC S        nz-> 112  z-> 113
 113                DEC N        nz-> 113  z-> 1
 114 ok:            DEC N        nz-> 114  z-> 115
 115                INC S        -> 2
 116 run:           DEC R        nz-> 116  z-> 117
 117                DEC R1       nz-> 117  z-> 118
 118                DEC Lt       nz-> 118  z-> 119
 119                DEC O        nz-> 119  z-> 120
 120                DEC A        nz-> 120  z-> 121
 121 enc:           DEC Pc       nz-> 122  z-> 127
 122                DEC Pc       nz-> 123  z-> 124
 123                INC A2       -> 121
 124                DEC A2       nz-> 125  z-> 138
 125                INC Pc       -> 126
 126                INC w        -> 127
 127                DEC A2       nz-> 128  z-> 129
 128                INC Pc       -> 127
 129                DEC R        nz-> 130  z-> 132
 130                INC A2       -> 131
 131                INC A2       -> 129
 132                DEC w        nz-> 133  z-> 134
 133                INC A2       -> 132
 134                DEC A2       nz-> 135  z-> 137
 135                INC R        -> 136
 136                INC R        -> 134
 137                INC R        -> 121
 138 step:          DEC Tb       nz-> 139  z-> 201
 139                DEC R        nz-> 140  z-> 143
 140                DEC R        nz-> 141  z-> 142
 141                INC R1       -> 139
 142 a1:            INC O        -> 143
 143                DEC P        nz-> 144  z-> 146
 144                INC Pc       -> 145
 145                INC A2       -> 143
 146                DEC A2       nz-> 147  z-> 148
 147                INC P        -> 146
 148 parse:         DEC Pc       nz-> 149  z-> 154
 149                DEC Pc       nz-> 150  z-> 151
 150                INC A2       -> 148
 151                DEC A2       nz-> 152  z-> 200
 152                INC Pc       -> 153
 153                INC w        -> 154
 154                DEC A2       nz-> 155  z-> 156
 155                INC Pc       -> 154
 156                DEC w        nz-> 157  z-> 160
 157                DEC O        nz-> 158  z-> 159
 158                INC O        -> 148
 159 bit1t:         INC A        -> 148
 160 bit0:          DEC O        nz-> 148  z-> 161
 161 decode:        DEC Pc       nz-> 161  z-> 162
 162                DEC A        nz-> 163  z-> 166
 163                DEC A        nz-> 164  z-> 165
 164                INC A2       -> 162
 165 w1:            INC w        -> 166
 166                DEC A2       nz-> 167  z-> 181
 167                DEC A2       nz-> 168  z-> 169
 168                INC A        -> 166
 169 right:         DEC A        nz-> 170  z-> 198
 170                DEC A        nz-> 171  z-> 172
 171                INC O        -> 170
 172                DEC Lt       nz-> 173  z-> 175
 173                INC A2       -> 174
 174                INC A2       -> 172
 175                DEC w        nz-> 176  z-> 177
 176                INC A2       -> 175
 177                DEC A2       nz-> 178  z-> 179
 178                INC Lt       -> 177
 179                DEC R1       nz-> 180  z-> 138
 180                INC R        -> 179
 181 left:          DEC A        nz-> 182  z-> 198
 182                DEC A        nz-> 183  z-> 184
 183                INC O        -> 182
 184                DEC Lt       nz-> 185  z-> 188
 185                DEC Lt       nz-> 186  z-> 187
 186                INC A2       -> 184
 187 l1:            INC R        -> 188
 188                DEC A2       nz-> 189  z-> 190
 189                INC Lt       -> 188
 190                DEC R1       nz-> 191  z-> 193
 191                INC A2       -> 192
 192                INC A2       -> 190
 193                DEC w        nz-> 194  z-> 195
 194                INC A2       -> 193
 195                DEC A2       nz-> 196  z-> 138
 196                INC R        -> 197
 197                INC R        -> 195
 198 halt:          DEC w        nz-> 199  z-> 200
 199 o_acc:         DEC F        nz-> 55  z-> 107
 200 o_rej:         DEC F        nz-> 56  z-> 108
 201 o_timeout:     DEC F        nz-> 56  z-> 109

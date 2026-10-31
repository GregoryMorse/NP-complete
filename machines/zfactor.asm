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
  17                DEC N        nz-> 18  z-> 20
  18                INC K        -> 19
  19                INC A2       -> 17
  20                DEC A2       nz-> 21  z-> 22
  21                INC N        -> 20
  22                DEC K        nz-> 23  z-> 26
  23                DEC K        nz-> 24  z-> 25
  24                INC A2       -> 22
  25                INC fa_Dt    -> 26
  26                DEC A2       nz-> 27  z-> 28
  27                INC K        -> 26
  28                DEC fa_Dt    nz-> 90  z-> 29
  29                DEC K        nz-> 30  z-> 90
  30                INC K        -> 31
  31                DEC S        nz-> 32  z-> 34
  32                INC E        -> 33
  33                INC A2       -> 31
  34                DEC A2       nz-> 35  z-> 36
  35                INC S        -> 34
  36                INC A2       -> 37
  37                DEC K        nz-> 38  z-> 57
  38                DEC E        nz-> 39  z-> 44
  39                DEC E        nz-> 40  z-> 41
  40                INC V_mul    -> 38
  41                DEC V_mul    nz-> 42  z-> 90
  42                INC E        -> 43
  43                INC fa_bit   -> 44
  44                DEC V_mul    nz-> 45  z-> 46
  45                INC E        -> 44
  46                DEC fa_bit   nz-> 47  z-> 52
  47                DEC A2       nz-> 48  z-> 50
  48                INC fa_K     -> 49
  49                INC V_mul    -> 47
  50                DEC V_mul    nz-> 51  z-> 52
  51                INC A2       -> 50
  52                DEC A2       nz-> 53  z-> 55
  53                INC V_mul    -> 54
  54                INC V_mul    -> 52
  55                DEC V_mul    nz-> 56  z-> 37
  56                INC A2       -> 55
  57                DEC A2       nz-> 58  z-> 59
  58                DEC E        nz-> 57  z-> 57
  59                DEC fa_K     nz-> 60  z-> 61
  60                INC fa_Kr    -> 59
  61                DEC fa_Kr    nz-> 62  z-> 90
  62                DEC E        nz-> 63  z-> 65
  63                INC fa_Ar    -> 64
  64                INC A2       -> 62
  65                DEC A2       nz-> 66  z-> 67
  66                INC E        -> 65
  67                DEC fa_Ar    nz-> 68  z-> 90
  68                DEC fa_Ar    nz-> 69  z-> 90
  69                INC V_mul    -> 70
  70                INC V_mul    -> 71
  71                DEC fa_Kr    nz-> 72  z-> 90
  72                DEC fa_Ar    nz-> 73  z-> 90
  73                DEC E        nz-> 74  z-> 76
  74                INC K        -> 75
  75                INC A2       -> 73
  76                DEC A2       nz-> 77  z-> 78
  77                INC E        -> 76
  78                DEC K        nz-> 79  z-> 89
  79                INC K        -> 80
  80                DEC V_mul    nz-> 81  z-> 83
  81                INC fa_Dt    -> 82
  82                INC A2       -> 80
  83                DEC A2       nz-> 84  z-> 85
  84                INC V_mul    -> 83
  85                DEC fa_Dt    nz-> 86  z-> 78
  86                DEC K        nz-> 85  z-> 87
  87                DEC fa_Dt    nz-> 87  z-> 88
  88                INC V_mul    -> 71
  89                INC TR       -> 90
  90                DEC K        nz-> 90  z-> 91
  91                DEC fa_Dt    nz-> 91  z-> 92
  92                DEC E        nz-> 92  z-> 93
  93                DEC fa_K     nz-> 93  z-> 94
  94                DEC A2       nz-> 94  z-> 95
  95                DEC fa_Kr    nz-> 95  z-> 96
  96                DEC fa_Ar    nz-> 96  z-> 97
  97                DEC V_mul    nz-> 97  z-> 98
  98                DEC K        nz-> 98  z-> 99
  99                DEC fa_Dt    nz-> 99  z-> 100
 100                DEC fa_bit   nz-> 100  z-> 101
 101                DEC J        nz-> 102  z-> 104
 102                INC K        -> 103
 103                INC A2       -> 101
 104                DEC A2       nz-> 105  z-> 106
 105                INC J        -> 104
 106                DEC K        nz-> 107  z-> 111
 107                DEC K        nz-> 108  z-> 109
 108                INC A2       -> 106
 109                DEC A2       nz-> 110  z-> 114
 110                INC K        -> 111
 111                DEC A2       nz-> 112  z-> 113
 112                INC K        -> 111
 113                INC E        -> 106
 114                DEC P        nz-> 114  z-> 115
 115                DEC Tb       nz-> 115  z-> 116
 116                DEC N        nz-> 117  z-> 119
 117                INC A2       -> 118
 118                INC K        -> 116
 119                DEC K        nz-> 120  z-> 121
 120                INC N        -> 119
 121                INC A2       -> 122
 122                INC A2       -> 123
 123                INC Tb       -> 124
 124 pow:           DEC E        nz-> 125  z-> 133
 125                DEC Tb       nz-> 126  z-> 127
 126                INC V_mul    -> 125
 127 mul:           DEC V_mul    nz-> 128  z-> 124
 128                DEC A2       nz-> 129  z-> 131
 129                INC Tb       -> 130
 130                INC K        -> 128
 131                DEC K        nz-> 132  z-> 127
 132                INC A2       -> 131
 133 powd:          DEC A2       nz-> 133  z-> 134
 134                DEC J        nz-> 135  z-> 137
 135                INC P        -> 136
 136                INC A2       -> 134
 137                DEC A2       nz-> 138  z-> 139
 138                INC J        -> 137
 139                DEC S        nz-> 140  z-> 142
 140                INC K        -> 141
 141                INC A2       -> 139
 142                DEC A2       nz-> 143  z-> 153
 143                INC S        -> 142
 144 dec_acc:       DEC TR       nz-> 151  z-> 147
 145 dec_rej:       DEC TR       nz-> 147  z-> 151
 146 dec_timeout:   DEC TR       nz-> 146  z-> 147
 147 bad:           BEEP         -> 148
 148                INC J        -> 149
 149                DEC S        nz-> 149  z-> 150
 150                DEC N        nz-> 150  z-> 1
 151 ok:            DEC N        nz-> 151  z-> 152
 152                INC S        -> 2
 153 run:           DEC R        nz-> 153  z-> 154
 154                DEC R1       nz-> 154  z-> 155
 155                DEC Lt       nz-> 155  z-> 156
 156                DEC O        nz-> 156  z-> 157
 157                DEC A        nz-> 157  z-> 158
 158 enc:           DEC K        nz-> 159  z-> 164
 159                DEC K        nz-> 160  z-> 161
 160                INC A2       -> 158
 161                DEC A2       nz-> 162  z-> 175
 162                INC K        -> 163
 163                INC w        -> 164
 164                DEC A2       nz-> 165  z-> 166
 165                INC K        -> 164
 166                DEC R        nz-> 167  z-> 169
 167                INC A2       -> 168
 168                INC A2       -> 166
 169                DEC w        nz-> 170  z-> 171
 170                INC A2       -> 169
 171                DEC A2       nz-> 172  z-> 174
 172                INC R        -> 173
 173                INC R        -> 171
 174                INC R        -> 158
 175 step:          DEC Tb       nz-> 176  z-> 238
 176                DEC R        nz-> 177  z-> 180
 177                DEC R        nz-> 178  z-> 179
 178                INC R1       -> 176
 179 a1:            INC O        -> 180
 180                DEC P        nz-> 181  z-> 183
 181                INC A2       -> 182
 182                INC V_mul    -> 180
 183                DEC V_mul    nz-> 184  z-> 185
 184                INC P        -> 183
 185 parse:         DEC A2       nz-> 186  z-> 191
 186                DEC A2       nz-> 187  z-> 188
 187                INC K        -> 185
 188                DEC K        nz-> 189  z-> 237
 189                INC A2       -> 190
 190                INC w        -> 191
 191                DEC K        nz-> 192  z-> 193
 192                INC A2       -> 191
 193                DEC w        nz-> 194  z-> 197
 194                DEC O        nz-> 195  z-> 196
 195                INC O        -> 185
 196 bit1t:         INC A        -> 185
 197 bit0:          DEC O        nz-> 185  z-> 198
 198 decode:        DEC A2       nz-> 198  z-> 199
 199                DEC A        nz-> 200  z-> 203
 200                DEC A        nz-> 201  z-> 202
 201                INC A2       -> 199
 202 w1:            INC w        -> 203
 203                DEC A2       nz-> 204  z-> 218
 204                DEC A2       nz-> 205  z-> 206
 205                INC A        -> 203
 206 right:         DEC A        nz-> 207  z-> 235
 207                DEC A        nz-> 208  z-> 209
 208                INC O        -> 207
 209                DEC Lt       nz-> 210  z-> 212
 210                INC A2       -> 211
 211                INC A2       -> 209
 212                DEC w        nz-> 213  z-> 214
 213                INC A2       -> 212
 214                DEC A2       nz-> 215  z-> 216
 215                INC Lt       -> 214
 216                DEC R1       nz-> 217  z-> 175
 217                INC R        -> 216
 218 left:          DEC A        nz-> 219  z-> 235
 219                DEC A        nz-> 220  z-> 221
 220                INC O        -> 219
 221                DEC Lt       nz-> 222  z-> 225
 222                DEC Lt       nz-> 223  z-> 224
 223                INC A2       -> 221
 224 l1:            INC R        -> 225
 225                DEC A2       nz-> 226  z-> 227
 226                INC Lt       -> 225
 227                DEC R1       nz-> 228  z-> 230
 228                INC A2       -> 229
 229                INC A2       -> 227
 230                DEC w        nz-> 231  z-> 232
 231                INC A2       -> 230
 232                DEC A2       nz-> 233  z-> 175
 233                INC R        -> 234
 234                INC R        -> 232
 235 halt:          DEC w        nz-> 236  z-> 237
 236 o_acc:         DEC A2       nz-> 239  z-> 144
 237 o_rej:         DEC A2       nz-> 239  z-> 145
 238 o_timeout:     DEC A2       nz-> 239  z-> 146
 239 never:         DEC A2       nz-> 239  z-> 239

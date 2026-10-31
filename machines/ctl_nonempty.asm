; entry 165
   0 cand:          INC S        -> 1
   1 inst:          DEC S        nz-> 2  z-> 5
   2                INC E        -> 3
   3                INC A2       -> 4
   4                INC T_inst   -> 1
   5                DEC T_inst   nz-> 6  z-> 7
   6                INC S        -> 5
   7                DEC A2       nz-> 7  z-> 8
   8                DEC E        nz-> 9  z-> 13
   9                DEC E        nz-> 10  z-> 11
  10                INC A2       -> 8
  11                DEC A2       nz-> 12  z-> 16
  12                INC E        -> 13
  13                DEC A2       nz-> 14  z-> 15
  14                INC E        -> 13
  15                INC N        -> 8
  16                DEC S        nz-> 17  z-> 19
  17                INC A2       -> 18
  18                INC T_inst   -> 16
  19                DEC T_inst   nz-> 20  z-> 21
  20                INC S        -> 19
  21                DEC A2       nz-> 22  z-> 22
  22                DEC A2       nz-> 23  z-> 25
  23                INC TR       -> 24
  24                DEC A2       nz-> 24  z-> 25
  25 tr_done:       DEC J        nz-> 26  z-> 28
  26                INC T_inst   -> 27
  27                INC A2       -> 25
  28                DEC A2       nz-> 29  z-> 30
  29                INC J        -> 28
  30                DEC T_inst   nz-> 31  z-> 35
  31                DEC T_inst   nz-> 32  z-> 33
  32                INC A2       -> 30
  33                DEC A2       nz-> 34  z-> 38
  34                INC T_inst   -> 35
  35                DEC A2       nz-> 36  z-> 37
  36                INC T_inst   -> 35
  37                INC E        -> 30
  38                DEC P        nz-> 38  z-> 39
  39                DEC Tb       nz-> 39  z-> 40
  40                DEC N        nz-> 41  z-> 43
  41                INC A2       -> 42
  42                INC T_inst   -> 40
  43                DEC T_inst   nz-> 44  z-> 45
  44                INC N        -> 43
  45                INC A2       -> 46
  46                INC A2       -> 47
  47                INC Tb       -> 48
  48 pow:           DEC E        nz-> 49  z-> 57
  49                DEC Tb       nz-> 50  z-> 51
  50                INC P        -> 49
  51 mul:           DEC P        nz-> 52  z-> 48
  52                DEC A2       nz-> 53  z-> 55
  53                INC Tb       -> 54
  54                INC T_inst   -> 52
  55                DEC T_inst   nz-> 56  z-> 51
  56                INC A2       -> 55
  57 powd:          DEC A2       nz-> 57  z-> 58
  58                DEC J        nz-> 59  z-> 61
  59                INC P        -> 60
  60                INC A2       -> 58
  61                DEC A2       nz-> 62  z-> 63
  62                INC J        -> 61
  63                DEC S        nz-> 64  z-> 66
  64                INC T_inst   -> 65
  65                INC A2       -> 63
  66                DEC A2       nz-> 67  z-> 78
  67                INC S        -> 66
  68 dec_acc:       DEC TR       nz-> 76  z-> 71
  69 dec_rej:       DEC TR       nz-> 71  z-> 76
  70 dec_timeout:   DEC TR       nz-> 70  z-> 71
  71 bad:           BEEP         -> 72
  72                DEC J        nz-> 72  z-> 73
  73                INC CI       -> 165
  74                DEC S        nz-> 74  z-> 75
  75                DEC N        nz-> 75  z-> 0
  76 ok:            DEC N        nz-> 76  z-> 77
  77                INC S        -> 1
  78 run:           DEC R        nz-> 78  z-> 79
  79                DEC R1       nz-> 79  z-> 80
  80                DEC Lt       nz-> 80  z-> 81
  81                DEC O        nz-> 81  z-> 82
  82                DEC A        nz-> 82  z-> 83
  83 enc:           DEC T_inst   nz-> 84  z-> 89
  84                DEC T_inst   nz-> 85  z-> 86
  85                INC A2       -> 83
  86                DEC A2       nz-> 87  z-> 100
  87                INC T_inst   -> 88
  88                INC w        -> 89
  89                DEC A2       nz-> 90  z-> 91
  90                INC T_inst   -> 89
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
 107                INC T_inst   -> 105
 108                DEC T_inst   nz-> 109  z-> 110
 109                INC P        -> 108
 110 parse:         DEC A2       nz-> 111  z-> 116
 111                DEC A2       nz-> 112  z-> 113
 112                INC T_inst   -> 110
 113                DEC T_inst   nz-> 114  z-> 162
 114                INC A2       -> 115
 115                INC w        -> 116
 116                DEC T_inst   nz-> 117  z-> 118
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
 161 o_acc:         DEC A2       nz-> 164  z-> 68
 162 o_rej:         DEC A2       nz-> 164  z-> 69
 163 o_timeout:     DEC A2       nz-> 164  z-> 70
 164 never:         DEC A2       nz-> 164  z-> 164
 165 load:          DEC CI       nz-> 166  z-> 168
 166                INC A2       -> 167
 167                INC T_inst   -> 165
 168                DEC T_inst   nz-> 169  z-> 170
 169                INC CI       -> 168
 170                DEC A2       nz-> 179  z-> 171
 171                DEC J        nz-> 172  z-> 174
 172                INC A2       -> 173
 173                INC A2       -> 171
 174                DEC A2       nz-> 175  z-> 176
 175                INC J        -> 174
 176                INC J        -> 177
 177                DEC S        nz-> 177  z-> 178
 178                DEC N        nz-> 178  z-> 0
 179                DEC A2       nz-> 234  z-> 180
 180                DEC J        nz-> 181  z-> 183
 181                INC A2       -> 182
 182                INC A2       -> 180
 183                DEC A2       nz-> 184  z-> 185
 184                INC J        -> 183
 185                INC J        -> 186
 186                DEC J        nz-> 187  z-> 189
 187                INC A2       -> 188
 188                INC A2       -> 186
 189                DEC A2       nz-> 190  z-> 191
 190                INC J        -> 189
 191                DEC J        nz-> 192  z-> 194
 192                INC A2       -> 193
 193                INC A2       -> 191
 194                DEC A2       nz-> 195  z-> 196
 195                INC J        -> 194
 196                INC J        -> 197
 197                DEC J        nz-> 198  z-> 200
 198                INC A2       -> 199
 199                INC A2       -> 197
 200                DEC A2       nz-> 201  z-> 202
 201                INC J        -> 200
 202                INC J        -> 203
 203                DEC J        nz-> 204  z-> 206
 204                INC A2       -> 205
 205                INC A2       -> 203
 206                DEC A2       nz-> 207  z-> 208
 207                INC J        -> 206
 208                INC J        -> 209
 209                DEC J        nz-> 210  z-> 212
 210                INC A2       -> 211
 211                INC A2       -> 209
 212                DEC A2       nz-> 213  z-> 214
 213                INC J        -> 212
 214                DEC J        nz-> 215  z-> 217
 215                INC A2       -> 216
 216                INC A2       -> 214
 217                DEC A2       nz-> 218  z-> 219
 218                INC J        -> 217
 219                INC J        -> 220
 220                DEC J        nz-> 221  z-> 223
 221                INC A2       -> 222
 222                INC A2       -> 220
 223                DEC A2       nz-> 224  z-> 225
 224                INC J        -> 223
 225                INC J        -> 226
 226                DEC J        nz-> 227  z-> 229
 227                INC A2       -> 228
 228                INC A2       -> 226
 229                DEC A2       nz-> 230  z-> 231
 230                INC J        -> 229
 231                INC J        -> 232
 232                DEC S        nz-> 232  z-> 233
 233                DEC N        nz-> 233  z-> 0
 234                DEC A2       nz-> 272  z-> 235
 235                DEC J        nz-> 236  z-> 238
 236                INC A2       -> 237
 237                INC A2       -> 235
 238                DEC A2       nz-> 239  z-> 240
 239                INC J        -> 238
 240                INC J        -> 241
 241                DEC J        nz-> 242  z-> 244
 242                INC A2       -> 243
 243                INC A2       -> 241
 244                DEC A2       nz-> 245  z-> 246
 245                INC J        -> 244
 246                DEC J        nz-> 247  z-> 249
 247                INC A2       -> 248
 248                INC A2       -> 246
 249                DEC A2       nz-> 250  z-> 251
 250                INC J        -> 249
 251                INC J        -> 252
 252                DEC J        nz-> 253  z-> 255
 253                INC A2       -> 254
 254                INC A2       -> 252
 255                DEC A2       nz-> 256  z-> 257
 256                INC J        -> 255
 257                INC J        -> 258
 258                DEC J        nz-> 259  z-> 261
 259                INC A2       -> 260
 260                INC A2       -> 258
 261                DEC A2       nz-> 262  z-> 263
 262                INC J        -> 261
 263                INC J        -> 264
 264                DEC J        nz-> 265  z-> 267
 265                INC A2       -> 266
 266                INC A2       -> 264
 267                DEC A2       nz-> 268  z-> 269
 268                INC J        -> 267
 269                INC J        -> 270
 270                DEC S        nz-> 270  z-> 271
 271                DEC N        nz-> 271  z-> 0
 272                DEC A2       nz-> 297  z-> 273
 273                DEC J        nz-> 274  z-> 276
 274                INC A2       -> 275
 275                INC A2       -> 273
 276                DEC A2       nz-> 277  z-> 278
 277                INC J        -> 276
 278                INC J        -> 279
 279                DEC J        nz-> 280  z-> 282
 280                INC A2       -> 281
 281                INC A2       -> 279
 282                DEC A2       nz-> 283  z-> 284
 283                INC J        -> 282
 284                DEC J        nz-> 285  z-> 287
 285                INC A2       -> 286
 286                INC A2       -> 284
 287                DEC A2       nz-> 288  z-> 289
 288                INC J        -> 287
 289                INC J        -> 290
 290                DEC J        nz-> 291  z-> 293
 291                INC A2       -> 292
 292                INC A2       -> 290
 293                DEC A2       nz-> 294  z-> 295
 294                INC J        -> 293
 295                DEC S        nz-> 295  z-> 296
 296                DEC N        nz-> 296  z-> 0
 297                DEC A2       nz-> 297  z-> 298
 298 idle:          DEC A2       nz-> 298  z-> 298

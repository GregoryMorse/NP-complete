; entry 177
   0 cand:          INC S        -> 1
   1 inst:          DEC S        nz-> 2  z-> 5
   2                INC Bs       -> 3
   3                INC E        -> 4
   4                INC A2       -> 1
   5                DEC A2       nz-> 6  z-> 7
   6                INC S        -> 5
   7                DEC Bs       nz-> 8  z-> 12
   8                DEC Bs       nz-> 9  z-> 10
   9                INC A2       -> 7
  10                DEC A2       nz-> 11  z-> 15
  11                INC Bs       -> 12
  12                DEC A2       nz-> 13  z-> 14
  13                INC Bs       -> 12
  14                INC N        -> 7
  15 cert:          DEC E        nz-> 16  z-> 37
  16                INC C        -> 17
  17                DEC P        nz-> 17  z-> 18
  18                DEC Tb       nz-> 18  z-> 19
  19                DEC S        nz-> 20  z-> 22
  20                INC P        -> 21
  21                INC A2       -> 19
  22                DEC A2       nz-> 23  z-> 24
  23                INC S        -> 22
  24                DEC C        nz-> 25  z-> 27
  25                INC Bs       -> 26
  26                INC A2       -> 24
  27                DEC A2       nz-> 28  z-> 29
  28                INC C        -> 27
  29                DEC N        nz-> 30  z-> 32
  30                INC Tb       -> 31
  31                INC A2       -> 29
  32                DEC A2       nz-> 33  z-> 34
  33                INC N        -> 32
  34                INC F        -> 91
  35 ver_acc:       INC TR       -> 36
  36                DEC E        nz-> 36  z-> 37
  37 certdone:      DEC C        nz-> 37  z-> 38
  38                DEC J        nz-> 39  z-> 41
  39                INC A2       -> 40
  40                INC Bs       -> 38
  41                DEC Bs       nz-> 42  z-> 43
  42                INC J        -> 41
  43                DEC A2       nz-> 44  z-> 48
  44                DEC A2       nz-> 45  z-> 46
  45                INC Bs       -> 43
  46                DEC Bs       nz-> 47  z-> 51
  47                INC A2       -> 48
  48                DEC Bs       nz-> 49  z-> 50
  49                INC A2       -> 48
  50                INC E        -> 43
  51                DEC P        nz-> 51  z-> 52
  52                DEC Tb       nz-> 52  z-> 53
  53                DEC N        nz-> 54  z-> 56
  54                INC Bs       -> 55
  55                INC A2       -> 53
  56                DEC A2       nz-> 57  z-> 58
  57                INC N        -> 56
  58                INC Bs       -> 59
  59                INC Bs       -> 60
  60                INC Tb       -> 61
  61 pow:           DEC E        nz-> 62  z-> 70
  62                DEC Tb       nz-> 63  z-> 64
  63                INC C        -> 62
  64 mul:           DEC C        nz-> 65  z-> 61
  65                DEC Bs       nz-> 66  z-> 68
  66                INC Tb       -> 67
  67                INC A2       -> 65
  68                DEC A2       nz-> 69  z-> 64
  69                INC Bs       -> 68
  70 powd:          DEC Bs       nz-> 70  z-> 71
  71                DEC J        nz-> 72  z-> 74
  72                INC P        -> 73
  73                INC A2       -> 71
  74                DEC A2       nz-> 75  z-> 76
  75                INC J        -> 74
  76                DEC S        nz-> 77  z-> 79
  77                INC Bs       -> 78
  78                INC A2       -> 76
  79                DEC A2       nz-> 80  z-> 91
  80                INC S        -> 79
  81 dec_acc:       DEC TR       nz-> 89  z-> 84
  82 dec_rej:       DEC TR       nz-> 84  z-> 89
  83 dec_timeout:   DEC TR       nz-> 83  z-> 84
  84 bad:           BEEP         -> 85
  85                DEC J        nz-> 85  z-> 86
  86                INC CI       -> 177
  87                DEC S        nz-> 87  z-> 88
  88                DEC N        nz-> 88  z-> 0
  89 ok:            DEC N        nz-> 89  z-> 90
  90                INC S        -> 1
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
 119                INC Bs       -> 120
 120                INC A2       -> 118
 121                DEC A2       nz-> 122  z-> 123
 122                INC P        -> 121
 123 parse:         DEC Bs       nz-> 124  z-> 129
 124                DEC Bs       nz-> 125  z-> 126
 125                INC A2       -> 123
 126                DEC A2       nz-> 127  z-> 175
 127                INC Bs       -> 128
 128                INC w        -> 129
 129                DEC A2       nz-> 130  z-> 131
 130                INC Bs       -> 129
 131                DEC w        nz-> 132  z-> 135
 132                DEC O        nz-> 133  z-> 134
 133                INC O        -> 123
 134 bit1t:         INC A        -> 123
 135 bit0:          DEC O        nz-> 123  z-> 136
 136 decode:        DEC Bs       nz-> 136  z-> 137
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
 174 o_acc:         DEC F        nz-> 35  z-> 81
 175 o_rej:         DEC F        nz-> 15  z-> 82
 176 o_timeout:     DEC F        nz-> 15  z-> 83
 177 load:          DEC CI       nz-> 178  z-> 180
 178                INC A2       -> 179
 179                INC Bs       -> 177
 180                DEC Bs       nz-> 181  z-> 182
 181                INC CI       -> 180
 182                DEC A2       nz-> 237  z-> 183
 183                DEC J        nz-> 184  z-> 186
 184                INC A2       -> 185
 185                INC A2       -> 183
 186                DEC A2       nz-> 187  z-> 188
 187                INC J        -> 186
 188                INC J        -> 189
 189                DEC J        nz-> 190  z-> 192
 190                INC A2       -> 191
 191                INC A2       -> 189
 192                DEC A2       nz-> 193  z-> 194
 193                INC J        -> 192
 194                DEC J        nz-> 195  z-> 197
 195                INC A2       -> 196
 196                INC A2       -> 194
 197                DEC A2       nz-> 198  z-> 199
 198                INC J        -> 197
 199                INC J        -> 200
 200                DEC J        nz-> 201  z-> 203
 201                INC A2       -> 202
 202                INC A2       -> 200
 203                DEC A2       nz-> 204  z-> 205
 204                INC J        -> 203
 205                INC J        -> 206
 206                DEC J        nz-> 207  z-> 209
 207                INC A2       -> 208
 208                INC A2       -> 206
 209                DEC A2       nz-> 210  z-> 211
 210                INC J        -> 209
 211                INC J        -> 212
 212                DEC J        nz-> 213  z-> 215
 213                INC A2       -> 214
 214                INC A2       -> 212
 215                DEC A2       nz-> 216  z-> 217
 216                INC J        -> 215
 217                DEC J        nz-> 218  z-> 220
 218                INC A2       -> 219
 219                INC A2       -> 217
 220                DEC A2       nz-> 221  z-> 222
 221                INC J        -> 220
 222                INC J        -> 223
 223                DEC J        nz-> 224  z-> 226
 224                INC A2       -> 225
 225                INC A2       -> 223
 226                DEC A2       nz-> 227  z-> 228
 227                INC J        -> 226
 228                INC J        -> 229
 229                DEC J        nz-> 230  z-> 232
 230                INC A2       -> 231
 231                INC A2       -> 229
 232                DEC A2       nz-> 233  z-> 234
 233                INC J        -> 232
 234                INC J        -> 235
 235                DEC S        nz-> 235  z-> 236
 236                DEC N        nz-> 236  z-> 0
 237                DEC A2       nz-> 275  z-> 238
 238                DEC J        nz-> 239  z-> 241
 239                INC A2       -> 240
 240                INC A2       -> 238
 241                DEC A2       nz-> 242  z-> 243
 242                INC J        -> 241
 243                INC J        -> 244
 244                DEC J        nz-> 245  z-> 247
 245                INC A2       -> 246
 246                INC A2       -> 244
 247                DEC A2       nz-> 248  z-> 249
 248                INC J        -> 247
 249                DEC J        nz-> 250  z-> 252
 250                INC A2       -> 251
 251                INC A2       -> 249
 252                DEC A2       nz-> 253  z-> 254
 253                INC J        -> 252
 254                INC J        -> 255
 255                DEC J        nz-> 256  z-> 258
 256                INC A2       -> 257
 257                INC A2       -> 255
 258                DEC A2       nz-> 259  z-> 260
 259                INC J        -> 258
 260                INC J        -> 261
 261                DEC J        nz-> 262  z-> 264
 262                INC A2       -> 263
 263                INC A2       -> 261
 264                DEC A2       nz-> 265  z-> 266
 265                INC J        -> 264
 266                INC J        -> 267
 267                DEC J        nz-> 268  z-> 270
 268                INC A2       -> 269
 269                INC A2       -> 267
 270                DEC A2       nz-> 271  z-> 272
 271                INC J        -> 270
 272                INC J        -> 273
 273                DEC S        nz-> 273  z-> 274
 274                DEC N        nz-> 274  z-> 0
 275                DEC A2       nz-> 284  z-> 276
 276                DEC J        nz-> 277  z-> 279
 277                INC A2       -> 278
 278                INC A2       -> 276
 279                DEC A2       nz-> 280  z-> 281
 280                INC J        -> 279
 281                INC J        -> 282
 282                DEC S        nz-> 282  z-> 283
 283                DEC N        nz-> 283  z-> 0
 284                DEC A2       nz-> 309  z-> 285
 285                DEC J        nz-> 286  z-> 288
 286                INC A2       -> 287
 287                INC A2       -> 285
 288                DEC A2       nz-> 289  z-> 290
 289                INC J        -> 288
 290                INC J        -> 291
 291                DEC J        nz-> 292  z-> 294
 292                INC A2       -> 293
 293                INC A2       -> 291
 294                DEC A2       nz-> 295  z-> 296
 295                INC J        -> 294
 296                DEC J        nz-> 297  z-> 299
 297                INC A2       -> 298
 298                INC A2       -> 296
 299                DEC A2       nz-> 300  z-> 301
 300                INC J        -> 299
 301                INC J        -> 302
 302                DEC J        nz-> 303  z-> 305
 303                INC A2       -> 304
 304                INC A2       -> 302
 305                DEC A2       nz-> 306  z-> 307
 306                INC J        -> 305
 307                DEC S        nz-> 307  z-> 308
 308                DEC N        nz-> 308  z-> 0
 309                DEC A2       nz-> 309  z-> 310
 310 idle:          DEC A2       nz-> 310  z-> 310

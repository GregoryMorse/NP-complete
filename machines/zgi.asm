; entry 0
   0                INC J        -> 1
   1 cand:          INC S        -> 2
   2 inst:          DEC S        nz-> 3  z-> 6
   3                INC A2       -> 4
   4                INC Bs       -> 5
   5                INC E        -> 2
   6                DEC E        nz-> 7  z-> 8
   7                INC S        -> 6
   8                DEC Bs       nz-> 8  z-> 9
   9                DEC A2       nz-> 10  z-> 14
  10                DEC A2       nz-> 11  z-> 12
  11                INC U_right  -> 9
  12                DEC U_right  nz-> 13  z-> 69
  13                INC A2       -> 14
  14                DEC U_right  nz-> 15  z-> 16
  15                INC A2       -> 14
  16                INC N        -> 9
  17                DEC gi_F     nz-> 18  z-> 20
  18                INC gi_dY    -> 19
  19                INC U_right  -> 17
  20                DEC U_right  nz-> 21  z-> 22
  21                INC gi_F     -> 20
  22                DEC A2       nz-> 23  z-> 37
  23                DEC Bs       nz-> 24  z-> 26
  24                INC _t_gi_m166 -> 25
  25                INC _t_N96   -> 23
  26                DEC _t_N96   nz-> 27  z-> 28
  27                INC Bs       -> 26
  28                DEC _t_gi_m166 nz-> 29  z-> 31
  29                DEC gi_dY    nz-> 30  z-> 33
  30                INC _t_N96   -> 28
  31                INC U_right  -> 32
  32                DEC _t_N96   nz-> 32  z-> 23
  33                DEC _t_gi_m166 nz-> 33  z-> 34
  34                DEC _t_N96   nz-> 34  z-> 35
  35                DEC U_right  nz-> 36  z-> 22
  36                INC gi_dY    -> 35
  37                DEC Bs       nz-> 38  z-> 40
  38                INC _t_gi_m166 -> 39
  39                INC A2       -> 37
  40                DEC A2       nz-> 41  z-> 42
  41                INC Bs       -> 40
  42                DEC _t_gi_m166 nz-> 43  z-> 45
  43                DEC gi_dY    nz-> 44  z-> 47
  44                INC A2       -> 42
  45                INC U_right  -> 46
  46                DEC A2       nz-> 46  z-> 37
  47                DEC _t_gi_m166 nz-> 47  z-> 48
  48                DEC U_right  nz-> 48  z-> 49
  49                DEC gi_rf_digit nz-> 174  z-> 166
  50                DEC S        nz-> 51  z-> 53
  51                INC U_right  -> 52
  52                INC A2       -> 50
  53                DEC A2       nz-> 54  z-> 55
  54                INC S        -> 53
  55                DEC _t_N96   nz-> 56  z-> 61
  56                DEC U_right  nz-> 57  z-> 59
  57                DEC U_right  nz-> 58  z-> 59
  58                INC A2       -> 56
  59                DEC A2       nz-> 60  z-> 55
  60                INC U_right  -> 59
  61                DEC U_right  nz-> 62  z-> 65
  62                DEC U_right  nz-> 63  z-> 64
  63                INC A2       -> 61
  64                INC gi_BV    -> 65
  65                DEC A2       nz-> 66  z-> 67
  66                INC U_right  -> 65
  67                DEC U_right  nz-> 67  z-> 68
  68                DEC gi_rf_bit nz-> 248  z-> 227
  69                INC Bs       -> 70
  70                DEC Bs       nz-> 71  z-> 73
  71                INC A2       -> 72
  72                INC _t_gi_m80 -> 70
  73                DEC _t_gi_m80 nz-> 74  z-> 75
  74                INC Bs       -> 73
  75                DEC A2       nz-> 76  z-> 81
  76                DEC Bs       nz-> 77  z-> 79
  77                INC U_right  -> 78
  78                INC _t_N96   -> 76
  79                DEC _t_N96   nz-> 80  z-> 75
  80                INC Bs       -> 79
  81                DEC U_right  nz-> 82  z-> 84
  82                INC A2       -> 83
  83                INC A2       -> 81
  84                DEC A2       nz-> 85  z-> 86
  85                INC U_right  -> 84
  86                DEC N        nz-> 87  z-> 89
  87                INC A2       -> 88
  88                INC _t_N96   -> 86
  89                DEC _t_N96   nz-> 90  z-> 91
  90                INC N        -> 89
  91                DEC U_right  nz-> 92  z-> 93
  92                DEC A2       nz-> 91  z-> 262
  93                DEC A2       nz-> 94  z-> 96
  94                DEC A2       nz-> 94  z-> 95
  95                INC Bs       -> 70
  96                DEC Bs       nz-> 97  z-> 99
  97                INC A2       -> 98
  98                INC U_right  -> 96
  99                DEC U_right  nz-> 100  z-> 101
 100                INC Bs       -> 99
 101                DEC A2       nz-> 102  z-> 107
 102                DEC Bs       nz-> 103  z-> 105
 103                INC gi_M2    -> 104
 104                INC U_right  -> 102
 105                DEC U_right  nz-> 106  z-> 101
 106                INC Bs       -> 105
 107                INC _t_gi_m166 -> 108
 108                DEC Bs       nz-> 109  z-> 111
 109                INC E        -> 110
 110                INC A2       -> 108
 111                DEC A2       nz-> 112  z-> 113
 112                INC Bs       -> 111
 113                DEC E        nz-> 114  z-> 128
 114                DEC _t_gi_m166 nz-> 115  z-> 116
 115                INC _t_gi_m80 -> 114
 116                DEC _t_gi_m80 nz-> 117  z-> 119
 117                INC A2       -> 118
 118                INC U_right  -> 116
 119                DEC U_right  nz-> 120  z-> 121
 120                INC _t_gi_m80 -> 119
 121                DEC A2       nz-> 122  z-> 127
 122                DEC Bs       nz-> 123  z-> 125
 123                INC _t_gi_m166 -> 124
 124                INC _t_N96   -> 122
 125                DEC _t_N96   nz-> 126  z-> 121
 126                INC Bs       -> 125
 127                DEC _t_gi_m80 nz-> 127  z-> 113
 128                DEC _t_gi_m166 nz-> 129  z-> 130
 129                INC gi_Frem  -> 128
 130                DEC gi_Frem  nz-> 131  z-> 262
 131                DEC _t_gi_m80 nz-> 132  z-> 134
 132                INC _t_N96   -> 133
 133                INC U_right  -> 131
 134                DEC U_right  nz-> 135  z-> 136
 135                INC _t_gi_m80 -> 134
 136                DEC Bs       nz-> 137  z-> 139
 137                INC A2       -> 138
 138                INC U_right  -> 136
 139                DEC U_right  nz-> 140  z-> 141
 140                INC Bs       -> 139
 141                DEC _t_N96   nz-> 142  z-> 144
 142                DEC A2       nz-> 141  z-> 143
 143                DEC _t_N96   nz-> 143  z-> 146
 144                DEC A2       nz-> 145  z-> 261
 145                DEC A2       nz-> 145  z-> 146
 146                DEC E        nz-> 147  z-> 149
 147                INC _t_N96   -> 148
 148                INC A2       -> 146
 149                DEC A2       nz-> 150  z-> 151
 150                INC E        -> 149
 151                DEC Bs       nz-> 152  z-> 154
 152                INC A2       -> 153
 153                INC _t_gi_m166 -> 151
 154                DEC _t_gi_m166 nz-> 155  z-> 156
 155                INC Bs       -> 154
 156                DEC _t_N96   nz-> 157  z-> 159
 157                DEC A2       nz-> 156  z-> 158
 158                DEC _t_N96   nz-> 158  z-> 161
 159                DEC A2       nz-> 160  z-> 252
 160                DEC A2       nz-> 160  z-> 161
 161                DEC _t_gi_m80 nz-> 162  z-> 164
 162                INC A2       -> 163
 163                INC U_right  -> 161
 164                DEC U_right  nz-> 165  z-> 17
 165                INC _t_gi_m80 -> 164
 166                DEC A2       nz-> 167  z-> 168
 167                INC gi_FI    -> 166
 168                DEC E        nz-> 169  z-> 171
 169                INC A2       -> 170
 170                INC _t_N96   -> 168
 171                DEC _t_N96   nz-> 172  z-> 173
 172                INC E        -> 171
 173                INC gi_rf_digit -> 17
 174                DEC A2       nz-> 175  z-> 176
 175                INC gi_FJ    -> 174
 176                DEC _t_gi_m80 nz-> 177  z-> 179
 177                INC _t_N96   -> 178
 178                INC A2       -> 176
 179                DEC A2       nz-> 180  z-> 181
 180                INC _t_gi_m80 -> 179
 181                DEC E        nz-> 182  z-> 184
 182                INC A2       -> 183
 183                INC U_right  -> 181
 184                DEC U_right  nz-> 185  z-> 186
 185                INC E        -> 184
 186                DEC _t_N96   nz-> 187  z-> 189
 187                DEC A2       nz-> 186  z-> 188
 188                DEC _t_N96   nz-> 188  z-> 191
 189                DEC A2       nz-> 190  z-> 206
 190                DEC A2       nz-> 190  z-> 191
 191                DEC gi_FI    nz-> 192  z-> 194
 192                INC _t_N96   -> 193
 193                INC A2       -> 191
 194                DEC A2       nz-> 195  z-> 196
 195                INC gi_FI    -> 194
 196                DEC gi_FJ    nz-> 197  z-> 199
 197                INC A2       -> 198
 198                INC U_right  -> 196
 199                DEC U_right  nz-> 200  z-> 201
 200                INC gi_FJ    -> 199
 201                DEC _t_N96   nz-> 202  z-> 204
 202                DEC A2       nz-> 201  z-> 203
 203                DEC _t_N96   nz-> 203  z-> 206
 204                DEC A2       nz-> 205  z-> 254
 205                DEC A2       nz-> 205  z-> 206
 206                DEC gi_M2    nz-> 207  z-> 209
 207                INC _t_N96   -> 208
 208                INC A2       -> 206
 209                DEC A2       nz-> 210  z-> 211
 210                INC gi_M2    -> 209
 211                DEC _t_gi_m80 nz-> 212  z-> 214
 212                INC A2       -> 213
 213                INC U_right  -> 211
 214                DEC U_right  nz-> 215  z-> 216
 215                INC _t_gi_m80 -> 214
 216                DEC A2       nz-> 217  z-> 222
 217                DEC Bs       nz-> 218  z-> 220
 218                INC _t_N96   -> 219
 219                INC U_right  -> 217
 220                DEC U_right  nz-> 221  z-> 216
 221                INC Bs       -> 220
 222                DEC E        nz-> 223  z-> 225
 223                INC _t_N96   -> 224
 224                INC U_right  -> 222
 225                DEC U_right  nz-> 226  z-> 50
 226                INC E        -> 225
 227                DEC gi_BV    nz-> 228  z-> 229
 228                INC gi_G     -> 227
 229                DEC gi_FI    nz-> 230  z-> 232
 230                INC A2       -> 231
 231                INC U_right  -> 229
 232                DEC U_right  nz-> 233  z-> 234
 233                INC gi_FI    -> 232
 234                DEC A2       nz-> 235  z-> 240
 235                DEC Bs       nz-> 236  z-> 238
 236                INC _t_N96   -> 237
 237                INC U_right  -> 235
 238                DEC U_right  nz-> 239  z-> 234
 239                INC Bs       -> 238
 240                DEC gi_FJ    nz-> 241  z-> 243
 241                INC _t_N96   -> 242
 242                INC A2       -> 240
 243                DEC A2       nz-> 244  z-> 245
 244                INC gi_FJ    -> 243
 245                DEC gi_FI    nz-> 245  z-> 246
 246                DEC gi_FJ    nz-> 246  z-> 247
 247                INC gi_rf_bit -> 50
 248                DEC gi_G     nz-> 249  z-> 250
 249                DEC gi_BV    nz-> 251  z-> 254
 250                DEC gi_BV    nz-> 254  z-> 251
 251                INC E        -> 146
 252                DEC E        nz-> 252  z-> 253
 253                INC _t_gi_m80 -> 131
 254                DEC gi_FI    nz-> 254  z-> 255
 255                DEC gi_FJ    nz-> 255  z-> 256
 256                DEC gi_BV    nz-> 256  z-> 257
 257                DEC gi_G     nz-> 257  z-> 258
 258                DEC _t_gi_m80 nz-> 258  z-> 259
 259                DEC E        nz-> 259  z-> 260
 260                INC gi_F     -> 130
 261                INC TR       -> 262
 262                DEC Bs       nz-> 262  z-> 263
 263                DEC gi_M2    nz-> 263  z-> 264
 264                DEC _t_gi_m166 nz-> 264  z-> 265
 265                DEC gi_F     nz-> 265  z-> 266
 266                DEC gi_Frem  nz-> 266  z-> 267
 267                DEC _t_gi_m80 nz-> 267  z-> 268
 268                DEC E        nz-> 268  z-> 269
 269                DEC U_right  nz-> 269  z-> 270
 270                DEC A2       nz-> 270  z-> 271
 271                DEC J        nz-> 272  z-> 274
 272                INC A2       -> 273
 273                INC Bs       -> 271
 274                DEC Bs       nz-> 275  z-> 276
 275                INC J        -> 274
 276                DEC A2       nz-> 277  z-> 281
 277                DEC A2       nz-> 278  z-> 279
 278                INC U_right  -> 276
 279                DEC U_right  nz-> 280  z-> 284
 280                INC A2       -> 281
 281                DEC U_right  nz-> 282  z-> 283
 282                INC A2       -> 281
 283                INC E        -> 276
 284                DEC P        nz-> 284  z-> 285
 285                DEC Tb       nz-> 285  z-> 286
 286                DEC N        nz-> 287  z-> 289
 287                INC Bs       -> 288
 288                INC A2       -> 286
 289                DEC A2       nz-> 290  z-> 291
 290                INC N        -> 289
 291                INC Bs       -> 292
 292                INC Bs       -> 293
 293                INC Tb       -> 294
 294 pow:           DEC E        nz-> 295  z-> 303
 295                DEC Tb       nz-> 296  z-> 297
 296                INC U_right  -> 295
 297 mul:           DEC U_right  nz-> 298  z-> 294
 298                DEC Bs       nz-> 299  z-> 301
 299                INC Tb       -> 300
 300                INC A2       -> 298
 301                DEC A2       nz-> 302  z-> 297
 302                INC Bs       -> 301
 303 powd:          DEC Bs       nz-> 303  z-> 304
 304                DEC J        nz-> 305  z-> 307
 305                INC P        -> 306
 306                INC A2       -> 304
 307                DEC A2       nz-> 308  z-> 309
 308                INC J        -> 307
 309                DEC S        nz-> 310  z-> 312
 310                INC U_right  -> 311
 311                INC A2       -> 309
 312                DEC A2       nz-> 313  z-> 323
 313                INC S        -> 312
 314 dec_acc:       DEC TR       nz-> 321  z-> 317
 315 dec_rej:       DEC TR       nz-> 317  z-> 321
 316 dec_timeout:   DEC TR       nz-> 316  z-> 317
 317 bad:           BEEP         -> 318
 318                INC J        -> 319
 319                DEC S        nz-> 319  z-> 320
 320                DEC N        nz-> 320  z-> 1
 321 ok:            DEC N        nz-> 321  z-> 322
 322                INC S        -> 2
 323 run:           DEC R        nz-> 323  z-> 324
 324                DEC R1       nz-> 324  z-> 325
 325                DEC Lt       nz-> 325  z-> 326
 326                DEC O        nz-> 326  z-> 327
 327                DEC A        nz-> 327  z-> 328
 328 enc:           DEC U_right  nz-> 329  z-> 334
 329                DEC U_right  nz-> 330  z-> 331
 330                INC Bs       -> 328
 331                DEC Bs       nz-> 332  z-> 345
 332                INC U_right  -> 333
 333                INC w        -> 334
 334                DEC Bs       nz-> 335  z-> 336
 335                INC U_right  -> 334
 336                DEC R        nz-> 337  z-> 339
 337                INC A2       -> 338
 338                INC A2       -> 336
 339                DEC w        nz-> 340  z-> 341
 340                INC A2       -> 339
 341                DEC A2       nz-> 342  z-> 344
 342                INC R        -> 343
 343                INC R        -> 341
 344                INC R        -> 328
 345 step:          DEC Tb       nz-> 346  z-> 408
 346                DEC R        nz-> 347  z-> 350
 347                DEC R        nz-> 348  z-> 349
 348                INC R1       -> 346
 349 a1:            INC O        -> 350
 350                DEC P        nz-> 351  z-> 353
 351                INC Bs       -> 352
 352                INC A2       -> 350
 353                DEC A2       nz-> 354  z-> 355
 354                INC P        -> 353
 355 parse:         DEC Bs       nz-> 356  z-> 361
 356                DEC Bs       nz-> 357  z-> 358
 357                INC A2       -> 355
 358                DEC A2       nz-> 359  z-> 407
 359                INC Bs       -> 360
 360                INC w        -> 361
 361                DEC A2       nz-> 362  z-> 363
 362                INC Bs       -> 361
 363                DEC w        nz-> 364  z-> 367
 364                DEC O        nz-> 365  z-> 366
 365                INC O        -> 355
 366 bit1t:         INC A        -> 355
 367 bit0:          DEC O        nz-> 355  z-> 368
 368 decode:        DEC Bs       nz-> 368  z-> 369
 369                DEC A        nz-> 370  z-> 373
 370                DEC A        nz-> 371  z-> 372
 371                INC A2       -> 369
 372 w1:            INC w        -> 373
 373                DEC A2       nz-> 374  z-> 388
 374                DEC A2       nz-> 375  z-> 376
 375                INC A        -> 373
 376 right:         DEC A        nz-> 377  z-> 405
 377                DEC A        nz-> 378  z-> 379
 378                INC O        -> 377
 379                DEC Lt       nz-> 380  z-> 382
 380                INC U_right  -> 381
 381                INC U_right  -> 379
 382                DEC w        nz-> 383  z-> 384
 383                INC U_right  -> 382
 384                DEC U_right  nz-> 385  z-> 386
 385                INC Lt       -> 384
 386                DEC R1       nz-> 387  z-> 345
 387                INC R        -> 386
 388 left:          DEC A        nz-> 389  z-> 405
 389                DEC A        nz-> 390  z-> 391
 390                INC O        -> 389
 391                DEC Lt       nz-> 392  z-> 395
 392                DEC Lt       nz-> 393  z-> 394
 393                INC U_right  -> 391
 394 l1:            INC R        -> 395
 395                DEC U_right  nz-> 396  z-> 397
 396                INC Lt       -> 395
 397                DEC R1       nz-> 398  z-> 400
 398                INC A2       -> 399
 399                INC A2       -> 397
 400                DEC w        nz-> 401  z-> 402
 401                INC A2       -> 400
 402                DEC A2       nz-> 403  z-> 345
 403                INC R        -> 404
 404                INC R        -> 402
 405 halt:          DEC w        nz-> 406  z-> 407
 406 o_acc:         DEC A2       nz-> 409  z-> 314
 407 o_rej:         DEC A2       nz-> 409  z-> 315
 408 o_timeout:     DEC A2       nz-> 409  z-> 316
 409 never:         DEC A2       nz-> 409  z-> 409

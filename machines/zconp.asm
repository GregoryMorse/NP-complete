; entry 0
   0                INC J        -> 1
   1 cand:          INC S        -> 2
   2 inst:          DEC S        nz-> 3  z-> 6
   3                INC Pc       -> 4
   4                INC K        -> 5
   5                INC A2       -> 2
   6                DEC A2       nz-> 7  z-> 8
   7                INC S        -> 6
   8                DEC Pc       nz-> 9  z-> 13
   9                DEC Pc       nz-> 10  z-> 11
  10                INC A2       -> 8
  11                DEC A2       nz-> 12  z-> 16
  12                INC Pc       -> 13
  13                DEC A2       nz-> 14  z-> 15
  14                INC Pc       -> 13
  15                INC N        -> 8
  16 cert:          DEC K        nz-> 17  z-> 38
  17                INC C        -> 18
  18                DEC Bs       nz-> 18  z-> 19
  19                DEC Tb       nz-> 19  z-> 20
  20                DEC S        nz-> 21  z-> 23
  21                INC Bs       -> 22
  22                INC A2       -> 20
  23                DEC A2       nz-> 24  z-> 25
  24                INC S        -> 23
  25                DEC C        nz-> 26  z-> 28
  26                INC Pc       -> 27
  27                INC A2       -> 25
  28                DEC A2       nz-> 29  z-> 30
  29                INC C        -> 28
  30                DEC N        nz-> 31  z-> 33
  31                INC Tb       -> 32
  32                INC A2       -> 30
  33                DEC A2       nz-> 34  z-> 35
  34                INC N        -> 33
  35                INC F        -> 122
  36 ver_acc:       INC TR       -> 37
  37                DEC K        nz-> 37  z-> 38
  38 certdone:      DEC C        nz-> 38  z-> 39
  39                DEC J        nz-> 40  z-> 42
  40                INC Pc       -> 41
  41                INC A2       -> 39
  42                DEC A2       nz-> 43  z-> 44
  43                INC J        -> 42
  44                DEC Pc       nz-> 45  z-> 49
  45                DEC Pc       nz-> 46  z-> 47
  46                INC A2       -> 44
  47                DEC A2       nz-> 48  z-> 52
  48                INC Pc       -> 49
  49                DEC A2       nz-> 50  z-> 51
  50                INC Pc       -> 49
  51                INC C        -> 44
  52                DEC Bs       nz-> 52  z-> 53
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
  64                INC Pc       -> 63
  65 mul:           DEC Pc       nz-> 66  z-> 62
  66                DEC Bs       nz-> 67  z-> 69
  67                INC Tb       -> 68
  68                INC A2       -> 66
  69                DEC A2       nz-> 70  z-> 65
  70                INC Bs       -> 69
  71 powd:          DEC Bs       nz-> 71  z-> 72
  72                DEC J        nz-> 73  z-> 75
  73                INC Bs       -> 74
  74                INC A2       -> 72
  75                DEC A2       nz-> 76  z-> 77
  76                INC J        -> 75
  77                DEC Tb       nz-> 78  z-> 79
  78                INC Tsv      -> 77
  79                INC Yrem     -> 80
  80                DEC Tsv      nz-> 81  z-> 83
  81                INC Tb       -> 82
  82                INC A2       -> 80
  83                DEC A2       nz-> 84  z-> 85
  84                INC Tsv      -> 83
  85                DEC Tb       nz-> 86  z-> 91
  86                DEC Yrem     nz-> 87  z-> 89
  87                INC A2       -> 88
  88                INC A2       -> 86
  89                DEC A2       nz-> 90  z-> 85
  90                INC Yrem     -> 89
  91 yloop:         DEC Yrem     nz-> 92  z-> 113
  92                DEC Tb       nz-> 92  z-> 93
  93                DEC Tsv      nz-> 94  z-> 96
  94                INC Tb       -> 95
  95                INC A2       -> 93
  96                DEC A2       nz-> 97  z-> 98
  97                INC Tsv      -> 96
  98                DEC S        nz-> 99  z-> 101
  99                INC Pc       -> 100
 100                INC A2       -> 98
 101                DEC A2       nz-> 102  z-> 103
 102                INC S        -> 101
 103                DEC Y        nz-> 104  z-> 106
 104                INC A2       -> 105
 105                INC _t_Y89   -> 103
 106                DEC _t_Y89   nz-> 107  z-> 122
 107                INC Y        -> 106
 108 dec_acc:       DEC Yrem     nz-> 108  z-> 109
 109                DEC Y        nz-> 109  z-> 110
 110                DEC Tsv      nz-> 110  z-> 111
 111                DEC TR       nz-> 116  z-> 120
 112 dec_rej:       INC Y        -> 91
 113 y_none:        DEC Y        nz-> 113  z-> 114
 114                DEC Tsv      nz-> 114  z-> 115
 115                DEC TR       nz-> 120  z-> 116
 116 bad:           BEEP         -> 117
 117                INC J        -> 118
 118                DEC S        nz-> 118  z-> 119
 119                DEC N        nz-> 119  z-> 1
 120 ok:            DEC N        nz-> 120  z-> 121
 121                INC S        -> 2
 122 run:           DEC R        nz-> 122  z-> 123
 123                DEC R1       nz-> 123  z-> 124
 124                DEC Lt       nz-> 124  z-> 125
 125                DEC O        nz-> 125  z-> 126
 126                DEC A        nz-> 126  z-> 127
 127                DEC A2       nz-> 128  z-> 129
 128                INC Lt       -> 127
 129 enc:           DEC Pc       nz-> 130  z-> 135
 130                DEC Pc       nz-> 131  z-> 132
 131                INC A2       -> 129
 132                DEC A2       nz-> 133  z-> 146
 133                INC Pc       -> 134
 134                INC w        -> 135
 135                DEC A2       nz-> 136  z-> 137
 136                INC Pc       -> 135
 137                DEC R        nz-> 138  z-> 140
 138                INC A2       -> 139
 139                INC A2       -> 137
 140                DEC w        nz-> 141  z-> 142
 141                INC A2       -> 140
 142                DEC A2       nz-> 143  z-> 145
 143                INC R        -> 144
 144                INC R        -> 142
 145                INC R        -> 129
 146 step:          DEC Tb       nz-> 147  z-> 209
 147                DEC R        nz-> 148  z-> 151
 148                DEC R        nz-> 149  z-> 150
 149                INC R1       -> 147
 150 a1:            INC O        -> 151
 151                DEC Bs       nz-> 152  z-> 154
 152                INC Pc       -> 153
 153                INC A2       -> 151
 154                DEC A2       nz-> 155  z-> 156
 155                INC Bs       -> 154
 156 parse:         DEC Pc       nz-> 157  z-> 162
 157                DEC Pc       nz-> 158  z-> 159
 158                INC A2       -> 156
 159                DEC A2       nz-> 160  z-> 208
 160                INC Pc       -> 161
 161                INC w        -> 162
 162                DEC A2       nz-> 163  z-> 164
 163                INC Pc       -> 162
 164                DEC w        nz-> 165  z-> 168
 165                DEC O        nz-> 166  z-> 167
 166                INC O        -> 156
 167 bit1t:         INC A        -> 156
 168 bit0:          DEC O        nz-> 156  z-> 169
 169 decode:        DEC Pc       nz-> 169  z-> 170
 170                DEC A        nz-> 171  z-> 174
 171                DEC A        nz-> 172  z-> 173
 172                INC A2       -> 170
 173 w1:            INC w        -> 174
 174                DEC A2       nz-> 175  z-> 189
 175                DEC A2       nz-> 176  z-> 177
 176                INC A        -> 174
 177 right:         DEC A        nz-> 178  z-> 206
 178                DEC A        nz-> 179  z-> 180
 179                INC O        -> 178
 180                DEC Lt       nz-> 181  z-> 183
 181                INC A2       -> 182
 182                INC A2       -> 180
 183                DEC w        nz-> 184  z-> 185
 184                INC A2       -> 183
 185                DEC A2       nz-> 186  z-> 187
 186                INC Lt       -> 185
 187                DEC R1       nz-> 188  z-> 146
 188                INC R        -> 187
 189 left:          DEC A        nz-> 190  z-> 206
 190                DEC A        nz-> 191  z-> 192
 191                INC O        -> 190
 192                DEC Lt       nz-> 193  z-> 196
 193                DEC Lt       nz-> 194  z-> 195
 194                INC A2       -> 192
 195 l1:            INC R        -> 196
 196                DEC A2       nz-> 197  z-> 198
 197                INC Lt       -> 196
 198                DEC R1       nz-> 199  z-> 201
 199                INC A2       -> 200
 200                INC A2       -> 198
 201                DEC w        nz-> 202  z-> 203
 202                INC A2       -> 201
 203                DEC A2       nz-> 204  z-> 146
 204                INC R        -> 205
 205                INC R        -> 203
 206 halt:          DEC w        nz-> 207  z-> 208
 207 o_acc:         DEC F        nz-> 36  z-> 108
 208 o_rej:         DEC F        nz-> 16  z-> 112
 209 o_timeout:     DEC F        nz-> 16  z-> 112

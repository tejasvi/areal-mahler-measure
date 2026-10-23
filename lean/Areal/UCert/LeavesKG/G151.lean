import ArealUK.Chunk15100
import ArealUK.Chunk15101
import ArealUK.Chunk15102
import ArealUK.Chunk15103
import ArealUK.Chunk15104
import ArealUK.Chunk15105
import ArealUK.Chunk15106
import ArealUK.Chunk15107
import ArealUK.Chunk15108
import ArealUK.Chunk15109
import ArealUK.Chunk15110
import ArealUK.Chunk15111
import ArealUK.Chunk15112
import ArealUK.Chunk15113
import ArealUK.Chunk15114
import ArealUK.Chunk15115
import ArealUK.Chunk15116
import ArealUK.Chunk15117
import ArealUK.Chunk15118
import ArealUK.Chunk15119
import ArealUK.Chunk15120
import ArealUK.Chunk15121
import ArealUK.Chunk15122
import ArealUK.Chunk15123
import ArealUK.Chunk15124
import ArealUK.Chunk15125
import ArealUK.Chunk15126
import ArealUK.Chunk15127
import ArealUK.Chunk15128
import ArealUK.Chunk15129
import ArealUK.Chunk15130
import ArealUK.Chunk15131
import ArealUK.Chunk15132
import ArealUK.Chunk15133
import ArealUK.Chunk15134
import ArealUK.Chunk15135
import ArealUK.Chunk15136
import ArealUK.Chunk15137
import ArealUK.Chunk15138
import ArealUK.Chunk15139
import ArealUK.Chunk15140
import ArealUK.Chunk15141
import ArealUK.Chunk15142
import ArealUK.Chunk15143
import ArealUK.Chunk15144
import ArealUK.Chunk15145
import ArealUK.Chunk15146
import ArealUK.Chunk15147
import ArealUK.Chunk15148
import ArealUK.Chunk15149
import ArealUK.Chunk15150
import ArealUK.Chunk15151
import ArealUK.Chunk15152
import ArealUK.Chunk15153
import ArealUK.Chunk15154
import ArealUK.Chunk15155
import ArealUK.Chunk15156
import ArealUK.Chunk15157
import ArealUK.Chunk15158
import ArealUK.Chunk15159
import ArealUK.Chunk15160
import ArealUK.Chunk15161
import ArealUK.Chunk15162
import ArealUK.Chunk15163
import ArealUK.Chunk15164
import ArealUK.Chunk15165
import ArealUK.Chunk15166
import ArealUK.Chunk15167
import ArealUK.Chunk15168
import ArealUK.Chunk15169
import ArealUK.Chunk15170
import ArealUK.Chunk15171
import ArealUK.Chunk15172
import ArealUK.Chunk15173
import ArealUK.Chunk15174
import ArealUK.Chunk15175
import ArealUK.Chunk15176
import ArealUK.Chunk15177
import ArealUK.Chunk15178
import ArealUK.Chunk15179
import ArealUK.Chunk15180
import ArealUK.Chunk15181
import ArealUK.Chunk15182
import ArealUK.Chunk15183
import ArealUK.Chunk15184
import ArealUK.Chunk15185
import ArealUK.Chunk15186
import ArealUK.Chunk15187
import ArealUK.Chunk15188
import ArealUK.Chunk15189
import ArealUK.Chunk15190
import ArealUK.Chunk15191
import ArealUK.Chunk15192
import ArealUK.Chunk15193
import ArealUK.Chunk15194
import ArealUK.Chunk15195
import ArealUK.Chunk15196
import ArealUK.Chunk15197
import ArealUK.Chunk15198
import ArealUK.Chunk15199
import Areal.UCert.LeavesKGen

/-! Group 151 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_151 : leavesOK ctxLitU 157818750000 0 ((leaves.drop 30200).take 200) 159218750000 0 = true := by
  have s99 := ArealUCore.ArealUK.chunk_15199
  have s98 : leavesOK ctxLitU 318387500000 1 ((leaves.drop 30396).take 4) 159218750000 0 = true :=
    take_step (n := 2) (t := 4) (b := 30398) rfl rfl ArealUCore.ArealUK.chunk_15198 s99
  have s97 : leavesOK ctxLitU 318362500000 1 ((leaves.drop 30394).take 6) 159218750000 0 = true :=
    take_step (n := 2) (t := 6) (b := 30396) rfl rfl ArealUCore.ArealUK.chunk_15197 s98
  have s96 : leavesOK ctxLitU 159168750000 0 ((leaves.drop 30392).take 8) 159218750000 0 = true :=
    take_step (n := 2) (t := 8) (b := 30394) rfl rfl ArealUCore.ArealUK.chunk_15196 s97
  have s95 : leavesOK ctxLitU 159156250000 0 ((leaves.drop 30390).take 10) 159218750000 0 = true :=
    take_step (n := 2) (t := 10) (b := 30392) rfl rfl ArealUCore.ArealUK.chunk_15195 s96
  have s94 : leavesOK ctxLitU 159143750000 0 ((leaves.drop 30388).take 12) 159218750000 0 = true :=
    take_step (n := 2) (t := 12) (b := 30390) rfl rfl ArealUCore.ArealUK.chunk_15194 s95
  have s93 : leavesOK ctxLitU 159131250000 0 ((leaves.drop 30386).take 14) 159218750000 0 = true :=
    take_step (n := 2) (t := 14) (b := 30388) rfl rfl ArealUCore.ArealUK.chunk_15193 s94
  have s92 : leavesOK ctxLitU 318237500000 1 ((leaves.drop 30384).take 16) 159218750000 0 = true :=
    take_step (n := 2) (t := 16) (b := 30386) rfl rfl ArealUCore.ArealUK.chunk_15192 s93
  have s91 : leavesOK ctxLitU 318212500000 1 ((leaves.drop 30382).take 18) 159218750000 0 = true :=
    take_step (n := 2) (t := 18) (b := 30384) rfl rfl ArealUCore.ArealUK.chunk_15191 s92
  have s90 : leavesOK ctxLitU 318187500000 1 ((leaves.drop 30380).take 20) 159218750000 0 = true :=
    take_step (n := 2) (t := 20) (b := 30382) rfl rfl ArealUCore.ArealUK.chunk_15190 s91
  have s89 : leavesOK ctxLitU 318162500000 1 ((leaves.drop 30378).take 22) 159218750000 0 = true :=
    take_step (n := 2) (t := 22) (b := 30380) rfl rfl ArealUCore.ArealUK.chunk_15189 s90
  have s88 : leavesOK ctxLitU 159068750000 0 ((leaves.drop 30376).take 24) 159218750000 0 = true :=
    take_step (n := 2) (t := 24) (b := 30378) rfl rfl ArealUCore.ArealUK.chunk_15188 s89
  have s87 : leavesOK ctxLitU 159056250000 0 ((leaves.drop 30374).take 26) 159218750000 0 = true :=
    take_step (n := 2) (t := 26) (b := 30376) rfl rfl ArealUCore.ArealUK.chunk_15187 s88
  have s86 : leavesOK ctxLitU 159043750000 0 ((leaves.drop 30372).take 28) 159218750000 0 = true :=
    take_step (n := 2) (t := 28) (b := 30374) rfl rfl ArealUCore.ArealUK.chunk_15186 s87
  have s85 : leavesOK ctxLitU 159031250000 0 ((leaves.drop 30370).take 30) 159218750000 0 = true :=
    take_step (n := 2) (t := 30) (b := 30372) rfl rfl ArealUCore.ArealUK.chunk_15185 s86
  have s84 : leavesOK ctxLitU 318037500000 1 ((leaves.drop 30368).take 32) 159218750000 0 = true :=
    take_step (n := 2) (t := 32) (b := 30370) rfl rfl ArealUCore.ArealUK.chunk_15184 s85
  have s83 : leavesOK ctxLitU 318012500000 1 ((leaves.drop 30366).take 34) 159218750000 0 = true :=
    take_step (n := 2) (t := 34) (b := 30368) rfl rfl ArealUCore.ArealUK.chunk_15183 s84
  have s82 : leavesOK ctxLitU 158987500000 0 ((leaves.drop 30364).take 36) 159218750000 0 = true :=
    take_step (n := 2) (t := 36) (b := 30366) rfl rfl ArealUCore.ArealUK.chunk_15182 s83
  have s81 : leavesOK ctxLitU 158968750000 0 ((leaves.drop 30362).take 38) 159218750000 0 = true :=
    take_step (n := 2) (t := 38) (b := 30364) rfl rfl ArealUCore.ArealUK.chunk_15181 s82
  have s80 : leavesOK ctxLitU 158956250000 0 ((leaves.drop 30360).take 40) 159218750000 0 = true :=
    take_step (n := 2) (t := 40) (b := 30362) rfl rfl ArealUCore.ArealUK.chunk_15180 s81
  have s79 : leavesOK ctxLitU 158943750000 0 ((leaves.drop 30358).take 42) 159218750000 0 = true :=
    take_step (n := 2) (t := 42) (b := 30360) rfl rfl ArealUCore.ArealUK.chunk_15179 s80
  have s78 : leavesOK ctxLitU 158931250000 0 ((leaves.drop 30356).take 44) 159218750000 0 = true :=
    take_step (n := 2) (t := 44) (b := 30358) rfl rfl ArealUCore.ArealUK.chunk_15178 s79
  have s77 : leavesOK ctxLitU 317837500000 1 ((leaves.drop 30354).take 46) 159218750000 0 = true :=
    take_step (n := 2) (t := 46) (b := 30356) rfl rfl ArealUCore.ArealUK.chunk_15177 s78
  have s76 : leavesOK ctxLitU 317812500000 1 ((leaves.drop 30352).take 48) 159218750000 0 = true :=
    take_step (n := 2) (t := 48) (b := 30354) rfl rfl ArealUCore.ArealUK.chunk_15176 s77
  have s75 : leavesOK ctxLitU 158887500000 0 ((leaves.drop 30350).take 50) 159218750000 0 = true :=
    take_step (n := 2) (t := 50) (b := 30352) rfl rfl ArealUCore.ArealUK.chunk_15175 s76
  have s74 : leavesOK ctxLitU 158868750000 0 ((leaves.drop 30348).take 52) 159218750000 0 = true :=
    take_step (n := 2) (t := 52) (b := 30350) rfl rfl ArealUCore.ArealUK.chunk_15174 s75
  have s73 : leavesOK ctxLitU 158856250000 0 ((leaves.drop 30346).take 54) 159218750000 0 = true :=
    take_step (n := 2) (t := 54) (b := 30348) rfl rfl ArealUCore.ArealUK.chunk_15173 s74
  have s72 : leavesOK ctxLitU 158843750000 0 ((leaves.drop 30344).take 56) 159218750000 0 = true :=
    take_step (n := 2) (t := 56) (b := 30346) rfl rfl ArealUCore.ArealUK.chunk_15172 s73
  have s71 : leavesOK ctxLitU 158831250000 0 ((leaves.drop 30342).take 58) 159218750000 0 = true :=
    take_step (n := 2) (t := 58) (b := 30344) rfl rfl ArealUCore.ArealUK.chunk_15171 s72
  have s70 : leavesOK ctxLitU 158812500000 0 ((leaves.drop 30340).take 60) 159218750000 0 = true :=
    take_step (n := 2) (t := 60) (b := 30342) rfl rfl ArealUCore.ArealUK.chunk_15170 s71
  have s69 : leavesOK ctxLitU 158787500000 0 ((leaves.drop 30338).take 62) 159218750000 0 = true :=
    take_step (n := 2) (t := 62) (b := 30340) rfl rfl ArealUCore.ArealUK.chunk_15169 s70
  have s68 : leavesOK ctxLitU 158768750000 0 ((leaves.drop 30336).take 64) 159218750000 0 = true :=
    take_step (n := 2) (t := 64) (b := 30338) rfl rfl ArealUCore.ArealUK.chunk_15168 s69
  have s67 : leavesOK ctxLitU 158756250000 0 ((leaves.drop 30334).take 66) 159218750000 0 = true :=
    take_step (n := 2) (t := 66) (b := 30336) rfl rfl ArealUCore.ArealUK.chunk_15167 s68
  have s66 : leavesOK ctxLitU 158743750000 0 ((leaves.drop 30332).take 68) 159218750000 0 = true :=
    take_step (n := 2) (t := 68) (b := 30334) rfl rfl ArealUCore.ArealUK.chunk_15166 s67
  have s65 : leavesOK ctxLitU 158731250000 0 ((leaves.drop 30330).take 70) 159218750000 0 = true :=
    take_step (n := 2) (t := 70) (b := 30332) rfl rfl ArealUCore.ArealUK.chunk_15165 s66
  have s64 : leavesOK ctxLitU 158712500000 0 ((leaves.drop 30328).take 72) 159218750000 0 = true :=
    take_step (n := 2) (t := 72) (b := 30330) rfl rfl ArealUCore.ArealUK.chunk_15164 s65
  have s63 : leavesOK ctxLitU 317387500000 1 ((leaves.drop 30326).take 74) 159218750000 0 = true :=
    take_step (n := 2) (t := 74) (b := 30328) rfl rfl ArealUCore.ArealUK.chunk_15163 s64
  have s62 : leavesOK ctxLitU 317362500000 1 ((leaves.drop 30324).take 76) 159218750000 0 = true :=
    take_step (n := 2) (t := 76) (b := 30326) rfl rfl ArealUCore.ArealUK.chunk_15162 s63
  have s61 : leavesOK ctxLitU 158668750000 0 ((leaves.drop 30322).take 78) 159218750000 0 = true :=
    take_step (n := 2) (t := 78) (b := 30324) rfl rfl ArealUCore.ArealUK.chunk_15161 s62
  have s60 : leavesOK ctxLitU 158656250000 0 ((leaves.drop 30320).take 80) 159218750000 0 = true :=
    take_step (n := 2) (t := 80) (b := 30322) rfl rfl ArealUCore.ArealUK.chunk_15160 s61
  have s59 : leavesOK ctxLitU 158643750000 0 ((leaves.drop 30318).take 82) 159218750000 0 = true :=
    take_step (n := 2) (t := 82) (b := 30320) rfl rfl ArealUCore.ArealUK.chunk_15159 s60
  have s58 : leavesOK ctxLitU 158631250000 0 ((leaves.drop 30316).take 84) 159218750000 0 = true :=
    take_step (n := 2) (t := 84) (b := 30318) rfl rfl ArealUCore.ArealUK.chunk_15158 s59
  have s57 : leavesOK ctxLitU 158612500000 0 ((leaves.drop 30314).take 86) 159218750000 0 = true :=
    take_step (n := 2) (t := 86) (b := 30316) rfl rfl ArealUCore.ArealUK.chunk_15157 s58
  have s56 : leavesOK ctxLitU 158587500000 0 ((leaves.drop 30312).take 88) 159218750000 0 = true :=
    take_step (n := 2) (t := 88) (b := 30314) rfl rfl ArealUCore.ArealUK.chunk_15156 s57
  have s55 : leavesOK ctxLitU 317150000000 1 ((leaves.drop 30310).take 90) 159218750000 0 = true :=
    take_step (n := 2) (t := 90) (b := 30312) rfl rfl ArealUCore.ArealUK.chunk_15155 s56
  have s54 : leavesOK ctxLitU 158562500000 0 ((leaves.drop 30308).take 92) 159218750000 0 = true :=
    take_step (n := 2) (t := 92) (b := 30310) rfl rfl ArealUCore.ArealUK.chunk_15154 s55
  have s53 : leavesOK ctxLitU 158550000000 0 ((leaves.drop 30306).take 94) 159218750000 0 = true :=
    take_step (n := 2) (t := 94) (b := 30308) rfl rfl ArealUCore.ArealUK.chunk_15153 s54
  have s52 : leavesOK ctxLitU 158537500000 0 ((leaves.drop 30304).take 96) 159218750000 0 = true :=
    take_step (n := 2) (t := 96) (b := 30306) rfl rfl ArealUCore.ArealUK.chunk_15152 s53
  have s51 : leavesOK ctxLitU 158525000000 0 ((leaves.drop 30302).take 98) 159218750000 0 = true :=
    take_step (n := 2) (t := 98) (b := 30304) rfl rfl ArealUCore.ArealUK.chunk_15151 s52
  have s50 : leavesOK ctxLitU 158500000000 0 ((leaves.drop 30300).take 100) 159218750000 0 = true :=
    take_step (n := 2) (t := 100) (b := 30302) rfl rfl ArealUCore.ArealUK.chunk_15150 s51
  have s49 : leavesOK ctxLitU 316975000000 1 ((leaves.drop 30298).take 102) 159218750000 0 = true :=
    take_step (n := 2) (t := 102) (b := 30300) rfl rfl ArealUCore.ArealUK.chunk_15149 s50
  have s48 : leavesOK ctxLitU 316950000000 1 ((leaves.drop 30296).take 104) 159218750000 0 = true :=
    take_step (n := 2) (t := 104) (b := 30298) rfl rfl ArealUCore.ArealUK.chunk_15148 s49
  have s47 : leavesOK ctxLitU 158462500000 0 ((leaves.drop 30294).take 106) 159218750000 0 = true :=
    take_step (n := 2) (t := 106) (b := 30296) rfl rfl ArealUCore.ArealUK.chunk_15147 s48
  have s46 : leavesOK ctxLitU 158450000000 0 ((leaves.drop 30292).take 108) 159218750000 0 = true :=
    take_step (n := 2) (t := 108) (b := 30294) rfl rfl ArealUCore.ArealUK.chunk_15146 s47
  have s45 : leavesOK ctxLitU 158437500000 0 ((leaves.drop 30290).take 110) 159218750000 0 = true :=
    take_step (n := 2) (t := 110) (b := 30292) rfl rfl ArealUCore.ArealUK.chunk_15145 s46
  have s44 : leavesOK ctxLitU 158425000000 0 ((leaves.drop 30288).take 112) 159218750000 0 = true :=
    take_step (n := 2) (t := 112) (b := 30290) rfl rfl ArealUCore.ArealUK.chunk_15144 s45
  have s43 : leavesOK ctxLitU 158412500000 0 ((leaves.drop 30286).take 114) 159218750000 0 = true :=
    take_step (n := 2) (t := 114) (b := 30288) rfl rfl ArealUCore.ArealUK.chunk_15143 s44
  have s42 : leavesOK ctxLitU 158400000000 0 ((leaves.drop 30284).take 116) 159218750000 0 = true :=
    take_step (n := 2) (t := 116) (b := 30286) rfl rfl ArealUCore.ArealUK.chunk_15142 s43
  have s41 : leavesOK ctxLitU 158387500000 0 ((leaves.drop 30282).take 118) 159218750000 0 = true :=
    take_step (n := 2) (t := 118) (b := 30284) rfl rfl ArealUCore.ArealUK.chunk_15141 s42
  have s40 : leavesOK ctxLitU 158375000000 0 ((leaves.drop 30280).take 120) 159218750000 0 = true :=
    take_step (n := 2) (t := 120) (b := 30282) rfl rfl ArealUCore.ArealUK.chunk_15140 s41
  have s39 : leavesOK ctxLitU 158362500000 0 ((leaves.drop 30278).take 122) 159218750000 0 = true :=
    take_step (n := 2) (t := 122) (b := 30280) rfl rfl ArealUCore.ArealUK.chunk_15139 s40
  have s38 : leavesOK ctxLitU 158350000000 0 ((leaves.drop 30276).take 124) 159218750000 0 = true :=
    take_step (n := 2) (t := 124) (b := 30278) rfl rfl ArealUCore.ArealUK.chunk_15138 s39
  have s37 : leavesOK ctxLitU 158337500000 0 ((leaves.drop 30274).take 126) 159218750000 0 = true :=
    take_step (n := 2) (t := 126) (b := 30276) rfl rfl ArealUCore.ArealUK.chunk_15137 s38
  have s36 : leavesOK ctxLitU 158325000000 0 ((leaves.drop 30272).take 128) 159218750000 0 = true :=
    take_step (n := 2) (t := 128) (b := 30274) rfl rfl ArealUCore.ArealUK.chunk_15136 s37
  have s35 : leavesOK ctxLitU 316625000000 1 ((leaves.drop 30270).take 130) 159218750000 0 = true :=
    take_step (n := 2) (t := 130) (b := 30272) rfl rfl ArealUCore.ArealUK.chunk_15135 s36
  have s34 : leavesOK ctxLitU 316600000000 1 ((leaves.drop 30268).take 132) 159218750000 0 = true :=
    take_step (n := 2) (t := 132) (b := 30270) rfl rfl ArealUCore.ArealUK.chunk_15134 s35
  have s33 : leavesOK ctxLitU 158275000000 0 ((leaves.drop 30266).take 134) 159218750000 0 = true :=
    take_step (n := 2) (t := 134) (b := 30268) rfl rfl ArealUCore.ArealUK.chunk_15133 s34
  have s32 : leavesOK ctxLitU 158262500000 0 ((leaves.drop 30264).take 136) 159218750000 0 = true :=
    take_step (n := 2) (t := 136) (b := 30266) rfl rfl ArealUCore.ArealUK.chunk_15132 s33
  have s31 : leavesOK ctxLitU 158250000000 0 ((leaves.drop 30262).take 138) 159218750000 0 = true :=
    take_step (n := 2) (t := 138) (b := 30264) rfl rfl ArealUCore.ArealUK.chunk_15131 s32
  have s30 : leavesOK ctxLitU 158237500000 0 ((leaves.drop 30260).take 140) 159218750000 0 = true :=
    take_step (n := 2) (t := 140) (b := 30262) rfl rfl ArealUCore.ArealUK.chunk_15130 s31
  have s29 : leavesOK ctxLitU 158225000000 0 ((leaves.drop 30258).take 142) 159218750000 0 = true :=
    take_step (n := 2) (t := 142) (b := 30260) rfl rfl ArealUCore.ArealUK.chunk_15129 s30
  have s28 : leavesOK ctxLitU 316425000000 1 ((leaves.drop 30256).take 144) 159218750000 0 = true :=
    take_step (n := 2) (t := 144) (b := 30258) rfl rfl ArealUCore.ArealUK.chunk_15128 s29
  have s27 : leavesOK ctxLitU 158187500000 0 ((leaves.drop 30254).take 146) 159218750000 0 = true :=
    take_step (n := 2) (t := 146) (b := 30256) rfl rfl ArealUCore.ArealUK.chunk_15127 s28
  have s26 : leavesOK ctxLitU 316350000000 1 ((leaves.drop 30252).take 148) 159218750000 0 = true :=
    take_step (n := 2) (t := 148) (b := 30254) rfl rfl ArealUCore.ArealUK.chunk_15126 s27
  have s25 : leavesOK ctxLitU 158162500000 0 ((leaves.drop 30250).take 150) 159218750000 0 = true :=
    take_step (n := 2) (t := 150) (b := 30252) rfl rfl ArealUCore.ArealUK.chunk_15125 s26
  have s24 : leavesOK ctxLitU 158150000000 0 ((leaves.drop 30248).take 152) 159218750000 0 = true :=
    take_step (n := 2) (t := 152) (b := 30250) rfl rfl ArealUCore.ArealUK.chunk_15124 s25
  have s23 : leavesOK ctxLitU 158137500000 0 ((leaves.drop 30246).take 154) 159218750000 0 = true :=
    take_step (n := 2) (t := 154) (b := 30248) rfl rfl ArealUCore.ArealUK.chunk_15123 s24
  have s22 : leavesOK ctxLitU 158125000000 0 ((leaves.drop 30244).take 156) 159218750000 0 = true :=
    take_step (n := 2) (t := 156) (b := 30246) rfl rfl ArealUCore.ArealUK.chunk_15122 s23
  have s21 : leavesOK ctxLitU 316212500000 1 ((leaves.drop 30242).take 158) 159218750000 0 = true :=
    take_step (n := 2) (t := 158) (b := 30244) rfl rfl ArealUCore.ArealUK.chunk_15121 s22
  have s20 : leavesOK ctxLitU 316187500000 1 ((leaves.drop 30240).take 160) 159218750000 0 = true :=
    take_step (n := 2) (t := 160) (b := 30242) rfl rfl ArealUCore.ArealUK.chunk_15120 s21
  have s19 : leavesOK ctxLitU 316162500000 1 ((leaves.drop 30238).take 162) 159218750000 0 = true :=
    take_step (n := 2) (t := 162) (b := 30240) rfl rfl ArealUCore.ArealUK.chunk_15119 s20
  have s18 : leavesOK ctxLitU 158068750000 0 ((leaves.drop 30236).take 164) 159218750000 0 = true :=
    take_step (n := 2) (t := 164) (b := 30238) rfl rfl ArealUCore.ArealUK.chunk_15118 s19
  have s17 : leavesOK ctxLitU 158056250000 0 ((leaves.drop 30234).take 166) 159218750000 0 = true :=
    take_step (n := 2) (t := 166) (b := 30236) rfl rfl ArealUCore.ArealUK.chunk_15117 s18
  have s16 : leavesOK ctxLitU 158043750000 0 ((leaves.drop 30232).take 168) 159218750000 0 = true :=
    take_step (n := 2) (t := 168) (b := 30234) rfl rfl ArealUCore.ArealUK.chunk_15116 s17
  have s15 : leavesOK ctxLitU 158031250000 0 ((leaves.drop 30230).take 170) 159218750000 0 = true :=
    take_step (n := 2) (t := 170) (b := 30232) rfl rfl ArealUCore.ArealUK.chunk_15115 s16
  have s14 : leavesOK ctxLitU 316037500000 1 ((leaves.drop 30228).take 172) 159218750000 0 = true :=
    take_step (n := 2) (t := 172) (b := 30230) rfl rfl ArealUCore.ArealUK.chunk_15114 s15
  have s13 : leavesOK ctxLitU 158000000000 0 ((leaves.drop 30226).take 174) 159218750000 0 = true :=
    take_step (n := 2) (t := 174) (b := 30228) rfl rfl ArealUCore.ArealUK.chunk_15113 s14
  have s12 : leavesOK ctxLitU 315962500000 1 ((leaves.drop 30224).take 176) 159218750000 0 = true :=
    take_step (n := 2) (t := 176) (b := 30226) rfl rfl ArealUCore.ArealUK.chunk_15112 s13
  have s11 : leavesOK ctxLitU 157968750000 0 ((leaves.drop 30222).take 178) 159218750000 0 = true :=
    take_step (n := 2) (t := 178) (b := 30224) rfl rfl ArealUCore.ArealUK.chunk_15111 s12
  have s10 : leavesOK ctxLitU 157956250000 0 ((leaves.drop 30220).take 180) 159218750000 0 = true :=
    take_step (n := 2) (t := 180) (b := 30222) rfl rfl ArealUCore.ArealUK.chunk_15110 s11
  have s9 : leavesOK ctxLitU 157943750000 0 ((leaves.drop 30218).take 182) 159218750000 0 = true :=
    take_step (n := 2) (t := 182) (b := 30220) rfl rfl ArealUCore.ArealUK.chunk_15109 s10
  have s8 : leavesOK ctxLitU 157931250000 0 ((leaves.drop 30216).take 184) 159218750000 0 = true :=
    take_step (n := 2) (t := 184) (b := 30218) rfl rfl ArealUCore.ArealUK.chunk_15108 s9
  have s7 : leavesOK ctxLitU 157912500000 0 ((leaves.drop 30214).take 186) 159218750000 0 = true :=
    take_step (n := 2) (t := 186) (b := 30216) rfl rfl ArealUCore.ArealUK.chunk_15107 s8
  have s6 : leavesOK ctxLitU 315787500000 1 ((leaves.drop 30212).take 188) 159218750000 0 = true :=
    take_step (n := 2) (t := 188) (b := 30214) rfl rfl ArealUCore.ArealUK.chunk_15106 s7
  have s5 : leavesOK ctxLitU 315762500000 1 ((leaves.drop 30210).take 190) 159218750000 0 = true :=
    take_step (n := 2) (t := 190) (b := 30212) rfl rfl ArealUCore.ArealUK.chunk_15105 s6
  have s4 : leavesOK ctxLitU 157868750000 0 ((leaves.drop 30208).take 192) 159218750000 0 = true :=
    take_step (n := 2) (t := 192) (b := 30210) rfl rfl ArealUCore.ArealUK.chunk_15104 s5
  have s3 : leavesOK ctxLitU 157856250000 0 ((leaves.drop 30206).take 194) 159218750000 0 = true :=
    take_step (n := 2) (t := 194) (b := 30208) rfl rfl ArealUCore.ArealUK.chunk_15103 s4
  have s2 : leavesOK ctxLitU 157843750000 0 ((leaves.drop 30204).take 196) 159218750000 0 = true :=
    take_step (n := 2) (t := 196) (b := 30206) rfl rfl ArealUCore.ArealUK.chunk_15102 s3
  have s1 : leavesOK ctxLitU 157831250000 0 ((leaves.drop 30202).take 198) 159218750000 0 = true :=
    take_step (n := 2) (t := 198) (b := 30204) rfl rfl ArealUCore.ArealUK.chunk_15101 s2
  have s0 : leavesOK ctxLitU 157818750000 0 ((leaves.drop 30200).take 200) 159218750000 0 = true :=
    take_step (n := 2) (t := 200) (b := 30202) rfl rfl ArealUCore.ArealUK.chunk_15100 s1
  exact s0

end Areal.UCert

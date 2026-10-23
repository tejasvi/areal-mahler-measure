import ArealUK.Chunk0100
import ArealUK.Chunk0101
import ArealUK.Chunk0102
import ArealUK.Chunk0103
import ArealUK.Chunk0104
import ArealUK.Chunk0105
import ArealUK.Chunk0106
import ArealUK.Chunk0107
import ArealUK.Chunk0108
import ArealUK.Chunk0109
import ArealUK.Chunk0110
import ArealUK.Chunk0111
import ArealUK.Chunk0112
import ArealUK.Chunk0113
import ArealUK.Chunk0114
import ArealUK.Chunk0115
import ArealUK.Chunk0116
import ArealUK.Chunk0117
import ArealUK.Chunk0118
import ArealUK.Chunk0119
import ArealUK.Chunk0120
import ArealUK.Chunk0121
import ArealUK.Chunk0122
import ArealUK.Chunk0123
import ArealUK.Chunk0124
import ArealUK.Chunk0125
import ArealUK.Chunk0126
import ArealUK.Chunk0127
import ArealUK.Chunk0128
import ArealUK.Chunk0129
import ArealUK.Chunk0130
import ArealUK.Chunk0131
import ArealUK.Chunk0132
import ArealUK.Chunk0133
import ArealUK.Chunk0134
import ArealUK.Chunk0135
import ArealUK.Chunk0136
import ArealUK.Chunk0137
import ArealUK.Chunk0138
import ArealUK.Chunk0139
import ArealUK.Chunk0140
import ArealUK.Chunk0141
import ArealUK.Chunk0142
import ArealUK.Chunk0143
import ArealUK.Chunk0144
import ArealUK.Chunk0145
import ArealUK.Chunk0146
import ArealUK.Chunk0147
import ArealUK.Chunk0148
import ArealUK.Chunk0149
import ArealUK.Chunk0150
import ArealUK.Chunk0151
import ArealUK.Chunk0152
import ArealUK.Chunk0153
import ArealUK.Chunk0154
import ArealUK.Chunk0155
import ArealUK.Chunk0156
import ArealUK.Chunk0157
import ArealUK.Chunk0158
import ArealUK.Chunk0159
import ArealUK.Chunk0160
import ArealUK.Chunk0161
import ArealUK.Chunk0162
import ArealUK.Chunk0163
import ArealUK.Chunk0164
import ArealUK.Chunk0165
import ArealUK.Chunk0166
import ArealUK.Chunk0167
import ArealUK.Chunk0168
import ArealUK.Chunk0169
import ArealUK.Chunk0170
import ArealUK.Chunk0171
import ArealUK.Chunk0172
import ArealUK.Chunk0173
import ArealUK.Chunk0174
import ArealUK.Chunk0175
import ArealUK.Chunk0176
import ArealUK.Chunk0177
import ArealUK.Chunk0178
import ArealUK.Chunk0179
import ArealUK.Chunk0180
import ArealUK.Chunk0181
import ArealUK.Chunk0182
import ArealUK.Chunk0183
import ArealUK.Chunk0184
import ArealUK.Chunk0185
import ArealUK.Chunk0186
import ArealUK.Chunk0187
import ArealUK.Chunk0188
import ArealUK.Chunk0189
import ArealUK.Chunk0190
import ArealUK.Chunk0191
import ArealUK.Chunk0192
import ArealUK.Chunk0193
import ArealUK.Chunk0194
import ArealUK.Chunk0195
import ArealUK.Chunk0196
import ArealUK.Chunk0197
import ArealUK.Chunk0198
import ArealUK.Chunk0199
import Areal.UCert.LeavesKGen

/-! Group 1 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_01 : leavesOK ctxLitU 29075000000 4 ((leaves.drop 200).take 200) 32175000000 4 = true := by
  have s99 := ArealUCore.ArealUK.chunk_0199
  have s98 : leavesOK ctxLitU 16025000000 3 ((leaves.drop 396).take 4) 32175000000 4 = true :=
    take_step (n := 2) (t := 4) (b := 398) rfl rfl ArealUCore.ArealUK.chunk_0198 s99
  have s97 : leavesOK ctxLitU 32000000000 4 ((leaves.drop 394).take 6) 32175000000 4 = true :=
    take_step (n := 2) (t := 6) (b := 396) rfl rfl ArealUCore.ArealUK.chunk_0197 s98
  have s96 : leavesOK ctxLitU 65452679898232 15 ((leaves.drop 392).take 8) 32175000000 4 = true :=
    take_step (n := 2) (t := 8) (b := 394) rfl rfl ArealUCore.ArealUK.chunk_0196 s97
  have s95 : leavesOK ctxLitU 261727399491160 17 ((leaves.drop 390).take 10) 32175000000 4 = true :=
    take_step (n := 2) (t := 10) (b := 392) rfl rfl ArealUCore.ArealUK.chunk_0195 s96
  have s94 : leavesOK ctxLitU 65369359796464 15 ((leaves.drop 388).take 12) 32175000000 4 = true :=
    take_step (n := 2) (t := 12) (b := 390) rfl rfl ArealUCore.ArealUK.chunk_0194 s95
  have s93 : leavesOK ctxLitU 32601359796464 14 ((leaves.drop 386).take 14) 32175000000 4 = true :=
    take_step (n := 2) (t := 14) (b := 388) rfl rfl ArealUCore.ArealUK.chunk_0193 s94
  have s92 : leavesOK ctxLitU 8140800000000 12 ((leaves.drop 384).take 16) 32175000000 4 = true :=
    take_step (n := 2) (t := 16) (b := 386) rfl rfl ArealUCore.ArealUK.chunk_0192 s93
  have s91 : leavesOK ctxLitU 8130627522626 12 ((leaves.drop 382).take 18) 32175000000 4 = true :=
    take_step (n := 2) (t := 18) (b := 384) rfl rfl ArealUCore.ArealUK.chunk_0191 s92
  have s90 : leavesOK ctxLitU 32440455045252 14 ((leaves.drop 380).take 20) 32175000000 4 = true :=
    take_step (n := 2) (t := 20) (b := 382) rfl rfl ArealUCore.ArealUK.chunk_0190 s91
  have s89 : leavesOK ctxLitU 259400557794138 17 ((leaves.drop 378).take 22) 32175000000 4 = true :=
    take_step (n := 2) (t := 22) (b := 380) rfl rfl ArealUCore.ArealUK.chunk_0189 s90
  have s88 : leavesOK ctxLitU 64798855045252 15 ((leaves.drop 376).take 24) 32175000000 4 = true :=
    take_step (n := 2) (t := 24) (b := 378) rfl rfl ArealUCore.ArealUK.chunk_0188 s89
  have s87 : leavesOK ctxLitU 3943750000 1 ((leaves.drop 374).take 26) 32175000000 4 = true :=
    take_step (n := 2) (t := 26) (b := 376) rfl rfl ArealUCore.ArealUK.chunk_0187 s88
  have s86 : leavesOK ctxLitU 7875000000 2 ((leaves.drop 372).take 28) 32175000000 4 = true :=
    take_step (n := 2) (t := 28) (b := 374) rfl rfl ArealUCore.ArealUK.chunk_0186 s87
  have s85 : leavesOK ctxLitU 31487500000 4 ((leaves.drop 370).take 30) 32175000000 4 = true :=
    take_step (n := 2) (t := 30) (b := 372) rfl rfl ArealUCore.ArealUK.chunk_0185 s86
  have s84 : leavesOK ctxLitU 15731250000 3 ((leaves.drop 368).take 32) 32175000000 4 = true :=
    take_step (n := 2) (t := 32) (b := 370) rfl rfl ArealUCore.ArealUK.chunk_0184 s85
  have s83 : leavesOK ctxLitU 31450000000 4 ((leaves.drop 366).take 34) 32175000000 4 = true :=
    take_step (n := 2) (t := 34) (b := 368) rfl rfl ArealUCore.ArealUK.chunk_0183 s84
  have s82 : leavesOK ctxLitU 15712500000 3 ((leaves.drop 364).take 36) 32175000000 4 = true :=
    take_step (n := 2) (t := 36) (b := 366) rfl rfl ArealUCore.ArealUK.chunk_0182 s83
  have s81 : leavesOK ctxLitU 15700000000 3 ((leaves.drop 362).take 38) 32175000000 4 = true :=
    take_step (n := 2) (t := 38) (b := 364) rfl rfl ArealUCore.ArealUK.chunk_0181 s82
  have s80 : leavesOK ctxLitU 15687500000 3 ((leaves.drop 360).take 40) 32175000000 4 = true :=
    take_step (n := 2) (t := 40) (b := 362) rfl rfl ArealUCore.ArealUK.chunk_0180 s81
  have s79 : leavesOK ctxLitU 15675000000 3 ((leaves.drop 358).take 42) 32175000000 4 = true :=
    take_step (n := 2) (t := 42) (b := 360) rfl rfl ArealUCore.ArealUK.chunk_0179 s80
  have s78 : leavesOK ctxLitU 15662500000 3 ((leaves.drop 356).take 44) 32175000000 4 = true :=
    take_step (n := 2) (t := 44) (b := 358) rfl rfl ArealUCore.ArealUK.chunk_0178 s79
  have s77 : leavesOK ctxLitU 31306250000 4 ((leaves.drop 354).take 46) 32175000000 4 = true :=
    take_step (n := 2) (t := 46) (b := 356) rfl rfl ArealUCore.ArealUK.chunk_0177 s78
  have s76 : leavesOK ctxLitU 31293750000 4 ((leaves.drop 352).take 48) 32175000000 4 = true :=
    take_step (n := 2) (t := 48) (b := 354) rfl rfl ArealUCore.ArealUK.chunk_0176 s77
  have s75 : leavesOK ctxLitU 31281250000 4 ((leaves.drop 350).take 50) 32175000000 4 = true :=
    take_step (n := 2) (t := 50) (b := 352) rfl rfl ArealUCore.ArealUK.chunk_0175 s76
  have s74 : leavesOK ctxLitU 31268750000 4 ((leaves.drop 348).take 52) 32175000000 4 = true :=
    take_step (n := 2) (t := 52) (b := 350) rfl rfl ArealUCore.ArealUK.chunk_0174 s75
  have s73 : leavesOK ctxLitU 15625000000 3 ((leaves.drop 346).take 54) 32175000000 4 = true :=
    take_step (n := 2) (t := 54) (b := 348) rfl rfl ArealUCore.ArealUK.chunk_0173 s74
  have s72 : leavesOK ctxLitU 15612500000 3 ((leaves.drop 344).take 56) 32175000000 4 = true :=
    take_step (n := 2) (t := 56) (b := 346) rfl rfl ArealUCore.ArealUK.chunk_0172 s73
  have s71 : leavesOK ctxLitU 15600000000 3 ((leaves.drop 342).take 58) 32175000000 4 = true :=
    take_step (n := 2) (t := 58) (b := 344) rfl rfl ArealUCore.ArealUK.chunk_0171 s72
  have s70 : leavesOK ctxLitU 15587500000 3 ((leaves.drop 340).take 60) 32175000000 4 = true :=
    take_step (n := 2) (t := 60) (b := 342) rfl rfl ArealUCore.ArealUK.chunk_0170 s71
  have s69 : leavesOK ctxLitU 31156250000 4 ((leaves.drop 338).take 62) 32175000000 4 = true :=
    take_step (n := 2) (t := 62) (b := 340) rfl rfl ArealUCore.ArealUK.chunk_0169 s70
  have s68 : leavesOK ctxLitU 31143750000 4 ((leaves.drop 336).take 64) 32175000000 4 = true :=
    take_step (n := 2) (t := 64) (b := 338) rfl rfl ArealUCore.ArealUK.chunk_0168 s69
  have s67 : leavesOK ctxLitU 31131250000 4 ((leaves.drop 334).take 66) 32175000000 4 = true :=
    take_step (n := 2) (t := 66) (b := 336) rfl rfl ArealUCore.ArealUK.chunk_0167 s68
  have s66 : leavesOK ctxLitU 31118750000 4 ((leaves.drop 332).take 68) 32175000000 4 = true :=
    take_step (n := 2) (t := 68) (b := 334) rfl rfl ArealUCore.ArealUK.chunk_0166 s67
  have s65 : leavesOK ctxLitU 31106250000 4 ((leaves.drop 330).take 70) 32175000000 4 = true :=
    take_step (n := 2) (t := 70) (b := 332) rfl rfl ArealUCore.ArealUK.chunk_0165 s66
  have s64 : leavesOK ctxLitU 15543750000 3 ((leaves.drop 328).take 72) 32175000000 4 = true :=
    take_step (n := 2) (t := 72) (b := 330) rfl rfl ArealUCore.ArealUK.chunk_0164 s65
  have s63 : leavesOK ctxLitU 15531250000 3 ((leaves.drop 326).take 74) 32175000000 4 = true :=
    take_step (n := 2) (t := 74) (b := 328) rfl rfl ArealUCore.ArealUK.chunk_0163 s64
  have s62 : leavesOK ctxLitU 7756250000 2 ((leaves.drop 324).take 76) 32175000000 4 = true :=
    take_step (n := 2) (t := 76) (b := 326) rfl rfl ArealUCore.ArealUK.chunk_0162 s63
  have s61 : leavesOK ctxLitU 63462771374385 15 ((leaves.drop 322).take 78) 32175000000 4 = true :=
    take_step (n := 2) (t := 78) (b := 324) rfl rfl ArealUCore.ArealUK.chunk_0161 s62
  have s60 : leavesOK ctxLitU 126849856871925 16 ((leaves.drop 320).take 80) 32175000000 4 = true :=
    take_step (n := 2) (t := 80) (b := 322) rfl rfl ArealUCore.ArealUK.chunk_0160 s61
  have s59 : leavesOK ctxLitU 253649256492620 17 ((leaves.drop 318).take 82) 32175000000 4 = true :=
    take_step (n := 2) (t := 82) (b := 320) rfl rfl ArealUCore.ArealUK.chunk_0159 s60
  have s58 : leavesOK ctxLitU 126774170995080 16 ((leaves.drop 316).take 84) 32175000000 4 = true :=
    take_step (n := 2) (t := 84) (b := 318) rfl rfl ArealUCore.ArealUK.chunk_0158 s59
  have s57 : leavesOK ctxLitU 31643085497540 14 ((leaves.drop 314).take 86) 32175000000 4 = true :=
    take_step (n := 2) (t := 86) (b := 316) rfl rfl ArealUCore.ArealUK.chunk_0157 s58
  have s56 : leavesOK ctxLitU 7910400000000 12 ((leaves.drop 312).take 88) 32175000000 4 = true :=
    take_step (n := 2) (t := 88) (b := 314) rfl rfl ArealUCore.ArealUK.chunk_0156 s57
  have s55 : leavesOK ctxLitU 126443559819145 16 ((leaves.drop 310).take 90) 32175000000 4 = true :=
    take_step (n := 2) (t := 90) (b := 312) rfl rfl ArealUCore.ArealUK.chunk_0155 s56
  have s54 : leavesOK ctxLitU 252837983565948 17 ((leaves.drop 308).take 92) 32175000000 4 = true :=
    take_step (n := 2) (t := 92) (b := 310) rfl rfl ArealUCore.ArealUK.chunk_0154 s55
  have s53 : leavesOK ctxLitU 31567895891487 14 ((leaves.drop 306).take 94) 32175000000 4 = true :=
    take_step (n := 2) (t := 94) (b := 308) rfl rfl ArealUCore.ArealUK.chunk_0153 s54
  have s52 : leavesOK ctxLitU 7885831963826 12 ((leaves.drop 304).take 96) 32175000000 4 = true :=
    take_step (n := 2) (t := 96) (b := 306) rfl rfl ArealUCore.ArealUK.chunk_0152 s53
  have s51 : leavesOK ctxLitU 15393750000 3 ((leaves.drop 302).take 98) 32175000000 4 = true :=
    take_step (n := 2) (t := 98) (b := 304) rfl rfl ArealUCore.ArealUK.chunk_0151 s52
  have s50 : leavesOK ctxLitU 7687500000 2 ((leaves.drop 300).take 100) 32175000000 4 = true :=
    take_step (n := 2) (t := 100) (b := 302) rfl rfl ArealUCore.ArealUK.chunk_0150 s51
  have s49 : leavesOK ctxLitU 61481250000 5 ((leaves.drop 298).take 102) 32175000000 4 = true :=
    take_step (n := 2) (t := 102) (b := 300) rfl rfl ArealUCore.ArealUK.chunk_0149 s50
  have s48 : leavesOK ctxLitU 30731250000 4 ((leaves.drop 296).take 104) 32175000000 4 = true :=
    take_step (n := 2) (t := 104) (b := 298) rfl rfl ArealUCore.ArealUK.chunk_0148 s49
  have s47 : leavesOK ctxLitU 7675000000 2 ((leaves.drop 294).take 106) 32175000000 4 = true :=
    take_step (n := 2) (t := 106) (b := 296) rfl rfl ArealUCore.ArealUK.chunk_0147 s48
  have s46 : leavesOK ctxLitU 15331250000 3 ((leaves.drop 292).take 108) 32175000000 4 = true :=
    take_step (n := 2) (t := 108) (b := 294) rfl rfl ArealUCore.ArealUK.chunk_0146 s47
  have s45 : leavesOK ctxLitU 61306250000 5 ((leaves.drop 290).take 110) 32175000000 4 = true :=
    take_step (n := 2) (t := 110) (b := 292) rfl rfl ArealUCore.ArealUK.chunk_0145 s46
  have s44 : leavesOK ctxLitU 30643750000 4 ((leaves.drop 288).take 112) 32175000000 4 = true :=
    take_step (n := 2) (t := 112) (b := 290) rfl rfl ArealUCore.ArealUK.chunk_0144 s45
  have s43 : leavesOK ctxLitU 15312500000 3 ((leaves.drop 286).take 114) 32175000000 4 = true :=
    take_step (n := 2) (t := 114) (b := 288) rfl rfl ArealUCore.ArealUK.chunk_0143 s44
  have s42 : leavesOK ctxLitU 15300000000 3 ((leaves.drop 284).take 116) 32175000000 4 = true :=
    take_step (n := 2) (t := 116) (b := 286) rfl rfl ArealUCore.ArealUK.chunk_0142 s43
  have s41 : leavesOK ctxLitU 7825116978447 12 ((leaves.drop 282).take 118) 32175000000 4 = true :=
    take_step (n := 2) (t := 118) (b := 284) rfl rfl ArealUCore.ArealUK.chunk_0141 s42
  have s40 : leavesOK ctxLitU 7618750000 2 ((leaves.drop 280).take 120) 32175000000 4 = true :=
    take_step (n := 2) (t := 120) (b := 282) rfl rfl ArealUCore.ArealUK.chunk_0140 s41
  have s39 : leavesOK ctxLitU 30443750000 4 ((leaves.drop 278).take 122) 32175000000 4 = true :=
    take_step (n := 2) (t := 122) (b := 280) rfl rfl ArealUCore.ArealUK.chunk_0139 s40
  have s38 : leavesOK ctxLitU 30431250000 4 ((leaves.drop 276).take 124) 32175000000 4 = true :=
    take_step (n := 2) (t := 124) (b := 278) rfl rfl ArealUCore.ArealUK.chunk_0138 s39
  have s37 : leavesOK ctxLitU 7600000000 2 ((leaves.drop 274).take 126) 32175000000 4 = true :=
    take_step (n := 2) (t := 126) (b := 276) rfl rfl ArealUCore.ArealUK.chunk_0137 s38
  have s36 : leavesOK ctxLitU 15175000000 3 ((leaves.drop 272).take 128) 32175000000 4 = true :=
    take_step (n := 2) (t := 128) (b := 274) rfl rfl ArealUCore.ArealUK.chunk_0136 s37
  have s35 : leavesOK ctxLitU 30312500000 4 ((leaves.drop 270).take 130) 32175000000 4 = true :=
    take_step (n := 2) (t := 130) (b := 272) rfl rfl ArealUCore.ArealUK.chunk_0135 s36
  have s34 : leavesOK ctxLitU 30287500000 4 ((leaves.drop 268).take 132) 32175000000 4 = true :=
    take_step (n := 2) (t := 132) (b := 270) rfl rfl ArealUCore.ArealUK.chunk_0134 s35
  have s33 : leavesOK ctxLitU 30262500000 4 ((leaves.drop 266).take 134) 32175000000 4 = true :=
    take_step (n := 2) (t := 134) (b := 268) rfl rfl ArealUCore.ArealUK.chunk_0133 s34
  have s32 : leavesOK ctxLitU 60500000000 5 ((leaves.drop 264).take 136) 32175000000 4 = true :=
    take_step (n := 2) (t := 136) (b := 266) rfl rfl ArealUCore.ArealUK.chunk_0132 s33
  have s31 : leavesOK ctxLitU 60475000000 5 ((leaves.drop 262).take 138) 32175000000 4 = true :=
    take_step (n := 2) (t := 138) (b := 264) rfl rfl ArealUCore.ArealUK.chunk_0131 s32
  have s30 : leavesOK ctxLitU 30212500000 4 ((leaves.drop 260).take 140) 32175000000 4 = true :=
    take_step (n := 2) (t := 140) (b := 262) rfl rfl ArealUCore.ArealUK.chunk_0130 s31
  have s29 : leavesOK ctxLitU 30187500000 4 ((leaves.drop 258).take 142) 32175000000 4 = true :=
    take_step (n := 2) (t := 142) (b := 260) rfl rfl ArealUCore.ArealUK.chunk_0129 s30
  have s28 : leavesOK ctxLitU 15075000000 3 ((leaves.drop 256).take 144) 32175000000 4 = true :=
    take_step (n := 2) (t := 144) (b := 258) rfl rfl ArealUCore.ArealUK.chunk_0128 s29
  have s27 : leavesOK ctxLitU 15050000000 3 ((leaves.drop 254).take 146) 32175000000 4 = true :=
    take_step (n := 2) (t := 146) (b := 256) rfl rfl ArealUCore.ArealUK.chunk_0127 s28
  have s26 : leavesOK ctxLitU 15025000000 3 ((leaves.drop 252).take 148) 32175000000 4 = true :=
    take_step (n := 2) (t := 148) (b := 254) rfl rfl ArealUCore.ArealUK.chunk_0126 s27
  have s25 : leavesOK ctxLitU 15000000000 3 ((leaves.drop 250).take 150) 32175000000 4 = true :=
    take_step (n := 2) (t := 150) (b := 252) rfl rfl ArealUCore.ArealUK.chunk_0125 s26
  have s24 : leavesOK ctxLitU 14975000000 3 ((leaves.drop 248).take 152) 32175000000 4 = true :=
    take_step (n := 2) (t := 152) (b := 250) rfl rfl ArealUCore.ArealUK.chunk_0124 s25
  have s23 : leavesOK ctxLitU 29925000000 4 ((leaves.drop 246).take 154) 32175000000 4 = true :=
    take_step (n := 2) (t := 154) (b := 248) rfl rfl ArealUCore.ArealUK.chunk_0123 s24
  have s22 : leavesOK ctxLitU 59825000000 5 ((leaves.drop 244).take 156) 32175000000 4 = true :=
    take_step (n := 2) (t := 156) (b := 246) rfl rfl ArealUCore.ArealUK.chunk_0122 s23
  have s21 : leavesOK ctxLitU 14937500000 3 ((leaves.drop 242).take 158) 32175000000 4 = true :=
    take_step (n := 2) (t := 158) (b := 244) rfl rfl ArealUCore.ArealUK.chunk_0121 s22
  have s20 : leavesOK ctxLitU 7450000000 2 ((leaves.drop 240).take 160) 32175000000 4 = true :=
    take_step (n := 2) (t := 160) (b := 242) rfl rfl ArealUCore.ArealUK.chunk_0120 s21
  have s19 : leavesOK ctxLitU 7602705084719 12 ((leaves.drop 238).take 162) 32175000000 4 = true :=
    take_step (n := 2) (t := 162) (b := 240) rfl rfl ArealUCore.ArealUK.chunk_0119 s20
  have s18 : leavesOK ctxLitU 15155200000000 13 ((leaves.drop 236).take 164) 32175000000 4 = true :=
    take_step (n := 2) (t := 164) (b := 238) rfl rfl ArealUCore.ArealUK.chunk_0118 s19
  have s17 : leavesOK ctxLitU 14787500000 3 ((leaves.drop 234).take 166) 32175000000 4 = true :=
    take_step (n := 2) (t := 166) (b := 236) rfl rfl ArealUCore.ArealUK.chunk_0117 s18
  have s16 : leavesOK ctxLitU 29556250000 4 ((leaves.drop 232).take 168) 32175000000 4 = true :=
    take_step (n := 2) (t := 168) (b := 234) rfl rfl ArealUCore.ArealUK.chunk_0116 s17
  have s15 : leavesOK ctxLitU 7381250000 2 ((leaves.drop 230).take 170) 32175000000 4 = true :=
    take_step (n := 2) (t := 170) (b := 232) rfl rfl ArealUCore.ArealUK.chunk_0115 s16
  have s14 : leavesOK ctxLitU 3681250000 1 ((leaves.drop 228).take 172) 32175000000 4 = true :=
    take_step (n := 2) (t := 172) (b := 230) rfl rfl ArealUCore.ArealUK.chunk_0114 s15
  have s13 : leavesOK ctxLitU 7350000000 2 ((leaves.drop 226).take 174) 32175000000 4 = true :=
    take_step (n := 2) (t := 174) (b := 228) rfl rfl ArealUCore.ArealUK.chunk_0113 s14
  have s12 : leavesOK ctxLitU 14687500000 3 ((leaves.drop 224).take 176) 32175000000 4 = true :=
    take_step (n := 2) (t := 176) (b := 226) rfl rfl ArealUCore.ArealUK.chunk_0112 s13
  have s11 : leavesOK ctxLitU 14675000000 3 ((leaves.drop 222).take 178) 32175000000 4 = true :=
    take_step (n := 2) (t := 178) (b := 224) rfl rfl ArealUCore.ArealUK.chunk_0111 s12
  have s10 : leavesOK ctxLitU 14662500000 3 ((leaves.drop 220).take 180) 32175000000 4 = true :=
    take_step (n := 2) (t := 180) (b := 222) rfl rfl ArealUCore.ArealUK.chunk_0110 s11
  have s9 : leavesOK ctxLitU 14650000000 3 ((leaves.drop 218).take 182) 32175000000 4 = true :=
    take_step (n := 2) (t := 182) (b := 220) rfl rfl ArealUCore.ArealUK.chunk_0109 s10
  have s8 : leavesOK ctxLitU 14637500000 3 ((leaves.drop 216).take 184) 32175000000 4 = true :=
    take_step (n := 2) (t := 184) (b := 218) rfl rfl ArealUCore.ArealUK.chunk_0108 s9
  have s7 : leavesOK ctxLitU 14625000000 3 ((leaves.drop 214).take 186) 32175000000 4 = true :=
    take_step (n := 2) (t := 186) (b := 216) rfl rfl ArealUCore.ArealUK.chunk_0107 s8
  have s6 : leavesOK ctxLitU 14612500000 3 ((leaves.drop 212).take 188) 32175000000 4 = true :=
    take_step (n := 2) (t := 188) (b := 214) rfl rfl ArealUCore.ArealUK.chunk_0106 s7
  have s5 : leavesOK ctxLitU 14600000000 3 ((leaves.drop 210).take 190) 32175000000 4 = true :=
    take_step (n := 2) (t := 190) (b := 212) rfl rfl ArealUCore.ArealUK.chunk_0105 s6
  have s4 : leavesOK ctxLitU 29175000000 4 ((leaves.drop 208).take 192) 32175000000 4 = true :=
    take_step (n := 2) (t := 192) (b := 210) rfl rfl ArealUCore.ArealUK.chunk_0104 s5
  have s3 : leavesOK ctxLitU 29150000000 4 ((leaves.drop 206).take 194) 32175000000 4 = true :=
    take_step (n := 2) (t := 194) (b := 208) rfl rfl ArealUCore.ArealUK.chunk_0103 s4
  have s2 : leavesOK ctxLitU 29125000000 4 ((leaves.drop 204).take 196) 32175000000 4 = true :=
    take_step (n := 2) (t := 196) (b := 206) rfl rfl ArealUCore.ArealUK.chunk_0102 s3
  have s1 : leavesOK ctxLitU 29100000000 4 ((leaves.drop 202).take 198) 32175000000 4 = true :=
    take_step (n := 2) (t := 198) (b := 204) rfl rfl ArealUCore.ArealUK.chunk_0101 s2
  have s0 : leavesOK ctxLitU 29075000000 4 ((leaves.drop 200).take 200) 32175000000 4 = true :=
    take_step (n := 2) (t := 200) (b := 202) rfl rfl ArealUCore.ArealUK.chunk_0100 s1
  exact s0

end Areal.UCert

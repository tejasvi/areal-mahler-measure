import ArealUK.Chunk13100
import ArealUK.Chunk13101
import ArealUK.Chunk13102
import ArealUK.Chunk13103
import ArealUK.Chunk13104
import ArealUK.Chunk13105
import ArealUK.Chunk13106
import ArealUK.Chunk13107
import ArealUK.Chunk13108
import ArealUK.Chunk13109
import ArealUK.Chunk13110
import ArealUK.Chunk13111
import ArealUK.Chunk13112
import ArealUK.Chunk13113
import ArealUK.Chunk13114
import ArealUK.Chunk13115
import ArealUK.Chunk13116
import ArealUK.Chunk13117
import ArealUK.Chunk13118
import ArealUK.Chunk13119
import ArealUK.Chunk13120
import ArealUK.Chunk13121
import ArealUK.Chunk13122
import ArealUK.Chunk13123
import ArealUK.Chunk13124
import ArealUK.Chunk13125
import ArealUK.Chunk13126
import ArealUK.Chunk13127
import ArealUK.Chunk13128
import ArealUK.Chunk13129
import ArealUK.Chunk13130
import ArealUK.Chunk13131
import ArealUK.Chunk13132
import ArealUK.Chunk13133
import ArealUK.Chunk13134
import ArealUK.Chunk13135
import ArealUK.Chunk13136
import ArealUK.Chunk13137
import ArealUK.Chunk13138
import ArealUK.Chunk13139
import ArealUK.Chunk13140
import ArealUK.Chunk13141
import ArealUK.Chunk13142
import ArealUK.Chunk13143
import ArealUK.Chunk13144
import ArealUK.Chunk13145
import ArealUK.Chunk13146
import ArealUK.Chunk13147
import ArealUK.Chunk13148
import ArealUK.Chunk13149
import ArealUK.Chunk13150
import ArealUK.Chunk13151
import ArealUK.Chunk13152
import ArealUK.Chunk13153
import ArealUK.Chunk13154
import ArealUK.Chunk13155
import ArealUK.Chunk13156
import ArealUK.Chunk13157
import ArealUK.Chunk13158
import ArealUK.Chunk13159
import ArealUK.Chunk13160
import ArealUK.Chunk13161
import ArealUK.Chunk13162
import ArealUK.Chunk13163
import ArealUK.Chunk13164
import ArealUK.Chunk13165
import ArealUK.Chunk13166
import ArealUK.Chunk13167
import ArealUK.Chunk13168
import ArealUK.Chunk13169
import ArealUK.Chunk13170
import ArealUK.Chunk13171
import ArealUK.Chunk13172
import ArealUK.Chunk13173
import ArealUK.Chunk13174
import ArealUK.Chunk13175
import ArealUK.Chunk13176
import ArealUK.Chunk13177
import ArealUK.Chunk13178
import ArealUK.Chunk13179
import ArealUK.Chunk13180
import ArealUK.Chunk13181
import ArealUK.Chunk13182
import ArealUK.Chunk13183
import ArealUK.Chunk13184
import ArealUK.Chunk13185
import ArealUK.Chunk13186
import ArealUK.Chunk13187
import ArealUK.Chunk13188
import ArealUK.Chunk13189
import ArealUK.Chunk13190
import ArealUK.Chunk13191
import ArealUK.Chunk13192
import ArealUK.Chunk13193
import ArealUK.Chunk13194
import ArealUK.Chunk13195
import ArealUK.Chunk13196
import ArealUK.Chunk13197
import ArealUK.Chunk13198
import ArealUK.Chunk13199
import Areal.UCert.LeavesKGen

/-! Group 131 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_131 : leavesOK ctxLitU 266500000000 1 ((leaves.drop 26200).take 200) 134437500000 0 = true := by
  have s99 := ArealUCore.ArealUK.chunk_13199
  have s98 : leavesOK ctxLitU 268850000000 1 ((leaves.drop 26396).take 4) 134437500000 0 = true :=
    take_step (n := 2) (t := 4) (b := 26398) rfl rfl ArealUCore.ArealUK.chunk_13198 s99
  have s97 : leavesOK ctxLitU 268825000000 1 ((leaves.drop 26394).take 6) 134437500000 0 = true :=
    take_step (n := 2) (t := 6) (b := 26396) rfl rfl ArealUCore.ArealUK.chunk_13197 s98
  have s96 : leavesOK ctxLitU 268800000000 1 ((leaves.drop 26392).take 8) 134437500000 0 = true :=
    take_step (n := 2) (t := 8) (b := 26394) rfl rfl ArealUCore.ArealUK.chunk_13196 s97
  have s95 : leavesOK ctxLitU 537550000000 2 ((leaves.drop 26390).take 10) 134437500000 0 = true :=
    take_step (n := 2) (t := 10) (b := 26392) rfl rfl ArealUCore.ArealUK.chunk_13195 s96
  have s94 : leavesOK ctxLitU 537500000000 2 ((leaves.drop 26388).take 12) 134437500000 0 = true :=
    take_step (n := 2) (t := 12) (b := 26390) rfl rfl ArealUCore.ArealUK.chunk_13194 s95
  have s93 : leavesOK ctxLitU 537450000000 2 ((leaves.drop 26386).take 14) 134437500000 0 = true :=
    take_step (n := 2) (t := 14) (b := 26388) rfl rfl ArealUCore.ArealUK.chunk_13193 s94
  have s92 : leavesOK ctxLitU 537400000000 2 ((leaves.drop 26384).take 16) 134437500000 0 = true :=
    take_step (n := 2) (t := 16) (b := 26386) rfl rfl ArealUCore.ArealUK.chunk_13192 s93
  have s91 : leavesOK ctxLitU 537350000000 2 ((leaves.drop 26382).take 18) 134437500000 0 = true :=
    take_step (n := 2) (t := 18) (b := 26384) rfl rfl ArealUCore.ArealUK.chunk_13191 s92
  have s90 : leavesOK ctxLitU 537300000000 2 ((leaves.drop 26380).take 20) 134437500000 0 = true :=
    take_step (n := 2) (t := 20) (b := 26382) rfl rfl ArealUCore.ArealUK.chunk_13190 s91
  have s89 : leavesOK ctxLitU 537250000000 2 ((leaves.drop 26378).take 22) 134437500000 0 = true :=
    take_step (n := 2) (t := 22) (b := 26380) rfl rfl ArealUCore.ArealUK.chunk_13189 s90
  have s88 : leavesOK ctxLitU 537200000000 2 ((leaves.drop 26376).take 24) 134437500000 0 = true :=
    take_step (n := 2) (t := 24) (b := 26378) rfl rfl ArealUCore.ArealUK.chunk_13188 s89
  have s87 : leavesOK ctxLitU 268575000000 1 ((leaves.drop 26374).take 26) 134437500000 0 = true :=
    take_step (n := 2) (t := 26) (b := 26376) rfl rfl ArealUCore.ArealUK.chunk_13187 s88
  have s86 : leavesOK ctxLitU 268550000000 1 ((leaves.drop 26372).take 28) 134437500000 0 = true :=
    take_step (n := 2) (t := 28) (b := 26374) rfl rfl ArealUCore.ArealUK.chunk_13186 s87
  have s85 : leavesOK ctxLitU 134262500000 0 ((leaves.drop 26370).take 30) 134437500000 0 = true :=
    take_step (n := 2) (t := 30) (b := 26372) rfl rfl ArealUCore.ArealUK.chunk_13185 s86
  have s84 : leavesOK ctxLitU 134250000000 0 ((leaves.drop 26368).take 32) 134437500000 0 = true :=
    take_step (n := 2) (t := 32) (b := 26370) rfl rfl ArealUCore.ArealUK.chunk_13184 s85
  have s83 : leavesOK ctxLitU 134237500000 0 ((leaves.drop 26366).take 34) 134437500000 0 = true :=
    take_step (n := 2) (t := 34) (b := 26368) rfl rfl ArealUCore.ArealUK.chunk_13183 s84
  have s82 : leavesOK ctxLitU 268462500000 1 ((leaves.drop 26364).take 36) 134437500000 0 = true :=
    take_step (n := 2) (t := 36) (b := 26366) rfl rfl ArealUCore.ArealUK.chunk_13182 s83
  have s81 : leavesOK ctxLitU 268450000000 1 ((leaves.drop 26362).take 38) 134437500000 0 = true :=
    take_step (n := 2) (t := 38) (b := 26364) rfl rfl ArealUCore.ArealUK.chunk_13181 s82
  have s80 : leavesOK ctxLitU 268425000000 1 ((leaves.drop 26360).take 40) 134437500000 0 = true :=
    take_step (n := 2) (t := 40) (b := 26362) rfl rfl ArealUCore.ArealUK.chunk_13180 s81
  have s79 : leavesOK ctxLitU 268400000000 1 ((leaves.drop 26358).take 42) 134437500000 0 = true :=
    take_step (n := 2) (t := 42) (b := 26360) rfl rfl ArealUCore.ArealUK.chunk_13179 s80
  have s78 : leavesOK ctxLitU 268375000000 1 ((leaves.drop 26356).take 44) 134437500000 0 = true :=
    take_step (n := 2) (t := 44) (b := 26358) rfl rfl ArealUCore.ArealUK.chunk_13178 s79
  have s77 : leavesOK ctxLitU 268350000000 1 ((leaves.drop 26354).take 46) 134437500000 0 = true :=
    take_step (n := 2) (t := 46) (b := 26356) rfl rfl ArealUCore.ArealUK.chunk_13177 s78
  have s76 : leavesOK ctxLitU 134162500000 0 ((leaves.drop 26352).take 48) 134437500000 0 = true :=
    take_step (n := 2) (t := 48) (b := 26354) rfl rfl ArealUCore.ArealUK.chunk_13176 s77
  have s75 : leavesOK ctxLitU 134150000000 0 ((leaves.drop 26350).take 50) 134437500000 0 = true :=
    take_step (n := 2) (t := 50) (b := 26352) rfl rfl ArealUCore.ArealUK.chunk_13175 s76
  have s74 : leavesOK ctxLitU 268275000000 1 ((leaves.drop 26348).take 52) 134437500000 0 = true :=
    take_step (n := 2) (t := 52) (b := 26350) rfl rfl ArealUCore.ArealUK.chunk_13174 s75
  have s73 : leavesOK ctxLitU 268250000000 1 ((leaves.drop 26346).take 54) 134437500000 0 = true :=
    take_step (n := 2) (t := 54) (b := 26348) rfl rfl ArealUCore.ArealUK.chunk_13173 s74
  have s72 : leavesOK ctxLitU 536450000000 2 ((leaves.drop 26344).take 56) 134437500000 0 = true :=
    take_step (n := 2) (t := 56) (b := 26346) rfl rfl ArealUCore.ArealUK.chunk_13172 s73
  have s71 : leavesOK ctxLitU 536400000000 2 ((leaves.drop 26342).take 58) 134437500000 0 = true :=
    take_step (n := 2) (t := 58) (b := 26344) rfl rfl ArealUCore.ArealUK.chunk_13171 s72
  have s70 : leavesOK ctxLitU 536350000000 2 ((leaves.drop 26340).take 60) 134437500000 0 = true :=
    take_step (n := 2) (t := 60) (b := 26342) rfl rfl ArealUCore.ArealUK.chunk_13170 s71
  have s69 : leavesOK ctxLitU 536300000000 2 ((leaves.drop 26338).take 62) 134437500000 0 = true :=
    take_step (n := 2) (t := 62) (b := 26340) rfl rfl ArealUCore.ArealUK.chunk_13169 s70
  have s68 : leavesOK ctxLitU 268125000000 1 ((leaves.drop 26336).take 64) 134437500000 0 = true :=
    take_step (n := 2) (t := 64) (b := 26338) rfl rfl ArealUCore.ArealUK.chunk_13168 s69
  have s67 : leavesOK ctxLitU 268100000000 1 ((leaves.drop 26334).take 66) 134437500000 0 = true :=
    take_step (n := 2) (t := 66) (b := 26336) rfl rfl ArealUCore.ArealUK.chunk_13167 s68
  have s66 : leavesOK ctxLitU 134037500000 0 ((leaves.drop 26332).take 68) 134437500000 0 = true :=
    take_step (n := 2) (t := 68) (b := 26334) rfl rfl ArealUCore.ArealUK.chunk_13166 s67
  have s65 : leavesOK ctxLitU 134025000000 0 ((leaves.drop 26330).take 70) 134437500000 0 = true :=
    take_step (n := 2) (t := 70) (b := 26332) rfl rfl ArealUCore.ArealUK.chunk_13165 s66
  have s64 : leavesOK ctxLitU 268025000000 1 ((leaves.drop 26328).take 72) 134437500000 0 = true :=
    take_step (n := 2) (t := 72) (b := 26330) rfl rfl ArealUCore.ArealUK.chunk_13164 s65
  have s63 : leavesOK ctxLitU 268000000000 1 ((leaves.drop 26326).take 74) 134437500000 0 = true :=
    take_step (n := 2) (t := 74) (b := 26328) rfl rfl ArealUCore.ArealUK.chunk_13163 s64
  have s62 : leavesOK ctxLitU 267975000000 1 ((leaves.drop 26324).take 76) 134437500000 0 = true :=
    take_step (n := 2) (t := 76) (b := 26326) rfl rfl ArealUCore.ArealUK.chunk_13162 s63
  have s61 : leavesOK ctxLitU 267950000000 1 ((leaves.drop 26322).take 78) 134437500000 0 = true :=
    take_step (n := 2) (t := 78) (b := 26324) rfl rfl ArealUCore.ArealUK.chunk_13161 s62
  have s60 : leavesOK ctxLitU 133962500000 0 ((leaves.drop 26320).take 80) 134437500000 0 = true :=
    take_step (n := 2) (t := 80) (b := 26322) rfl rfl ArealUCore.ArealUK.chunk_13160 s61
  have s59 : leavesOK ctxLitU 133950000000 0 ((leaves.drop 26318).take 82) 134437500000 0 = true :=
    take_step (n := 2) (t := 82) (b := 26320) rfl rfl ArealUCore.ArealUK.chunk_13159 s60
  have s58 : leavesOK ctxLitU 133937500000 0 ((leaves.drop 26316).take 84) 134437500000 0 = true :=
    take_step (n := 2) (t := 84) (b := 26318) rfl rfl ArealUCore.ArealUK.chunk_13158 s59
  have s57 : leavesOK ctxLitU 133925000000 0 ((leaves.drop 26314).take 86) 134437500000 0 = true :=
    take_step (n := 2) (t := 86) (b := 26316) rfl rfl ArealUCore.ArealUK.chunk_13157 s58
  have s56 : leavesOK ctxLitU 267825000000 1 ((leaves.drop 26312).take 88) 134437500000 0 = true :=
    take_step (n := 2) (t := 88) (b := 26314) rfl rfl ArealUCore.ArealUK.chunk_13156 s57
  have s55 : leavesOK ctxLitU 267800000000 1 ((leaves.drop 26310).take 90) 134437500000 0 = true :=
    take_step (n := 2) (t := 90) (b := 26312) rfl rfl ArealUCore.ArealUK.chunk_13155 s56
  have s54 : leavesOK ctxLitU 535550000000 2 ((leaves.drop 26308).take 92) 134437500000 0 = true :=
    take_step (n := 2) (t := 92) (b := 26310) rfl rfl ArealUCore.ArealUK.chunk_13154 s55
  have s53 : leavesOK ctxLitU 535500000000 2 ((leaves.drop 26306).take 94) 134437500000 0 = true :=
    take_step (n := 2) (t := 94) (b := 26308) rfl rfl ArealUCore.ArealUK.chunk_13153 s54
  have s52 : leavesOK ctxLitU 267725000000 1 ((leaves.drop 26304).take 96) 134437500000 0 = true :=
    take_step (n := 2) (t := 96) (b := 26306) rfl rfl ArealUCore.ArealUK.chunk_13152 s53
  have s51 : leavesOK ctxLitU 267700000000 1 ((leaves.drop 26302).take 98) 134437500000 0 = true :=
    take_step (n := 2) (t := 98) (b := 26304) rfl rfl ArealUCore.ArealUK.chunk_13151 s52
  have s50 : leavesOK ctxLitU 133837500000 0 ((leaves.drop 26300).take 100) 134437500000 0 = true :=
    take_step (n := 2) (t := 100) (b := 26302) rfl rfl ArealUCore.ArealUK.chunk_13150 s51
  have s49 : leavesOK ctxLitU 267662500000 1 ((leaves.drop 26298).take 102) 134437500000 0 = true :=
    take_step (n := 2) (t := 102) (b := 26300) rfl rfl ArealUCore.ArealUK.chunk_13149 s50
  have s48 : leavesOK ctxLitU 267650000000 1 ((leaves.drop 26296).take 104) 134437500000 0 = true :=
    take_step (n := 2) (t := 104) (b := 26298) rfl rfl ArealUCore.ArealUK.chunk_13148 s49
  have s47 : leavesOK ctxLitU 267625000000 1 ((leaves.drop 26294).take 106) 134437500000 0 = true :=
    take_step (n := 2) (t := 106) (b := 26296) rfl rfl ArealUCore.ArealUK.chunk_13147 s48
  have s46 : leavesOK ctxLitU 267600000000 1 ((leaves.drop 26292).take 108) 134437500000 0 = true :=
    take_step (n := 2) (t := 108) (b := 26294) rfl rfl ArealUCore.ArealUK.chunk_13146 s47
  have s45 : leavesOK ctxLitU 267575000000 1 ((leaves.drop 26290).take 110) 134437500000 0 = true :=
    take_step (n := 2) (t := 110) (b := 26292) rfl rfl ArealUCore.ArealUK.chunk_13145 s46
  have s44 : leavesOK ctxLitU 267550000000 1 ((leaves.drop 26288).take 112) 134437500000 0 = true :=
    take_step (n := 2) (t := 112) (b := 26290) rfl rfl ArealUCore.ArealUK.chunk_13144 s45
  have s43 : leavesOK ctxLitU 133762500000 0 ((leaves.drop 26286).take 114) 134437500000 0 = true :=
    take_step (n := 2) (t := 114) (b := 26288) rfl rfl ArealUCore.ArealUK.chunk_13143 s44
  have s42 : leavesOK ctxLitU 133750000000 0 ((leaves.drop 26284).take 116) 134437500000 0 = true :=
    take_step (n := 2) (t := 116) (b := 26286) rfl rfl ArealUCore.ArealUK.chunk_13142 s43
  have s41 : leavesOK ctxLitU 267475000000 1 ((leaves.drop 26282).take 118) 134437500000 0 = true :=
    take_step (n := 2) (t := 118) (b := 26284) rfl rfl ArealUCore.ArealUK.chunk_13141 s42
  have s40 : leavesOK ctxLitU 267450000000 1 ((leaves.drop 26280).take 120) 134437500000 0 = true :=
    take_step (n := 2) (t := 120) (b := 26282) rfl rfl ArealUCore.ArealUK.chunk_13140 s41
  have s39 : leavesOK ctxLitU 534850000000 2 ((leaves.drop 26278).take 122) 134437500000 0 = true :=
    take_step (n := 2) (t := 122) (b := 26280) rfl rfl ArealUCore.ArealUK.chunk_13139 s40
  have s38 : leavesOK ctxLitU 534800000000 2 ((leaves.drop 26276).take 124) 134437500000 0 = true :=
    take_step (n := 2) (t := 124) (b := 26278) rfl rfl ArealUCore.ArealUK.chunk_13138 s39
  have s37 : leavesOK ctxLitU 534750000000 2 ((leaves.drop 26274).take 126) 134437500000 0 = true :=
    take_step (n := 2) (t := 126) (b := 26276) rfl rfl ArealUCore.ArealUK.chunk_13137 s38
  have s36 : leavesOK ctxLitU 534700000000 2 ((leaves.drop 26272).take 128) 134437500000 0 = true :=
    take_step (n := 2) (t := 128) (b := 26274) rfl rfl ArealUCore.ArealUK.chunk_13136 s37
  have s35 : leavesOK ctxLitU 267325000000 1 ((leaves.drop 26270).take 130) 134437500000 0 = true :=
    take_step (n := 2) (t := 130) (b := 26272) rfl rfl ArealUCore.ArealUK.chunk_13135 s36
  have s34 : leavesOK ctxLitU 267300000000 1 ((leaves.drop 26268).take 132) 134437500000 0 = true :=
    take_step (n := 2) (t := 132) (b := 26270) rfl rfl ArealUCore.ArealUK.chunk_13134 s35
  have s33 : leavesOK ctxLitU 133637500000 0 ((leaves.drop 26266).take 134) 134437500000 0 = true :=
    take_step (n := 2) (t := 134) (b := 26268) rfl rfl ArealUCore.ArealUK.chunk_13133 s34
  have s32 : leavesOK ctxLitU 133625000000 0 ((leaves.drop 26264).take 136) 134437500000 0 = true :=
    take_step (n := 2) (t := 136) (b := 26266) rfl rfl ArealUCore.ArealUK.chunk_13132 s33
  have s31 : leavesOK ctxLitU 267225000000 1 ((leaves.drop 26262).take 138) 134437500000 0 = true :=
    take_step (n := 2) (t := 138) (b := 26264) rfl rfl ArealUCore.ArealUK.chunk_13131 s32
  have s30 : leavesOK ctxLitU 267200000000 1 ((leaves.drop 26260).take 140) 134437500000 0 = true :=
    take_step (n := 2) (t := 140) (b := 26262) rfl rfl ArealUCore.ArealUK.chunk_13130 s31
  have s29 : leavesOK ctxLitU 267175000000 1 ((leaves.drop 26258).take 142) 134437500000 0 = true :=
    take_step (n := 2) (t := 142) (b := 26260) rfl rfl ArealUCore.ArealUK.chunk_13129 s30
  have s28 : leavesOK ctxLitU 267150000000 1 ((leaves.drop 26256).take 144) 134437500000 0 = true :=
    take_step (n := 2) (t := 144) (b := 26258) rfl rfl ArealUCore.ArealUK.chunk_13128 s29
  have s27 : leavesOK ctxLitU 133562500000 0 ((leaves.drop 26254).take 146) 134437500000 0 = true :=
    take_step (n := 2) (t := 146) (b := 26256) rfl rfl ArealUCore.ArealUK.chunk_13127 s28
  have s26 : leavesOK ctxLitU 133550000000 0 ((leaves.drop 26252).take 148) 134437500000 0 = true :=
    take_step (n := 2) (t := 148) (b := 26254) rfl rfl ArealUCore.ArealUK.chunk_13126 s27
  have s25 : leavesOK ctxLitU 133537500000 0 ((leaves.drop 26250).take 150) 134437500000 0 = true :=
    take_step (n := 2) (t := 150) (b := 26252) rfl rfl ArealUCore.ArealUK.chunk_13125 s26
  have s24 : leavesOK ctxLitU 133525000000 0 ((leaves.drop 26248).take 152) 134437500000 0 = true :=
    take_step (n := 2) (t := 152) (b := 26250) rfl rfl ArealUCore.ArealUK.chunk_13124 s25
  have s23 : leavesOK ctxLitU 267025000000 1 ((leaves.drop 26246).take 154) 134437500000 0 = true :=
    take_step (n := 2) (t := 154) (b := 26248) rfl rfl ArealUCore.ArealUK.chunk_13123 s24
  have s22 : leavesOK ctxLitU 267000000000 1 ((leaves.drop 26244).take 156) 134437500000 0 = true :=
    take_step (n := 2) (t := 156) (b := 26246) rfl rfl ArealUCore.ArealUK.chunk_13122 s23
  have s21 : leavesOK ctxLitU 533950000000 2 ((leaves.drop 26242).take 158) 134437500000 0 = true :=
    take_step (n := 2) (t := 158) (b := 26244) rfl rfl ArealUCore.ArealUK.chunk_13121 s22
  have s20 : leavesOK ctxLitU 533900000000 2 ((leaves.drop 26240).take 160) 134437500000 0 = true :=
    take_step (n := 2) (t := 160) (b := 26242) rfl rfl ArealUCore.ArealUK.chunk_13120 s21
  have s19 : leavesOK ctxLitU 266925000000 1 ((leaves.drop 26238).take 162) 134437500000 0 = true :=
    take_step (n := 2) (t := 162) (b := 26240) rfl rfl ArealUCore.ArealUK.chunk_13119 s20
  have s18 : leavesOK ctxLitU 266900000000 1 ((leaves.drop 26236).take 164) 134437500000 0 = true :=
    take_step (n := 2) (t := 164) (b := 26238) rfl rfl ArealUCore.ArealUK.chunk_13118 s19
  have s17 : leavesOK ctxLitU 133437500000 0 ((leaves.drop 26234).take 166) 134437500000 0 = true :=
    take_step (n := 2) (t := 166) (b := 26236) rfl rfl ArealUCore.ArealUK.chunk_13117 s18
  have s16 : leavesOK ctxLitU 266862500000 1 ((leaves.drop 26232).take 168) 134437500000 0 = true :=
    take_step (n := 2) (t := 168) (b := 26234) rfl rfl ArealUCore.ArealUK.chunk_13116 s17
  have s15 : leavesOK ctxLitU 533712500000 2 ((leaves.drop 26230).take 170) 134437500000 0 = true :=
    take_step (n := 2) (t := 170) (b := 26232) rfl rfl ArealUCore.ArealUK.chunk_13115 s16
  have s14 : leavesOK ctxLitU 266837500000 1 ((leaves.drop 26228).take 172) 134437500000 0 = true :=
    take_step (n := 2) (t := 172) (b := 26230) rfl rfl ArealUCore.ArealUK.chunk_13114 s15
  have s13 : leavesOK ctxLitU 266812500000 1 ((leaves.drop 26226).take 174) 134437500000 0 = true :=
    take_step (n := 2) (t := 174) (b := 26228) rfl rfl ArealUCore.ArealUK.chunk_13113 s14
  have s12 : leavesOK ctxLitU 266787500000 1 ((leaves.drop 26224).take 176) 134437500000 0 = true :=
    take_step (n := 2) (t := 176) (b := 26226) rfl rfl ArealUCore.ArealUK.chunk_13112 s13
  have s11 : leavesOK ctxLitU 266762500000 1 ((leaves.drop 26222).take 178) 134437500000 0 = true :=
    take_step (n := 2) (t := 178) (b := 26224) rfl rfl ArealUCore.ArealUK.chunk_13111 s12
  have s10 : leavesOK ctxLitU 266743750000 1 ((leaves.drop 26220).take 180) 134437500000 0 = true :=
    take_step (n := 2) (t := 180) (b := 26222) rfl rfl ArealUCore.ArealUK.chunk_13110 s11
  have s9 : leavesOK ctxLitU 133362500000 0 ((leaves.drop 26218).take 182) 134437500000 0 = true :=
    take_step (n := 2) (t := 182) (b := 26220) rfl rfl ArealUCore.ArealUK.chunk_13109 s10
  have s8 : leavesOK ctxLitU 133350000000 0 ((leaves.drop 26216).take 184) 134437500000 0 = true :=
    take_step (n := 2) (t := 184) (b := 26218) rfl rfl ArealUCore.ArealUK.chunk_13108 s9
  have s7 : leavesOK ctxLitU 266675000000 1 ((leaves.drop 26214).take 186) 134437500000 0 = true :=
    take_step (n := 2) (t := 186) (b := 26216) rfl rfl ArealUCore.ArealUK.chunk_13107 s8
  have s6 : leavesOK ctxLitU 266650000000 1 ((leaves.drop 26212).take 188) 134437500000 0 = true :=
    take_step (n := 2) (t := 188) (b := 26214) rfl rfl ArealUCore.ArealUK.chunk_13106 s7
  have s5 : leavesOK ctxLitU 533250000000 2 ((leaves.drop 26210).take 190) 134437500000 0 = true :=
    take_step (n := 2) (t := 190) (b := 26212) rfl rfl ArealUCore.ArealUK.chunk_13105 s6
  have s4 : leavesOK ctxLitU 533200000000 2 ((leaves.drop 26208).take 192) 134437500000 0 = true :=
    take_step (n := 2) (t := 192) (b := 26210) rfl rfl ArealUCore.ArealUK.chunk_13104 s5
  have s3 : leavesOK ctxLitU 533150000000 2 ((leaves.drop 26206).take 194) 134437500000 0 = true :=
    take_step (n := 2) (t := 194) (b := 26208) rfl rfl ArealUCore.ArealUK.chunk_13103 s4
  have s2 : leavesOK ctxLitU 533100000000 2 ((leaves.drop 26204).take 196) 134437500000 0 = true :=
    take_step (n := 2) (t := 196) (b := 26206) rfl rfl ArealUCore.ArealUK.chunk_13102 s3
  have s1 : leavesOK ctxLitU 266525000000 1 ((leaves.drop 26202).take 198) 134437500000 0 = true :=
    take_step (n := 2) (t := 198) (b := 26204) rfl rfl ArealUCore.ArealUK.chunk_13101 s2
  have s0 : leavesOK ctxLitU 266500000000 1 ((leaves.drop 26200).take 200) 134437500000 0 = true :=
    take_step (n := 2) (t := 200) (b := 26202) rfl rfl ArealUCore.ArealUK.chunk_13100 s1
  exact s0

end Areal.UCert

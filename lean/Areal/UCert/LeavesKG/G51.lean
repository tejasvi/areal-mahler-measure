import ArealUK.Chunk5100
import ArealUK.Chunk5101
import ArealUK.Chunk5102
import ArealUK.Chunk5103
import ArealUK.Chunk5104
import ArealUK.Chunk5105
import ArealUK.Chunk5106
import ArealUK.Chunk5107
import ArealUK.Chunk5108
import ArealUK.Chunk5109
import ArealUK.Chunk5110
import ArealUK.Chunk5111
import ArealUK.Chunk5112
import ArealUK.Chunk5113
import ArealUK.Chunk5114
import ArealUK.Chunk5115
import ArealUK.Chunk5116
import ArealUK.Chunk5117
import ArealUK.Chunk5118
import ArealUK.Chunk5119
import ArealUK.Chunk5120
import ArealUK.Chunk5121
import ArealUK.Chunk5122
import ArealUK.Chunk5123
import ArealUK.Chunk5124
import ArealUK.Chunk5125
import ArealUK.Chunk5126
import ArealUK.Chunk5127
import ArealUK.Chunk5128
import ArealUK.Chunk5129
import ArealUK.Chunk5130
import ArealUK.Chunk5131
import ArealUK.Chunk5132
import ArealUK.Chunk5133
import ArealUK.Chunk5134
import ArealUK.Chunk5135
import ArealUK.Chunk5136
import ArealUK.Chunk5137
import ArealUK.Chunk5138
import ArealUK.Chunk5139
import ArealUK.Chunk5140
import ArealUK.Chunk5141
import ArealUK.Chunk5142
import ArealUK.Chunk5143
import ArealUK.Chunk5144
import ArealUK.Chunk5145
import ArealUK.Chunk5146
import ArealUK.Chunk5147
import ArealUK.Chunk5148
import ArealUK.Chunk5149
import ArealUK.Chunk5150
import ArealUK.Chunk5151
import ArealUK.Chunk5152
import ArealUK.Chunk5153
import ArealUK.Chunk5154
import ArealUK.Chunk5155
import ArealUK.Chunk5156
import ArealUK.Chunk5157
import ArealUK.Chunk5158
import ArealUK.Chunk5159
import ArealUK.Chunk5160
import ArealUK.Chunk5161
import ArealUK.Chunk5162
import ArealUK.Chunk5163
import ArealUK.Chunk5164
import ArealUK.Chunk5165
import ArealUK.Chunk5166
import ArealUK.Chunk5167
import ArealUK.Chunk5168
import ArealUK.Chunk5169
import ArealUK.Chunk5170
import ArealUK.Chunk5171
import ArealUK.Chunk5172
import ArealUK.Chunk5173
import ArealUK.Chunk5174
import ArealUK.Chunk5175
import ArealUK.Chunk5176
import ArealUK.Chunk5177
import ArealUK.Chunk5178
import ArealUK.Chunk5179
import ArealUK.Chunk5180
import ArealUK.Chunk5181
import ArealUK.Chunk5182
import ArealUK.Chunk5183
import ArealUK.Chunk5184
import ArealUK.Chunk5185
import ArealUK.Chunk5186
import ArealUK.Chunk5187
import ArealUK.Chunk5188
import ArealUK.Chunk5189
import ArealUK.Chunk5190
import ArealUK.Chunk5191
import ArealUK.Chunk5192
import ArealUK.Chunk5193
import ArealUK.Chunk5194
import ArealUK.Chunk5195
import ArealUK.Chunk5196
import ArealUK.Chunk5197
import ArealUK.Chunk5198
import ArealUK.Chunk5199
import Areal.UCert.LeavesKGen

/-! Group 51 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_51 : leavesOK ctxLitU 271775000000 3 ((leaves.drop 10200).take 200) 138156250000 2 = true := by
  have s99 := ArealUCore.ArealUK.chunk_5199
  have s98 : leavesOK ctxLitU 138137500000 2 ((leaves.drop 10396).take 4) 138156250000 2 = true :=
    take_step (n := 2) (t := 4) (b := 10398) rfl rfl ArealUCore.ArealUK.chunk_5198 s99
  have s97 : leavesOK ctxLitU 138125000000 2 ((leaves.drop 10394).take 6) 138156250000 2 = true :=
    take_step (n := 2) (t := 6) (b := 10396) rfl rfl ArealUCore.ArealUK.chunk_5197 s98
  have s96 : leavesOK ctxLitU 138106250000 2 ((leaves.drop 10392).take 8) 138156250000 2 = true :=
    take_step (n := 2) (t := 8) (b := 10394) rfl rfl ArealUCore.ArealUK.chunk_5196 s97
  have s95 : leavesOK ctxLitU 138093750000 2 ((leaves.drop 10390).take 10) 138156250000 2 = true :=
    take_step (n := 2) (t := 10) (b := 10392) rfl rfl ArealUCore.ArealUK.chunk_5195 s96
  have s94 : leavesOK ctxLitU 69037500000 1 ((leaves.drop 10388).take 12) 138156250000 2 = true :=
    take_step (n := 2) (t := 12) (b := 10390) rfl rfl ArealUCore.ArealUK.chunk_5194 s95
  have s93 : leavesOK ctxLitU 69025000000 1 ((leaves.drop 10386).take 14) 138156250000 2 = true :=
    take_step (n := 2) (t := 14) (b := 10388) rfl rfl ArealUCore.ArealUK.chunk_5193 s94
  have s92 : leavesOK ctxLitU 69012500000 1 ((leaves.drop 10384).take 16) 138156250000 2 = true :=
    take_step (n := 2) (t := 16) (b := 10386) rfl rfl ArealUCore.ArealUK.chunk_5192 s93
  have s91 : leavesOK ctxLitU 69000000000 1 ((leaves.drop 10382).take 18) 138156250000 2 = true :=
    take_step (n := 2) (t := 18) (b := 10384) rfl rfl ArealUCore.ArealUK.chunk_5191 s92
  have s90 : leavesOK ctxLitU 137975000000 2 ((leaves.drop 10380).take 20) 138156250000 2 = true :=
    take_step (n := 2) (t := 20) (b := 10382) rfl rfl ArealUCore.ArealUK.chunk_5190 s91
  have s89 : leavesOK ctxLitU 137950000000 2 ((leaves.drop 10378).take 22) 138156250000 2 = true :=
    take_step (n := 2) (t := 22) (b := 10380) rfl rfl ArealUCore.ArealUK.chunk_5189 s90
  have s88 : leavesOK ctxLitU 137925000000 2 ((leaves.drop 10376).take 24) 138156250000 2 = true :=
    take_step (n := 2) (t := 24) (b := 10378) rfl rfl ArealUCore.ArealUK.chunk_5188 s89
  have s87 : leavesOK ctxLitU 137900000000 2 ((leaves.drop 10374).take 26) 138156250000 2 = true :=
    take_step (n := 2) (t := 26) (b := 10376) rfl rfl ArealUCore.ArealUK.chunk_5187 s88
  have s86 : leavesOK ctxLitU 275750000000 3 ((leaves.drop 10372).take 28) 138156250000 2 = true :=
    take_step (n := 2) (t := 28) (b := 10374) rfl rfl ArealUCore.ArealUK.chunk_5186 s87
  have s85 : leavesOK ctxLitU 275700000000 3 ((leaves.drop 10370).take 30) 138156250000 2 = true :=
    take_step (n := 2) (t := 30) (b := 10372) rfl rfl ArealUCore.ArealUK.chunk_5185 s86
  have s84 : leavesOK ctxLitU 275650000000 3 ((leaves.drop 10368).take 32) 138156250000 2 = true :=
    take_step (n := 2) (t := 32) (b := 10370) rfl rfl ArealUCore.ArealUK.chunk_5184 s85
  have s83 : leavesOK ctxLitU 275600000000 3 ((leaves.drop 10366).take 34) 138156250000 2 = true :=
    take_step (n := 2) (t := 34) (b := 10368) rfl rfl ArealUCore.ArealUK.chunk_5183 s84
  have s82 : leavesOK ctxLitU 275550000000 3 ((leaves.drop 10364).take 36) 138156250000 2 = true :=
    take_step (n := 2) (t := 36) (b := 10366) rfl rfl ArealUCore.ArealUK.chunk_5182 s83
  have s81 : leavesOK ctxLitU 275500000000 3 ((leaves.drop 10362).take 38) 138156250000 2 = true :=
    take_step (n := 2) (t := 38) (b := 10364) rfl rfl ArealUCore.ArealUK.chunk_5181 s82
  have s80 : leavesOK ctxLitU 275450000000 3 ((leaves.drop 10360).take 40) 138156250000 2 = true :=
    take_step (n := 2) (t := 40) (b := 10362) rfl rfl ArealUCore.ArealUK.chunk_5180 s81
  have s79 : leavesOK ctxLitU 275400000000 3 ((leaves.drop 10358).take 42) 138156250000 2 = true :=
    take_step (n := 2) (t := 42) (b := 10360) rfl rfl ArealUCore.ArealUK.chunk_5179 s80
  have s78 : leavesOK ctxLitU 275350000000 3 ((leaves.drop 10356).take 44) 138156250000 2 = true :=
    take_step (n := 2) (t := 44) (b := 10358) rfl rfl ArealUCore.ArealUK.chunk_5178 s79
  have s77 : leavesOK ctxLitU 275300000000 3 ((leaves.drop 10354).take 46) 138156250000 2 = true :=
    take_step (n := 2) (t := 46) (b := 10356) rfl rfl ArealUCore.ArealUK.chunk_5177 s78
  have s76 : leavesOK ctxLitU 275250000000 3 ((leaves.drop 10352).take 48) 138156250000 2 = true :=
    take_step (n := 2) (t := 48) (b := 10354) rfl rfl ArealUCore.ArealUK.chunk_5176 s77
  have s75 : leavesOK ctxLitU 275200000000 3 ((leaves.drop 10350).take 50) 138156250000 2 = true :=
    take_step (n := 2) (t := 50) (b := 10352) rfl rfl ArealUCore.ArealUK.chunk_5175 s76
  have s74 : leavesOK ctxLitU 275150000000 3 ((leaves.drop 10348).take 52) 138156250000 2 = true :=
    take_step (n := 2) (t := 52) (b := 10350) rfl rfl ArealUCore.ArealUK.chunk_5174 s75
  have s73 : leavesOK ctxLitU 275100000000 3 ((leaves.drop 10346).take 54) 138156250000 2 = true :=
    take_step (n := 2) (t := 54) (b := 10348) rfl rfl ArealUCore.ArealUK.chunk_5173 s74
  have s72 : leavesOK ctxLitU 275050000000 3 ((leaves.drop 10344).take 56) 138156250000 2 = true :=
    take_step (n := 2) (t := 56) (b := 10346) rfl rfl ArealUCore.ArealUK.chunk_5172 s73
  have s71 : leavesOK ctxLitU 275000000000 3 ((leaves.drop 10342).take 58) 138156250000 2 = true :=
    take_step (n := 2) (t := 58) (b := 10344) rfl rfl ArealUCore.ArealUK.chunk_5171 s72
  have s70 : leavesOK ctxLitU 274950000000 3 ((leaves.drop 10340).take 60) 138156250000 2 = true :=
    take_step (n := 2) (t := 60) (b := 10342) rfl rfl ArealUCore.ArealUK.chunk_5170 s71
  have s69 : leavesOK ctxLitU 549850000000 4 ((leaves.drop 10338).take 62) 138156250000 2 = true :=
    take_step (n := 2) (t := 62) (b := 10340) rfl rfl ArealUCore.ArealUK.chunk_5169 s70
  have s68 : leavesOK ctxLitU 549800000000 4 ((leaves.drop 10336).take 64) 138156250000 2 = true :=
    take_step (n := 2) (t := 64) (b := 10338) rfl rfl ArealUCore.ArealUK.chunk_5168 s69
  have s67 : leavesOK ctxLitU 549750000000 4 ((leaves.drop 10334).take 66) 138156250000 2 = true :=
    take_step (n := 2) (t := 66) (b := 10336) rfl rfl ArealUCore.ArealUK.chunk_5167 s68
  have s66 : leavesOK ctxLitU 549700000000 4 ((leaves.drop 10332).take 68) 138156250000 2 = true :=
    take_step (n := 2) (t := 68) (b := 10334) rfl rfl ArealUCore.ArealUK.chunk_5166 s67
  have s65 : leavesOK ctxLitU 549650000000 4 ((leaves.drop 10330).take 70) 138156250000 2 = true :=
    take_step (n := 2) (t := 70) (b := 10332) rfl rfl ArealUCore.ArealUK.chunk_5165 s66
  have s64 : leavesOK ctxLitU 549600000000 4 ((leaves.drop 10328).take 72) 138156250000 2 = true :=
    take_step (n := 2) (t := 72) (b := 10330) rfl rfl ArealUCore.ArealUK.chunk_5164 s65
  have s63 : leavesOK ctxLitU 549550000000 4 ((leaves.drop 10326).take 74) 138156250000 2 = true :=
    take_step (n := 2) (t := 74) (b := 10328) rfl rfl ArealUCore.ArealUK.chunk_5163 s64
  have s62 : leavesOK ctxLitU 549500000000 4 ((leaves.drop 10324).take 76) 138156250000 2 = true :=
    take_step (n := 2) (t := 76) (b := 10326) rfl rfl ArealUCore.ArealUK.chunk_5162 s63
  have s61 : leavesOK ctxLitU 274700000000 3 ((leaves.drop 10322).take 78) 138156250000 2 = true :=
    take_step (n := 2) (t := 78) (b := 10324) rfl rfl ArealUCore.ArealUK.chunk_5161 s62
  have s60 : leavesOK ctxLitU 274650000000 3 ((leaves.drop 10320).take 80) 138156250000 2 = true :=
    take_step (n := 2) (t := 80) (b := 10322) rfl rfl ArealUCore.ArealUK.chunk_5160 s61
  have s59 : leavesOK ctxLitU 274600000000 3 ((leaves.drop 10318).take 82) 138156250000 2 = true :=
    take_step (n := 2) (t := 82) (b := 10320) rfl rfl ArealUCore.ArealUK.chunk_5159 s60
  have s58 : leavesOK ctxLitU 274550000000 3 ((leaves.drop 10316).take 84) 138156250000 2 = true :=
    take_step (n := 2) (t := 84) (b := 10318) rfl rfl ArealUCore.ArealUK.chunk_5158 s59
  have s57 : leavesOK ctxLitU 274500000000 3 ((leaves.drop 10314).take 86) 138156250000 2 = true :=
    take_step (n := 2) (t := 86) (b := 10316) rfl rfl ArealUCore.ArealUK.chunk_5157 s58
  have s56 : leavesOK ctxLitU 274450000000 3 ((leaves.drop 10312).take 88) 138156250000 2 = true :=
    take_step (n := 2) (t := 88) (b := 10314) rfl rfl ArealUCore.ArealUK.chunk_5156 s57
  have s55 : leavesOK ctxLitU 274400000000 3 ((leaves.drop 10310).take 90) 138156250000 2 = true :=
    take_step (n := 2) (t := 90) (b := 10312) rfl rfl ArealUCore.ArealUK.chunk_5155 s56
  have s54 : leavesOK ctxLitU 274350000000 3 ((leaves.drop 10308).take 92) 138156250000 2 = true :=
    take_step (n := 2) (t := 92) (b := 10310) rfl rfl ArealUCore.ArealUK.chunk_5154 s55
  have s53 : leavesOK ctxLitU 274300000000 3 ((leaves.drop 10306).take 94) 138156250000 2 = true :=
    take_step (n := 2) (t := 94) (b := 10308) rfl rfl ArealUCore.ArealUK.chunk_5153 s54
  have s52 : leavesOK ctxLitU 274250000000 3 ((leaves.drop 10304).take 96) 138156250000 2 = true :=
    take_step (n := 2) (t := 96) (b := 10306) rfl rfl ArealUCore.ArealUK.chunk_5152 s53
  have s51 : leavesOK ctxLitU 274200000000 3 ((leaves.drop 10302).take 98) 138156250000 2 = true :=
    take_step (n := 2) (t := 98) (b := 10304) rfl rfl ArealUCore.ArealUK.chunk_5151 s52
  have s50 : leavesOK ctxLitU 274150000000 3 ((leaves.drop 10300).take 100) 138156250000 2 = true :=
    take_step (n := 2) (t := 100) (b := 10302) rfl rfl ArealUCore.ArealUK.chunk_5150 s51
  have s49 : leavesOK ctxLitU 274100000000 3 ((leaves.drop 10298).take 102) 138156250000 2 = true :=
    take_step (n := 2) (t := 102) (b := 10300) rfl rfl ArealUCore.ArealUK.chunk_5149 s50
  have s48 : leavesOK ctxLitU 274050000000 3 ((leaves.drop 10296).take 104) 138156250000 2 = true :=
    take_step (n := 2) (t := 104) (b := 10298) rfl rfl ArealUCore.ArealUK.chunk_5148 s49
  have s47 : leavesOK ctxLitU 548050000000 4 ((leaves.drop 10294).take 106) 138156250000 2 = true :=
    take_step (n := 2) (t := 106) (b := 10296) rfl rfl ArealUCore.ArealUK.chunk_5147 s48
  have s46 : leavesOK ctxLitU 548000000000 4 ((leaves.drop 10292).take 108) 138156250000 2 = true :=
    take_step (n := 2) (t := 108) (b := 10294) rfl rfl ArealUCore.ArealUK.chunk_5146 s47
  have s45 : leavesOK ctxLitU 547950000000 4 ((leaves.drop 10290).take 110) 138156250000 2 = true :=
    take_step (n := 2) (t := 110) (b := 10292) rfl rfl ArealUCore.ArealUK.chunk_5145 s46
  have s44 : leavesOK ctxLitU 547900000000 4 ((leaves.drop 10288).take 112) 138156250000 2 = true :=
    take_step (n := 2) (t := 112) (b := 10290) rfl rfl ArealUCore.ArealUK.chunk_5144 s45
  have s43 : leavesOK ctxLitU 547850000000 4 ((leaves.drop 10286).take 114) 138156250000 2 = true :=
    take_step (n := 2) (t := 114) (b := 10288) rfl rfl ArealUCore.ArealUK.chunk_5143 s44
  have s42 : leavesOK ctxLitU 273875000000 3 ((leaves.drop 10284).take 116) 138156250000 2 = true :=
    take_step (n := 2) (t := 116) (b := 10286) rfl rfl ArealUCore.ArealUK.chunk_5142 s43
  have s41 : leavesOK ctxLitU 273825000000 3 ((leaves.drop 10282).take 118) 138156250000 2 = true :=
    take_step (n := 2) (t := 118) (b := 10284) rfl rfl ArealUCore.ArealUK.chunk_5141 s42
  have s40 : leavesOK ctxLitU 273775000000 3 ((leaves.drop 10280).take 120) 138156250000 2 = true :=
    take_step (n := 2) (t := 120) (b := 10282) rfl rfl ArealUCore.ArealUK.chunk_5140 s41
  have s39 : leavesOK ctxLitU 273725000000 3 ((leaves.drop 10278).take 122) 138156250000 2 = true :=
    take_step (n := 2) (t := 122) (b := 10280) rfl rfl ArealUCore.ArealUK.chunk_5139 s40
  have s38 : leavesOK ctxLitU 273675000000 3 ((leaves.drop 10276).take 124) 138156250000 2 = true :=
    take_step (n := 2) (t := 124) (b := 10278) rfl rfl ArealUCore.ArealUK.chunk_5138 s39
  have s37 : leavesOK ctxLitU 273625000000 3 ((leaves.drop 10274).take 126) 138156250000 2 = true :=
    take_step (n := 2) (t := 126) (b := 10276) rfl rfl ArealUCore.ArealUK.chunk_5137 s38
  have s36 : leavesOK ctxLitU 273575000000 3 ((leaves.drop 10272).take 128) 138156250000 2 = true :=
    take_step (n := 2) (t := 128) (b := 10274) rfl rfl ArealUCore.ArealUK.chunk_5136 s37
  have s35 : leavesOK ctxLitU 273525000000 3 ((leaves.drop 10270).take 130) 138156250000 2 = true :=
    take_step (n := 2) (t := 130) (b := 10272) rfl rfl ArealUCore.ArealUK.chunk_5135 s36
  have s34 : leavesOK ctxLitU 273475000000 3 ((leaves.drop 10268).take 132) 138156250000 2 = true :=
    take_step (n := 2) (t := 132) (b := 10270) rfl rfl ArealUCore.ArealUK.chunk_5134 s35
  have s33 : leavesOK ctxLitU 273425000000 3 ((leaves.drop 10266).take 134) 138156250000 2 = true :=
    take_step (n := 2) (t := 134) (b := 10268) rfl rfl ArealUCore.ArealUK.chunk_5133 s34
  have s32 : leavesOK ctxLitU 273375000000 3 ((leaves.drop 10264).take 136) 138156250000 2 = true :=
    take_step (n := 2) (t := 136) (b := 10266) rfl rfl ArealUCore.ArealUK.chunk_5132 s33
  have s31 : leavesOK ctxLitU 273325000000 3 ((leaves.drop 10262).take 138) 138156250000 2 = true :=
    take_step (n := 2) (t := 138) (b := 10264) rfl rfl ArealUCore.ArealUK.chunk_5131 s32
  have s30 : leavesOK ctxLitU 273275000000 3 ((leaves.drop 10260).take 140) 138156250000 2 = true :=
    take_step (n := 2) (t := 140) (b := 10262) rfl rfl ArealUCore.ArealUK.chunk_5130 s31
  have s29 : leavesOK ctxLitU 273225000000 3 ((leaves.drop 10258).take 142) 138156250000 2 = true :=
    take_step (n := 2) (t := 142) (b := 10260) rfl rfl ArealUCore.ArealUK.chunk_5129 s30
  have s28 : leavesOK ctxLitU 273175000000 3 ((leaves.drop 10256).take 144) 138156250000 2 = true :=
    take_step (n := 2) (t := 144) (b := 10258) rfl rfl ArealUCore.ArealUK.chunk_5128 s29
  have s27 : leavesOK ctxLitU 273125000000 3 ((leaves.drop 10254).take 146) 138156250000 2 = true :=
    take_step (n := 2) (t := 146) (b := 10256) rfl rfl ArealUCore.ArealUK.chunk_5127 s28
  have s26 : leavesOK ctxLitU 273075000000 3 ((leaves.drop 10252).take 148) 138156250000 2 = true :=
    take_step (n := 2) (t := 148) (b := 10254) rfl rfl ArealUCore.ArealUK.chunk_5126 s27
  have s25 : leavesOK ctxLitU 273025000000 3 ((leaves.drop 10250).take 150) 138156250000 2 = true :=
    take_step (n := 2) (t := 150) (b := 10252) rfl rfl ArealUCore.ArealUK.chunk_5125 s26
  have s24 : leavesOK ctxLitU 272975000000 3 ((leaves.drop 10248).take 152) 138156250000 2 = true :=
    take_step (n := 2) (t := 152) (b := 10250) rfl rfl ArealUCore.ArealUK.chunk_5124 s25
  have s23 : leavesOK ctxLitU 272925000000 3 ((leaves.drop 10246).take 154) 138156250000 2 = true :=
    take_step (n := 2) (t := 154) (b := 10248) rfl rfl ArealUCore.ArealUK.chunk_5123 s24
  have s22 : leavesOK ctxLitU 272875000000 3 ((leaves.drop 10244).take 156) 138156250000 2 = true :=
    take_step (n := 2) (t := 156) (b := 10246) rfl rfl ArealUCore.ArealUK.chunk_5122 s23
  have s21 : leavesOK ctxLitU 272825000000 3 ((leaves.drop 10242).take 158) 138156250000 2 = true :=
    take_step (n := 2) (t := 158) (b := 10244) rfl rfl ArealUCore.ArealUK.chunk_5121 s22
  have s20 : leavesOK ctxLitU 272775000000 3 ((leaves.drop 10240).take 160) 138156250000 2 = true :=
    take_step (n := 2) (t := 160) (b := 10242) rfl rfl ArealUCore.ArealUK.chunk_5120 s21
  have s19 : leavesOK ctxLitU 272725000000 3 ((leaves.drop 10238).take 162) 138156250000 2 = true :=
    take_step (n := 2) (t := 162) (b := 10240) rfl rfl ArealUCore.ArealUK.chunk_5119 s20
  have s18 : leavesOK ctxLitU 272675000000 3 ((leaves.drop 10236).take 164) 138156250000 2 = true :=
    take_step (n := 2) (t := 164) (b := 10238) rfl rfl ArealUCore.ArealUK.chunk_5118 s19
  have s17 : leavesOK ctxLitU 272625000000 3 ((leaves.drop 10234).take 166) 138156250000 2 = true :=
    take_step (n := 2) (t := 166) (b := 10236) rfl rfl ArealUCore.ArealUK.chunk_5117 s18
  have s16 : leavesOK ctxLitU 272575000000 3 ((leaves.drop 10232).take 168) 138156250000 2 = true :=
    take_step (n := 2) (t := 168) (b := 10234) rfl rfl ArealUCore.ArealUK.chunk_5116 s17
  have s15 : leavesOK ctxLitU 272525000000 3 ((leaves.drop 10230).take 170) 138156250000 2 = true :=
    take_step (n := 2) (t := 170) (b := 10232) rfl rfl ArealUCore.ArealUK.chunk_5115 s16
  have s14 : leavesOK ctxLitU 272475000000 3 ((leaves.drop 10228).take 172) 138156250000 2 = true :=
    take_step (n := 2) (t := 172) (b := 10230) rfl rfl ArealUCore.ArealUK.chunk_5114 s15
  have s13 : leavesOK ctxLitU 272425000000 3 ((leaves.drop 10226).take 174) 138156250000 2 = true :=
    take_step (n := 2) (t := 174) (b := 10228) rfl rfl ArealUCore.ArealUK.chunk_5113 s14
  have s12 : leavesOK ctxLitU 272375000000 3 ((leaves.drop 10224).take 176) 138156250000 2 = true :=
    take_step (n := 2) (t := 176) (b := 10226) rfl rfl ArealUCore.ArealUK.chunk_5112 s13
  have s11 : leavesOK ctxLitU 272325000000 3 ((leaves.drop 10222).take 178) 138156250000 2 = true :=
    take_step (n := 2) (t := 178) (b := 10224) rfl rfl ArealUCore.ArealUK.chunk_5111 s12
  have s10 : leavesOK ctxLitU 272275000000 3 ((leaves.drop 10220).take 180) 138156250000 2 = true :=
    take_step (n := 2) (t := 180) (b := 10222) rfl rfl ArealUCore.ArealUK.chunk_5110 s11
  have s9 : leavesOK ctxLitU 272225000000 3 ((leaves.drop 10218).take 182) 138156250000 2 = true :=
    take_step (n := 2) (t := 182) (b := 10220) rfl rfl ArealUCore.ArealUK.chunk_5109 s10
  have s8 : leavesOK ctxLitU 272175000000 3 ((leaves.drop 10216).take 184) 138156250000 2 = true :=
    take_step (n := 2) (t := 184) (b := 10218) rfl rfl ArealUCore.ArealUK.chunk_5108 s9
  have s7 : leavesOK ctxLitU 272125000000 3 ((leaves.drop 10214).take 186) 138156250000 2 = true :=
    take_step (n := 2) (t := 186) (b := 10216) rfl rfl ArealUCore.ArealUK.chunk_5107 s8
  have s6 : leavesOK ctxLitU 272075000000 3 ((leaves.drop 10212).take 188) 138156250000 2 = true :=
    take_step (n := 2) (t := 188) (b := 10214) rfl rfl ArealUCore.ArealUK.chunk_5106 s7
  have s5 : leavesOK ctxLitU 272025000000 3 ((leaves.drop 10210).take 190) 138156250000 2 = true :=
    take_step (n := 2) (t := 190) (b := 10212) rfl rfl ArealUCore.ArealUK.chunk_5105 s6
  have s4 : leavesOK ctxLitU 271975000000 3 ((leaves.drop 10208).take 192) 138156250000 2 = true :=
    take_step (n := 2) (t := 192) (b := 10210) rfl rfl ArealUCore.ArealUK.chunk_5104 s5
  have s3 : leavesOK ctxLitU 271925000000 3 ((leaves.drop 10206).take 194) 138156250000 2 = true :=
    take_step (n := 2) (t := 194) (b := 10208) rfl rfl ArealUCore.ArealUK.chunk_5103 s4
  have s2 : leavesOK ctxLitU 271875000000 3 ((leaves.drop 10204).take 196) 138156250000 2 = true :=
    take_step (n := 2) (t := 196) (b := 10206) rfl rfl ArealUCore.ArealUK.chunk_5102 s3
  have s1 : leavesOK ctxLitU 271825000000 3 ((leaves.drop 10202).take 198) 138156250000 2 = true :=
    take_step (n := 2) (t := 198) (b := 10204) rfl rfl ArealUCore.ArealUK.chunk_5101 s2
  have s0 : leavesOK ctxLitU 271775000000 3 ((leaves.drop 10200).take 200) 138156250000 2 = true :=
    take_step (n := 2) (t := 200) (b := 10202) rfl rfl ArealUCore.ArealUK.chunk_5100 s1
  exact s0

end Areal.UCert

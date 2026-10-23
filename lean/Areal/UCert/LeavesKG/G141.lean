import ArealUK.Chunk14100
import ArealUK.Chunk14101
import ArealUK.Chunk14102
import ArealUK.Chunk14103
import ArealUK.Chunk14104
import ArealUK.Chunk14105
import ArealUK.Chunk14106
import ArealUK.Chunk14107
import ArealUK.Chunk14108
import ArealUK.Chunk14109
import ArealUK.Chunk14110
import ArealUK.Chunk14111
import ArealUK.Chunk14112
import ArealUK.Chunk14113
import ArealUK.Chunk14114
import ArealUK.Chunk14115
import ArealUK.Chunk14116
import ArealUK.Chunk14117
import ArealUK.Chunk14118
import ArealUK.Chunk14119
import ArealUK.Chunk14120
import ArealUK.Chunk14121
import ArealUK.Chunk14122
import ArealUK.Chunk14123
import ArealUK.Chunk14124
import ArealUK.Chunk14125
import ArealUK.Chunk14126
import ArealUK.Chunk14127
import ArealUK.Chunk14128
import ArealUK.Chunk14129
import ArealUK.Chunk14130
import ArealUK.Chunk14131
import ArealUK.Chunk14132
import ArealUK.Chunk14133
import ArealUK.Chunk14134
import ArealUK.Chunk14135
import ArealUK.Chunk14136
import ArealUK.Chunk14137
import ArealUK.Chunk14138
import ArealUK.Chunk14139
import ArealUK.Chunk14140
import ArealUK.Chunk14141
import ArealUK.Chunk14142
import ArealUK.Chunk14143
import ArealUK.Chunk14144
import ArealUK.Chunk14145
import ArealUK.Chunk14146
import ArealUK.Chunk14147
import ArealUK.Chunk14148
import ArealUK.Chunk14149
import ArealUK.Chunk14150
import ArealUK.Chunk14151
import ArealUK.Chunk14152
import ArealUK.Chunk14153
import ArealUK.Chunk14154
import ArealUK.Chunk14155
import ArealUK.Chunk14156
import ArealUK.Chunk14157
import ArealUK.Chunk14158
import ArealUK.Chunk14159
import ArealUK.Chunk14160
import ArealUK.Chunk14161
import ArealUK.Chunk14162
import ArealUK.Chunk14163
import ArealUK.Chunk14164
import ArealUK.Chunk14165
import ArealUK.Chunk14166
import ArealUK.Chunk14167
import ArealUK.Chunk14168
import ArealUK.Chunk14169
import ArealUK.Chunk14170
import ArealUK.Chunk14171
import ArealUK.Chunk14172
import ArealUK.Chunk14173
import ArealUK.Chunk14174
import ArealUK.Chunk14175
import ArealUK.Chunk14176
import ArealUK.Chunk14177
import ArealUK.Chunk14178
import ArealUK.Chunk14179
import ArealUK.Chunk14180
import ArealUK.Chunk14181
import ArealUK.Chunk14182
import ArealUK.Chunk14183
import ArealUK.Chunk14184
import ArealUK.Chunk14185
import ArealUK.Chunk14186
import ArealUK.Chunk14187
import ArealUK.Chunk14188
import ArealUK.Chunk14189
import ArealUK.Chunk14190
import ArealUK.Chunk14191
import ArealUK.Chunk14192
import ArealUK.Chunk14193
import ArealUK.Chunk14194
import ArealUK.Chunk14195
import ArealUK.Chunk14196
import ArealUK.Chunk14197
import ArealUK.Chunk14198
import ArealUK.Chunk14199
import Areal.UCert.LeavesKGen

/-! Group 141 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_141 : leavesOK ctxLitU 290050000000 1 ((leaves.drop 28200).take 200) 584850000000 2 = true := by
  have s99 := ArealUCore.ArealUK.chunk_14199
  have s98 : leavesOK ctxLitU 292375000000 1 ((leaves.drop 28396).take 4) 584850000000 2 = true :=
    take_step (n := 2) (t := 4) (b := 28398) rfl rfl ArealUCore.ArealUK.chunk_14198 s99
  have s97 : leavesOK ctxLitU 292350000000 1 ((leaves.drop 28394).take 6) 584850000000 2 = true :=
    take_step (n := 2) (t := 6) (b := 28396) rfl rfl ArealUCore.ArealUK.chunk_14197 s98
  have s96 : leavesOK ctxLitU 292337500000 1 ((leaves.drop 28392).take 8) 584850000000 2 = true :=
    take_step (n := 2) (t := 8) (b := 28394) rfl rfl ArealUCore.ArealUK.chunk_14196 s97
  have s95 : leavesOK ctxLitU 292325000000 1 ((leaves.drop 28390).take 10) 584850000000 2 = true :=
    take_step (n := 2) (t := 10) (b := 28392) rfl rfl ArealUCore.ArealUK.chunk_14195 s96
  have s94 : leavesOK ctxLitU 146150000000 0 ((leaves.drop 28388).take 12) 584850000000 2 = true :=
    take_step (n := 2) (t := 12) (b := 28390) rfl rfl ArealUCore.ArealUK.chunk_14194 s95
  have s93 : leavesOK ctxLitU 292275000000 1 ((leaves.drop 28386).take 14) 584850000000 2 = true :=
    take_step (n := 2) (t := 14) (b := 28388) rfl rfl ArealUCore.ArealUK.chunk_14193 s94
  have s92 : leavesOK ctxLitU 292250000000 1 ((leaves.drop 28384).take 16) 584850000000 2 = true :=
    take_step (n := 2) (t := 16) (b := 28386) rfl rfl ArealUCore.ArealUK.chunk_14192 s93
  have s91 : leavesOK ctxLitU 584450000000 2 ((leaves.drop 28382).take 18) 584850000000 2 = true :=
    take_step (n := 2) (t := 18) (b := 28384) rfl rfl ArealUCore.ArealUK.chunk_14191 s92
  have s90 : leavesOK ctxLitU 584400000000 2 ((leaves.drop 28380).take 20) 584850000000 2 = true :=
    take_step (n := 2) (t := 20) (b := 28382) rfl rfl ArealUCore.ArealUK.chunk_14190 s91
  have s89 : leavesOK ctxLitU 292175000000 1 ((leaves.drop 28378).take 22) 584850000000 2 = true :=
    take_step (n := 2) (t := 22) (b := 28380) rfl rfl ArealUCore.ArealUK.chunk_14189 s90
  have s88 : leavesOK ctxLitU 292150000000 1 ((leaves.drop 28376).take 24) 584850000000 2 = true :=
    take_step (n := 2) (t := 24) (b := 28378) rfl rfl ArealUCore.ArealUK.chunk_14188 s89
  have s87 : leavesOK ctxLitU 146062500000 0 ((leaves.drop 28374).take 26) 584850000000 2 = true :=
    take_step (n := 2) (t := 26) (b := 28376) rfl rfl ArealUCore.ArealUK.chunk_14187 s88
  have s86 : leavesOK ctxLitU 146050000000 0 ((leaves.drop 28372).take 28) 584850000000 2 = true :=
    take_step (n := 2) (t := 28) (b := 28374) rfl rfl ArealUCore.ArealUK.chunk_14186 s87
  have s85 : leavesOK ctxLitU 146037500000 0 ((leaves.drop 28370).take 30) 584850000000 2 = true :=
    take_step (n := 2) (t := 30) (b := 28372) rfl rfl ArealUCore.ArealUK.chunk_14185 s86
  have s84 : leavesOK ctxLitU 292062500000 1 ((leaves.drop 28368).take 32) 584850000000 2 = true :=
    take_step (n := 2) (t := 32) (b := 28370) rfl rfl ArealUCore.ArealUK.chunk_14184 s85
  have s83 : leavesOK ctxLitU 292050000000 1 ((leaves.drop 28366).take 34) 584850000000 2 = true :=
    take_step (n := 2) (t := 34) (b := 28368) rfl rfl ArealUCore.ArealUK.chunk_14183 s84
  have s82 : leavesOK ctxLitU 292025000000 1 ((leaves.drop 28364).take 36) 584850000000 2 = true :=
    take_step (n := 2) (t := 36) (b := 28366) rfl rfl ArealUCore.ArealUK.chunk_14182 s83
  have s81 : leavesOK ctxLitU 292000000000 1 ((leaves.drop 28362).take 38) 584850000000 2 = true :=
    take_step (n := 2) (t := 38) (b := 28364) rfl rfl ArealUCore.ArealUK.chunk_14181 s82
  have s80 : leavesOK ctxLitU 291975000000 1 ((leaves.drop 28360).take 40) 584850000000 2 = true :=
    take_step (n := 2) (t := 40) (b := 28362) rfl rfl ArealUCore.ArealUK.chunk_14180 s81
  have s79 : leavesOK ctxLitU 291950000000 1 ((leaves.drop 28358).take 42) 584850000000 2 = true :=
    take_step (n := 2) (t := 42) (b := 28360) rfl rfl ArealUCore.ArealUK.chunk_14179 s80
  have s78 : leavesOK ctxLitU 291937500000 1 ((leaves.drop 28356).take 44) 584850000000 2 = true :=
    take_step (n := 2) (t := 44) (b := 28358) rfl rfl ArealUCore.ArealUK.chunk_14178 s79
  have s77 : leavesOK ctxLitU 291925000000 1 ((leaves.drop 28354).take 46) 584850000000 2 = true :=
    take_step (n := 2) (t := 46) (b := 28356) rfl rfl ArealUCore.ArealUK.chunk_14177 s78
  have s76 : leavesOK ctxLitU 145950000000 0 ((leaves.drop 28352).take 48) 584850000000 2 = true :=
    take_step (n := 2) (t := 48) (b := 28354) rfl rfl ArealUCore.ArealUK.chunk_14176 s77
  have s75 : leavesOK ctxLitU 145937500000 0 ((leaves.drop 28350).take 50) 584850000000 2 = true :=
    take_step (n := 2) (t := 50) (b := 28352) rfl rfl ArealUCore.ArealUK.chunk_14175 s76
  have s74 : leavesOK ctxLitU 145925000000 0 ((leaves.drop 28348).take 52) 584850000000 2 = true :=
    take_step (n := 2) (t := 52) (b := 28350) rfl rfl ArealUCore.ArealUK.chunk_14174 s75
  have s73 : leavesOK ctxLitU 291825000000 1 ((leaves.drop 28346).take 54) 584850000000 2 = true :=
    take_step (n := 2) (t := 54) (b := 28348) rfl rfl ArealUCore.ArealUK.chunk_14173 s74
  have s72 : leavesOK ctxLitU 291800000000 1 ((leaves.drop 28344).take 56) 584850000000 2 = true :=
    take_step (n := 2) (t := 56) (b := 28346) rfl rfl ArealUCore.ArealUK.chunk_14172 s73
  have s71 : leavesOK ctxLitU 583550000000 2 ((leaves.drop 28342).take 58) 584850000000 2 = true :=
    take_step (n := 2) (t := 58) (b := 28344) rfl rfl ArealUCore.ArealUK.chunk_14171 s72
  have s70 : leavesOK ctxLitU 583500000000 2 ((leaves.drop 28340).take 60) 584850000000 2 = true :=
    take_step (n := 2) (t := 60) (b := 28342) rfl rfl ArealUCore.ArealUK.chunk_14170 s71
  have s69 : leavesOK ctxLitU 291725000000 1 ((leaves.drop 28338).take 62) 584850000000 2 = true :=
    take_step (n := 2) (t := 62) (b := 28340) rfl rfl ArealUCore.ArealUK.chunk_14169 s70
  have s68 : leavesOK ctxLitU 291700000000 1 ((leaves.drop 28336).take 64) 584850000000 2 = true :=
    take_step (n := 2) (t := 64) (b := 28338) rfl rfl ArealUCore.ArealUK.chunk_14168 s69
  have s67 : leavesOK ctxLitU 145837500000 0 ((leaves.drop 28334).take 66) 584850000000 2 = true :=
    take_step (n := 2) (t := 66) (b := 28336) rfl rfl ArealUCore.ArealUK.chunk_14167 s68
  have s66 : leavesOK ctxLitU 145825000000 0 ((leaves.drop 28332).take 68) 584850000000 2 = true :=
    take_step (n := 2) (t := 68) (b := 28334) rfl rfl ArealUCore.ArealUK.chunk_14166 s67
  have s65 : leavesOK ctxLitU 291625000000 1 ((leaves.drop 28330).take 70) 584850000000 2 = true :=
    take_step (n := 2) (t := 70) (b := 28332) rfl rfl ArealUCore.ArealUK.chunk_14165 s66
  have s64 : leavesOK ctxLitU 291600000000 1 ((leaves.drop 28328).take 72) 584850000000 2 = true :=
    take_step (n := 2) (t := 72) (b := 28330) rfl rfl ArealUCore.ArealUK.chunk_14164 s65
  have s63 : leavesOK ctxLitU 291575000000 1 ((leaves.drop 28326).take 74) 584850000000 2 = true :=
    take_step (n := 2) (t := 74) (b := 28328) rfl rfl ArealUCore.ArealUK.chunk_14163 s64
  have s62 : leavesOK ctxLitU 291550000000 1 ((leaves.drop 28324).take 76) 584850000000 2 = true :=
    take_step (n := 2) (t := 76) (b := 28326) rfl rfl ArealUCore.ArealUK.chunk_14162 s63
  have s61 : leavesOK ctxLitU 145762500000 0 ((leaves.drop 28322).take 78) 584850000000 2 = true :=
    take_step (n := 2) (t := 78) (b := 28324) rfl rfl ArealUCore.ArealUK.chunk_14161 s62
  have s60 : leavesOK ctxLitU 145750000000 0 ((leaves.drop 28320).take 80) 584850000000 2 = true :=
    take_step (n := 2) (t := 80) (b := 28322) rfl rfl ArealUCore.ArealUK.chunk_14160 s61
  have s59 : leavesOK ctxLitU 145737500000 0 ((leaves.drop 28318).take 82) 584850000000 2 = true :=
    take_step (n := 2) (t := 82) (b := 28320) rfl rfl ArealUCore.ArealUK.chunk_14159 s60
  have s58 : leavesOK ctxLitU 145725000000 0 ((leaves.drop 28316).take 84) 584850000000 2 = true :=
    take_step (n := 2) (t := 84) (b := 28318) rfl rfl ArealUCore.ArealUK.chunk_14158 s59
  have s57 : leavesOK ctxLitU 291425000000 1 ((leaves.drop 28314).take 86) 584850000000 2 = true :=
    take_step (n := 2) (t := 86) (b := 28316) rfl rfl ArealUCore.ArealUK.chunk_14157 s58
  have s56 : leavesOK ctxLitU 291400000000 1 ((leaves.drop 28312).take 88) 584850000000 2 = true :=
    take_step (n := 2) (t := 88) (b := 28314) rfl rfl ArealUCore.ArealUK.chunk_14156 s57
  have s55 : leavesOK ctxLitU 291375000000 1 ((leaves.drop 28310).take 90) 584850000000 2 = true :=
    take_step (n := 2) (t := 90) (b := 28312) rfl rfl ArealUCore.ArealUK.chunk_14155 s56
  have s54 : leavesOK ctxLitU 291350000000 1 ((leaves.drop 28308).take 92) 584850000000 2 = true :=
    take_step (n := 2) (t := 92) (b := 28310) rfl rfl ArealUCore.ArealUK.chunk_14154 s55
  have s53 : leavesOK ctxLitU 145662500000 0 ((leaves.drop 28306).take 94) 584850000000 2 = true :=
    take_step (n := 2) (t := 94) (b := 28308) rfl rfl ArealUCore.ArealUK.chunk_14153 s54
  have s52 : leavesOK ctxLitU 145650000000 0 ((leaves.drop 28304).take 96) 584850000000 2 = true :=
    take_step (n := 2) (t := 96) (b := 28306) rfl rfl ArealUCore.ArealUK.chunk_14152 s53
  have s51 : leavesOK ctxLitU 145637500000 0 ((leaves.drop 28302).take 98) 584850000000 2 = true :=
    take_step (n := 2) (t := 98) (b := 28304) rfl rfl ArealUCore.ArealUK.chunk_14151 s52
  have s50 : leavesOK ctxLitU 291262500000 1 ((leaves.drop 28300).take 100) 584850000000 2 = true :=
    take_step (n := 2) (t := 100) (b := 28302) rfl rfl ArealUCore.ArealUK.chunk_14150 s51
  have s49 : leavesOK ctxLitU 291250000000 1 ((leaves.drop 28298).take 102) 584850000000 2 = true :=
    take_step (n := 2) (t := 102) (b := 28300) rfl rfl ArealUCore.ArealUK.chunk_14149 s50
  have s48 : leavesOK ctxLitU 291225000000 1 ((leaves.drop 28296).take 104) 584850000000 2 = true :=
    take_step (n := 2) (t := 104) (b := 28298) rfl rfl ArealUCore.ArealUK.chunk_14148 s49
  have s47 : leavesOK ctxLitU 291200000000 1 ((leaves.drop 28294).take 106) 584850000000 2 = true :=
    take_step (n := 2) (t := 106) (b := 28296) rfl rfl ArealUCore.ArealUK.chunk_14147 s48
  have s46 : leavesOK ctxLitU 291175000000 1 ((leaves.drop 28292).take 108) 584850000000 2 = true :=
    take_step (n := 2) (t := 108) (b := 28294) rfl rfl ArealUCore.ArealUK.chunk_14146 s47
  have s45 : leavesOK ctxLitU 291150000000 1 ((leaves.drop 28290).take 110) 584850000000 2 = true :=
    take_step (n := 2) (t := 110) (b := 28292) rfl rfl ArealUCore.ArealUK.chunk_14145 s46
  have s44 : leavesOK ctxLitU 145562500000 0 ((leaves.drop 28288).take 112) 584850000000 2 = true :=
    take_step (n := 2) (t := 112) (b := 28290) rfl rfl ArealUCore.ArealUK.chunk_14144 s45
  have s43 : leavesOK ctxLitU 145550000000 0 ((leaves.drop 28286).take 114) 584850000000 2 = true :=
    take_step (n := 2) (t := 114) (b := 28288) rfl rfl ArealUCore.ArealUK.chunk_14143 s44
  have s42 : leavesOK ctxLitU 291075000000 1 ((leaves.drop 28284).take 116) 584850000000 2 = true :=
    take_step (n := 2) (t := 116) (b := 28286) rfl rfl ArealUCore.ArealUK.chunk_14142 s43
  have s41 : leavesOK ctxLitU 291050000000 1 ((leaves.drop 28282).take 118) 584850000000 2 = true :=
    take_step (n := 2) (t := 118) (b := 28284) rfl rfl ArealUCore.ArealUK.chunk_14141 s42
  have s40 : leavesOK ctxLitU 582050000000 2 ((leaves.drop 28280).take 120) 584850000000 2 = true :=
    take_step (n := 2) (t := 120) (b := 28282) rfl rfl ArealUCore.ArealUK.chunk_14140 s41
  have s39 : leavesOK ctxLitU 582000000000 2 ((leaves.drop 28278).take 122) 584850000000 2 = true :=
    take_step (n := 2) (t := 122) (b := 28280) rfl rfl ArealUCore.ArealUK.chunk_14139 s40
  have s38 : leavesOK ctxLitU 581950000000 2 ((leaves.drop 28276).take 124) 584850000000 2 = true :=
    take_step (n := 2) (t := 124) (b := 28278) rfl rfl ArealUCore.ArealUK.chunk_14138 s39
  have s37 : leavesOK ctxLitU 581900000000 2 ((leaves.drop 28274).take 126) 584850000000 2 = true :=
    take_step (n := 2) (t := 126) (b := 28276) rfl rfl ArealUCore.ArealUK.chunk_14137 s38
  have s36 : leavesOK ctxLitU 290925000000 1 ((leaves.drop 28272).take 128) 584850000000 2 = true :=
    take_step (n := 2) (t := 128) (b := 28274) rfl rfl ArealUCore.ArealUK.chunk_14136 s37
  have s35 : leavesOK ctxLitU 290900000000 1 ((leaves.drop 28270).take 130) 584850000000 2 = true :=
    take_step (n := 2) (t := 130) (b := 28272) rfl rfl ArealUCore.ArealUK.chunk_14135 s36
  have s34 : leavesOK ctxLitU 145437500000 0 ((leaves.drop 28268).take 132) 584850000000 2 = true :=
    take_step (n := 2) (t := 132) (b := 28270) rfl rfl ArealUCore.ArealUK.chunk_14134 s35
  have s33 : leavesOK ctxLitU 145425000000 0 ((leaves.drop 28266).take 134) 584850000000 2 = true :=
    take_step (n := 2) (t := 134) (b := 28268) rfl rfl ArealUCore.ArealUK.chunk_14133 s34
  have s32 : leavesOK ctxLitU 290825000000 1 ((leaves.drop 28264).take 136) 584850000000 2 = true :=
    take_step (n := 2) (t := 136) (b := 28266) rfl rfl ArealUCore.ArealUK.chunk_14132 s33
  have s31 : leavesOK ctxLitU 290800000000 1 ((leaves.drop 28262).take 138) 584850000000 2 = true :=
    take_step (n := 2) (t := 138) (b := 28264) rfl rfl ArealUCore.ArealUK.chunk_14131 s32
  have s30 : leavesOK ctxLitU 290775000000 1 ((leaves.drop 28260).take 140) 584850000000 2 = true :=
    take_step (n := 2) (t := 140) (b := 28262) rfl rfl ArealUCore.ArealUK.chunk_14130 s31
  have s29 : leavesOK ctxLitU 290750000000 1 ((leaves.drop 28258).take 142) 584850000000 2 = true :=
    take_step (n := 2) (t := 142) (b := 28260) rfl rfl ArealUCore.ArealUK.chunk_14129 s30
  have s28 : leavesOK ctxLitU 145362500000 0 ((leaves.drop 28256).take 144) 584850000000 2 = true :=
    take_step (n := 2) (t := 144) (b := 28258) rfl rfl ArealUCore.ArealUK.chunk_14128 s29
  have s27 : leavesOK ctxLitU 145350000000 0 ((leaves.drop 28254).take 146) 584850000000 2 = true :=
    take_step (n := 2) (t := 146) (b := 28256) rfl rfl ArealUCore.ArealUK.chunk_14127 s28
  have s26 : leavesOK ctxLitU 145337500000 0 ((leaves.drop 28252).take 148) 584850000000 2 = true :=
    take_step (n := 2) (t := 148) (b := 28254) rfl rfl ArealUCore.ArealUK.chunk_14126 s27
  have s25 : leavesOK ctxLitU 145325000000 0 ((leaves.drop 28250).take 150) 584850000000 2 = true :=
    take_step (n := 2) (t := 150) (b := 28252) rfl rfl ArealUCore.ArealUK.chunk_14125 s26
  have s24 : leavesOK ctxLitU 290625000000 1 ((leaves.drop 28248).take 152) 584850000000 2 = true :=
    take_step (n := 2) (t := 152) (b := 28250) rfl rfl ArealUCore.ArealUK.chunk_14124 s25
  have s23 : leavesOK ctxLitU 290600000000 1 ((leaves.drop 28246).take 154) 584850000000 2 = true :=
    take_step (n := 2) (t := 154) (b := 28248) rfl rfl ArealUCore.ArealUK.chunk_14123 s24
  have s22 : leavesOK ctxLitU 290575000000 1 ((leaves.drop 28244).take 156) 584850000000 2 = true :=
    take_step (n := 2) (t := 156) (b := 28246) rfl rfl ArealUCore.ArealUK.chunk_14122 s23
  have s21 : leavesOK ctxLitU 290550000000 1 ((leaves.drop 28242).take 158) 584850000000 2 = true :=
    take_step (n := 2) (t := 158) (b := 28244) rfl rfl ArealUCore.ArealUK.chunk_14121 s22
  have s20 : leavesOK ctxLitU 145262500000 0 ((leaves.drop 28240).take 160) 584850000000 2 = true :=
    take_step (n := 2) (t := 160) (b := 28242) rfl rfl ArealUCore.ArealUK.chunk_14120 s21
  have s19 : leavesOK ctxLitU 145250000000 0 ((leaves.drop 28238).take 162) 584850000000 2 = true :=
    take_step (n := 2) (t := 162) (b := 28240) rfl rfl ArealUCore.ArealUK.chunk_14119 s20
  have s18 : leavesOK ctxLitU 145237500000 0 ((leaves.drop 28236).take 164) 584850000000 2 = true :=
    take_step (n := 2) (t := 164) (b := 28238) rfl rfl ArealUCore.ArealUK.chunk_14118 s19
  have s17 : leavesOK ctxLitU 145225000000 0 ((leaves.drop 28234).take 166) 584850000000 2 = true :=
    take_step (n := 2) (t := 166) (b := 28236) rfl rfl ArealUCore.ArealUK.chunk_14117 s18
  have s16 : leavesOK ctxLitU 290425000000 1 ((leaves.drop 28232).take 168) 584850000000 2 = true :=
    take_step (n := 2) (t := 168) (b := 28234) rfl rfl ArealUCore.ArealUK.chunk_14116 s17
  have s15 : leavesOK ctxLitU 290400000000 1 ((leaves.drop 28230).take 170) 584850000000 2 = true :=
    take_step (n := 2) (t := 170) (b := 28232) rfl rfl ArealUCore.ArealUK.chunk_14115 s16
  have s14 : leavesOK ctxLitU 580750000000 2 ((leaves.drop 28228).take 172) 584850000000 2 = true :=
    take_step (n := 2) (t := 172) (b := 28230) rfl rfl ArealUCore.ArealUK.chunk_14114 s15
  have s13 : leavesOK ctxLitU 580700000000 2 ((leaves.drop 28226).take 174) 584850000000 2 = true :=
    take_step (n := 2) (t := 174) (b := 28228) rfl rfl ArealUCore.ArealUK.chunk_14113 s14
  have s12 : leavesOK ctxLitU 580650000000 2 ((leaves.drop 28224).take 176) 584850000000 2 = true :=
    take_step (n := 2) (t := 176) (b := 28226) rfl rfl ArealUCore.ArealUK.chunk_14112 s13
  have s11 : leavesOK ctxLitU 580600000000 2 ((leaves.drop 28222).take 178) 584850000000 2 = true :=
    take_step (n := 2) (t := 178) (b := 28224) rfl rfl ArealUCore.ArealUK.chunk_14111 s12
  have s10 : leavesOK ctxLitU 580525000000 2 ((leaves.drop 28220).take 180) 584850000000 2 = true :=
    take_step (n := 2) (t := 180) (b := 28222) rfl rfl ArealUCore.ArealUK.chunk_14110 s11
  have s9 : leavesOK ctxLitU 580475000000 2 ((leaves.drop 28218).take 182) 584850000000 2 = true :=
    take_step (n := 2) (t := 182) (b := 28220) rfl rfl ArealUCore.ArealUK.chunk_14109 s10
  have s8 : leavesOK ctxLitU 580425000000 2 ((leaves.drop 28216).take 184) 584850000000 2 = true :=
    take_step (n := 2) (t := 184) (b := 28218) rfl rfl ArealUCore.ArealUK.chunk_14108 s9
  have s7 : leavesOK ctxLitU 290187500000 1 ((leaves.drop 28214).take 186) 584850000000 2 = true :=
    take_step (n := 2) (t := 186) (b := 28216) rfl rfl ArealUCore.ArealUK.chunk_14107 s8
  have s6 : leavesOK ctxLitU 580350000000 2 ((leaves.drop 28212).take 188) 584850000000 2 = true :=
    take_step (n := 2) (t := 188) (b := 28214) rfl rfl ArealUCore.ArealUK.chunk_14106 s7
  have s5 : leavesOK ctxLitU 580325000000 2 ((leaves.drop 28210).take 190) 584850000000 2 = true :=
    take_step (n := 2) (t := 190) (b := 28212) rfl rfl ArealUCore.ArealUK.chunk_14105 s6
  have s4 : leavesOK ctxLitU 145068750000 0 ((leaves.drop 28208).take 192) 584850000000 2 = true :=
    take_step (n := 2) (t := 192) (b := 28210) rfl rfl ArealUCore.ArealUK.chunk_14104 s5
  have s3 : leavesOK ctxLitU 145056250000 0 ((leaves.drop 28206).take 194) 584850000000 2 = true :=
    take_step (n := 2) (t := 194) (b := 28208) rfl rfl ArealUCore.ArealUK.chunk_14103 s4
  have s2 : leavesOK ctxLitU 145043750000 0 ((leaves.drop 28204).take 196) 584850000000 2 = true :=
    take_step (n := 2) (t := 196) (b := 28206) rfl rfl ArealUCore.ArealUK.chunk_14102 s3
  have s1 : leavesOK ctxLitU 145031250000 0 ((leaves.drop 28202).take 198) 584850000000 2 = true :=
    take_step (n := 2) (t := 198) (b := 28204) rfl rfl ArealUCore.ArealUK.chunk_14101 s2
  have s0 : leavesOK ctxLitU 290050000000 1 ((leaves.drop 28200).take 200) 584850000000 2 = true :=
    take_step (n := 2) (t := 200) (b := 28202) rfl rfl ArealUCore.ArealUK.chunk_14100 s1
  exact s0

end Areal.UCert

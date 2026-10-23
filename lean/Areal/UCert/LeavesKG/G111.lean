import ArealUK.Chunk11100
import ArealUK.Chunk11101
import ArealUK.Chunk11102
import ArealUK.Chunk11103
import ArealUK.Chunk11104
import ArealUK.Chunk11105
import ArealUK.Chunk11106
import ArealUK.Chunk11107
import ArealUK.Chunk11108
import ArealUK.Chunk11109
import ArealUK.Chunk11110
import ArealUK.Chunk11111
import ArealUK.Chunk11112
import ArealUK.Chunk11113
import ArealUK.Chunk11114
import ArealUK.Chunk11115
import ArealUK.Chunk11116
import ArealUK.Chunk11117
import ArealUK.Chunk11118
import ArealUK.Chunk11119
import ArealUK.Chunk11120
import ArealUK.Chunk11121
import ArealUK.Chunk11122
import ArealUK.Chunk11123
import ArealUK.Chunk11124
import ArealUK.Chunk11125
import ArealUK.Chunk11126
import ArealUK.Chunk11127
import ArealUK.Chunk11128
import ArealUK.Chunk11129
import ArealUK.Chunk11130
import ArealUK.Chunk11131
import ArealUK.Chunk11132
import ArealUK.Chunk11133
import ArealUK.Chunk11134
import ArealUK.Chunk11135
import ArealUK.Chunk11136
import ArealUK.Chunk11137
import ArealUK.Chunk11138
import ArealUK.Chunk11139
import ArealUK.Chunk11140
import ArealUK.Chunk11141
import ArealUK.Chunk11142
import ArealUK.Chunk11143
import ArealUK.Chunk11144
import ArealUK.Chunk11145
import ArealUK.Chunk11146
import ArealUK.Chunk11147
import ArealUK.Chunk11148
import ArealUK.Chunk11149
import ArealUK.Chunk11150
import ArealUK.Chunk11151
import ArealUK.Chunk11152
import ArealUK.Chunk11153
import ArealUK.Chunk11154
import ArealUK.Chunk11155
import ArealUK.Chunk11156
import ArealUK.Chunk11157
import ArealUK.Chunk11158
import ArealUK.Chunk11159
import ArealUK.Chunk11160
import ArealUK.Chunk11161
import ArealUK.Chunk11162
import ArealUK.Chunk11163
import ArealUK.Chunk11164
import ArealUK.Chunk11165
import ArealUK.Chunk11166
import ArealUK.Chunk11167
import ArealUK.Chunk11168
import ArealUK.Chunk11169
import ArealUK.Chunk11170
import ArealUK.Chunk11171
import ArealUK.Chunk11172
import ArealUK.Chunk11173
import ArealUK.Chunk11174
import ArealUK.Chunk11175
import ArealUK.Chunk11176
import ArealUK.Chunk11177
import ArealUK.Chunk11178
import ArealUK.Chunk11179
import ArealUK.Chunk11180
import ArealUK.Chunk11181
import ArealUK.Chunk11182
import ArealUK.Chunk11183
import ArealUK.Chunk11184
import ArealUK.Chunk11185
import ArealUK.Chunk11186
import ArealUK.Chunk11187
import ArealUK.Chunk11188
import ArealUK.Chunk11189
import ArealUK.Chunk11190
import ArealUK.Chunk11191
import ArealUK.Chunk11192
import ArealUK.Chunk11193
import ArealUK.Chunk11194
import ArealUK.Chunk11195
import ArealUK.Chunk11196
import ArealUK.Chunk11197
import ArealUK.Chunk11198
import ArealUK.Chunk11199
import Areal.UCert.LeavesKGen

/-! Group 111 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_111 : leavesOK ctxLitU 412900000000 2 ((leaves.drop 22200).take 200) 417900000000 2 = true := by
  have s99 := ArealUCore.ArealUK.chunk_11199
  have s98 : leavesOK ctxLitU 417800000000 2 ((leaves.drop 22396).take 4) 417900000000 2 = true :=
    take_step (n := 2) (t := 4) (b := 22398) rfl rfl ArealUCore.ArealUK.chunk_11198 s99
  have s97 : leavesOK ctxLitU 417750000000 2 ((leaves.drop 22394).take 6) 417900000000 2 = true :=
    take_step (n := 2) (t := 6) (b := 22396) rfl rfl ArealUCore.ArealUK.chunk_11197 s98
  have s96 : leavesOK ctxLitU 417700000000 2 ((leaves.drop 22392).take 8) 417900000000 2 = true :=
    take_step (n := 2) (t := 8) (b := 22394) rfl rfl ArealUCore.ArealUK.chunk_11196 s97
  have s95 : leavesOK ctxLitU 417650000000 2 ((leaves.drop 22390).take 10) 417900000000 2 = true :=
    take_step (n := 2) (t := 10) (b := 22392) rfl rfl ArealUCore.ArealUK.chunk_11195 s96
  have s94 : leavesOK ctxLitU 417600000000 2 ((leaves.drop 22388).take 12) 417900000000 2 = true :=
    take_step (n := 2) (t := 12) (b := 22390) rfl rfl ArealUCore.ArealUK.chunk_11194 s95
  have s93 : leavesOK ctxLitU 417550000000 2 ((leaves.drop 22386).take 14) 417900000000 2 = true :=
    take_step (n := 2) (t := 14) (b := 22388) rfl rfl ArealUCore.ArealUK.chunk_11193 s94
  have s92 : leavesOK ctxLitU 417500000000 2 ((leaves.drop 22384).take 16) 417900000000 2 = true :=
    take_step (n := 2) (t := 16) (b := 22386) rfl rfl ArealUCore.ArealUK.chunk_11192 s93
  have s91 : leavesOK ctxLitU 417450000000 2 ((leaves.drop 22382).take 18) 417900000000 2 = true :=
    take_step (n := 2) (t := 18) (b := 22384) rfl rfl ArealUCore.ArealUK.chunk_11191 s92
  have s90 : leavesOK ctxLitU 417400000000 2 ((leaves.drop 22380).take 20) 417900000000 2 = true :=
    take_step (n := 2) (t := 20) (b := 22382) rfl rfl ArealUCore.ArealUK.chunk_11190 s91
  have s89 : leavesOK ctxLitU 417350000000 2 ((leaves.drop 22378).take 22) 417900000000 2 = true :=
    take_step (n := 2) (t := 22) (b := 22380) rfl rfl ArealUCore.ArealUK.chunk_11189 s90
  have s88 : leavesOK ctxLitU 417300000000 2 ((leaves.drop 22376).take 24) 417900000000 2 = true :=
    take_step (n := 2) (t := 24) (b := 22378) rfl rfl ArealUCore.ArealUK.chunk_11188 s89
  have s87 : leavesOK ctxLitU 417250000000 2 ((leaves.drop 22374).take 26) 417900000000 2 = true :=
    take_step (n := 2) (t := 26) (b := 22376) rfl rfl ArealUCore.ArealUK.chunk_11187 s88
  have s86 : leavesOK ctxLitU 417200000000 2 ((leaves.drop 22372).take 28) 417900000000 2 = true :=
    take_step (n := 2) (t := 28) (b := 22374) rfl rfl ArealUCore.ArealUK.chunk_11186 s87
  have s85 : leavesOK ctxLitU 417150000000 2 ((leaves.drop 22370).take 30) 417900000000 2 = true :=
    take_step (n := 2) (t := 30) (b := 22372) rfl rfl ArealUCore.ArealUK.chunk_11185 s86
  have s84 : leavesOK ctxLitU 417100000000 2 ((leaves.drop 22368).take 32) 417900000000 2 = true :=
    take_step (n := 2) (t := 32) (b := 22370) rfl rfl ArealUCore.ArealUK.chunk_11184 s85
  have s83 : leavesOK ctxLitU 417050000000 2 ((leaves.drop 22366).take 34) 417900000000 2 = true :=
    take_step (n := 2) (t := 34) (b := 22368) rfl rfl ArealUCore.ArealUK.chunk_11183 s84
  have s82 : leavesOK ctxLitU 417000000000 2 ((leaves.drop 22364).take 36) 417900000000 2 = true :=
    take_step (n := 2) (t := 36) (b := 22366) rfl rfl ArealUCore.ArealUK.chunk_11182 s83
  have s81 : leavesOK ctxLitU 416950000000 2 ((leaves.drop 22362).take 38) 417900000000 2 = true :=
    take_step (n := 2) (t := 38) (b := 22364) rfl rfl ArealUCore.ArealUK.chunk_11181 s82
  have s80 : leavesOK ctxLitU 416900000000 2 ((leaves.drop 22360).take 40) 417900000000 2 = true :=
    take_step (n := 2) (t := 40) (b := 22362) rfl rfl ArealUCore.ArealUK.chunk_11180 s81
  have s79 : leavesOK ctxLitU 416850000000 2 ((leaves.drop 22358).take 42) 417900000000 2 = true :=
    take_step (n := 2) (t := 42) (b := 22360) rfl rfl ArealUCore.ArealUK.chunk_11179 s80
  have s78 : leavesOK ctxLitU 416800000000 2 ((leaves.drop 22356).take 44) 417900000000 2 = true :=
    take_step (n := 2) (t := 44) (b := 22358) rfl rfl ArealUCore.ArealUK.chunk_11178 s79
  have s77 : leavesOK ctxLitU 416750000000 2 ((leaves.drop 22354).take 46) 417900000000 2 = true :=
    take_step (n := 2) (t := 46) (b := 22356) rfl rfl ArealUCore.ArealUK.chunk_11177 s78
  have s76 : leavesOK ctxLitU 416700000000 2 ((leaves.drop 22352).take 48) 417900000000 2 = true :=
    take_step (n := 2) (t := 48) (b := 22354) rfl rfl ArealUCore.ArealUK.chunk_11176 s77
  have s75 : leavesOK ctxLitU 416650000000 2 ((leaves.drop 22350).take 50) 417900000000 2 = true :=
    take_step (n := 2) (t := 50) (b := 22352) rfl rfl ArealUCore.ArealUK.chunk_11175 s76
  have s74 : leavesOK ctxLitU 416600000000 2 ((leaves.drop 22348).take 52) 417900000000 2 = true :=
    take_step (n := 2) (t := 52) (b := 22350) rfl rfl ArealUCore.ArealUK.chunk_11174 s75
  have s73 : leavesOK ctxLitU 416550000000 2 ((leaves.drop 22346).take 54) 417900000000 2 = true :=
    take_step (n := 2) (t := 54) (b := 22348) rfl rfl ArealUCore.ArealUK.chunk_11173 s74
  have s72 : leavesOK ctxLitU 416500000000 2 ((leaves.drop 22344).take 56) 417900000000 2 = true :=
    take_step (n := 2) (t := 56) (b := 22346) rfl rfl ArealUCore.ArealUK.chunk_11172 s73
  have s71 : leavesOK ctxLitU 416450000000 2 ((leaves.drop 22342).take 58) 417900000000 2 = true :=
    take_step (n := 2) (t := 58) (b := 22344) rfl rfl ArealUCore.ArealUK.chunk_11171 s72
  have s70 : leavesOK ctxLitU 416400000000 2 ((leaves.drop 22340).take 60) 417900000000 2 = true :=
    take_step (n := 2) (t := 60) (b := 22342) rfl rfl ArealUCore.ArealUK.chunk_11170 s71
  have s69 : leavesOK ctxLitU 416350000000 2 ((leaves.drop 22338).take 62) 417900000000 2 = true :=
    take_step (n := 2) (t := 62) (b := 22340) rfl rfl ArealUCore.ArealUK.chunk_11169 s70
  have s68 : leavesOK ctxLitU 416300000000 2 ((leaves.drop 22336).take 64) 417900000000 2 = true :=
    take_step (n := 2) (t := 64) (b := 22338) rfl rfl ArealUCore.ArealUK.chunk_11168 s69
  have s67 : leavesOK ctxLitU 416250000000 2 ((leaves.drop 22334).take 66) 417900000000 2 = true :=
    take_step (n := 2) (t := 66) (b := 22336) rfl rfl ArealUCore.ArealUK.chunk_11167 s68
  have s66 : leavesOK ctxLitU 416200000000 2 ((leaves.drop 22332).take 68) 417900000000 2 = true :=
    take_step (n := 2) (t := 68) (b := 22334) rfl rfl ArealUCore.ArealUK.chunk_11166 s67
  have s65 : leavesOK ctxLitU 416150000000 2 ((leaves.drop 22330).take 70) 417900000000 2 = true :=
    take_step (n := 2) (t := 70) (b := 22332) rfl rfl ArealUCore.ArealUK.chunk_11165 s66
  have s64 : leavesOK ctxLitU 416100000000 2 ((leaves.drop 22328).take 72) 417900000000 2 = true :=
    take_step (n := 2) (t := 72) (b := 22330) rfl rfl ArealUCore.ArealUK.chunk_11164 s65
  have s63 : leavesOK ctxLitU 416050000000 2 ((leaves.drop 22326).take 74) 417900000000 2 = true :=
    take_step (n := 2) (t := 74) (b := 22328) rfl rfl ArealUCore.ArealUK.chunk_11163 s64
  have s62 : leavesOK ctxLitU 416000000000 2 ((leaves.drop 22324).take 76) 417900000000 2 = true :=
    take_step (n := 2) (t := 76) (b := 22326) rfl rfl ArealUCore.ArealUK.chunk_11162 s63
  have s61 : leavesOK ctxLitU 415950000000 2 ((leaves.drop 22322).take 78) 417900000000 2 = true :=
    take_step (n := 2) (t := 78) (b := 22324) rfl rfl ArealUCore.ArealUK.chunk_11161 s62
  have s60 : leavesOK ctxLitU 415900000000 2 ((leaves.drop 22320).take 80) 417900000000 2 = true :=
    take_step (n := 2) (t := 80) (b := 22322) rfl rfl ArealUCore.ArealUK.chunk_11160 s61
  have s59 : leavesOK ctxLitU 415850000000 2 ((leaves.drop 22318).take 82) 417900000000 2 = true :=
    take_step (n := 2) (t := 82) (b := 22320) rfl rfl ArealUCore.ArealUK.chunk_11159 s60
  have s58 : leavesOK ctxLitU 415800000000 2 ((leaves.drop 22316).take 84) 417900000000 2 = true :=
    take_step (n := 2) (t := 84) (b := 22318) rfl rfl ArealUCore.ArealUK.chunk_11158 s59
  have s57 : leavesOK ctxLitU 415750000000 2 ((leaves.drop 22314).take 86) 417900000000 2 = true :=
    take_step (n := 2) (t := 86) (b := 22316) rfl rfl ArealUCore.ArealUK.chunk_11157 s58
  have s56 : leavesOK ctxLitU 415700000000 2 ((leaves.drop 22312).take 88) 417900000000 2 = true :=
    take_step (n := 2) (t := 88) (b := 22314) rfl rfl ArealUCore.ArealUK.chunk_11156 s57
  have s55 : leavesOK ctxLitU 415650000000 2 ((leaves.drop 22310).take 90) 417900000000 2 = true :=
    take_step (n := 2) (t := 90) (b := 22312) rfl rfl ArealUCore.ArealUK.chunk_11155 s56
  have s54 : leavesOK ctxLitU 415600000000 2 ((leaves.drop 22308).take 92) 417900000000 2 = true :=
    take_step (n := 2) (t := 92) (b := 22310) rfl rfl ArealUCore.ArealUK.chunk_11154 s55
  have s53 : leavesOK ctxLitU 415550000000 2 ((leaves.drop 22306).take 94) 417900000000 2 = true :=
    take_step (n := 2) (t := 94) (b := 22308) rfl rfl ArealUCore.ArealUK.chunk_11153 s54
  have s52 : leavesOK ctxLitU 415500000000 2 ((leaves.drop 22304).take 96) 417900000000 2 = true :=
    take_step (n := 2) (t := 96) (b := 22306) rfl rfl ArealUCore.ArealUK.chunk_11152 s53
  have s51 : leavesOK ctxLitU 415450000000 2 ((leaves.drop 22302).take 98) 417900000000 2 = true :=
    take_step (n := 2) (t := 98) (b := 22304) rfl rfl ArealUCore.ArealUK.chunk_11151 s52
  have s50 : leavesOK ctxLitU 415400000000 2 ((leaves.drop 22300).take 100) 417900000000 2 = true :=
    take_step (n := 2) (t := 100) (b := 22302) rfl rfl ArealUCore.ArealUK.chunk_11150 s51
  have s49 : leavesOK ctxLitU 415350000000 2 ((leaves.drop 22298).take 102) 417900000000 2 = true :=
    take_step (n := 2) (t := 102) (b := 22300) rfl rfl ArealUCore.ArealUK.chunk_11149 s50
  have s48 : leavesOK ctxLitU 415300000000 2 ((leaves.drop 22296).take 104) 417900000000 2 = true :=
    take_step (n := 2) (t := 104) (b := 22298) rfl rfl ArealUCore.ArealUK.chunk_11148 s49
  have s47 : leavesOK ctxLitU 415250000000 2 ((leaves.drop 22294).take 106) 417900000000 2 = true :=
    take_step (n := 2) (t := 106) (b := 22296) rfl rfl ArealUCore.ArealUK.chunk_11147 s48
  have s46 : leavesOK ctxLitU 415200000000 2 ((leaves.drop 22292).take 108) 417900000000 2 = true :=
    take_step (n := 2) (t := 108) (b := 22294) rfl rfl ArealUCore.ArealUK.chunk_11146 s47
  have s45 : leavesOK ctxLitU 415150000000 2 ((leaves.drop 22290).take 110) 417900000000 2 = true :=
    take_step (n := 2) (t := 110) (b := 22292) rfl rfl ArealUCore.ArealUK.chunk_11145 s46
  have s44 : leavesOK ctxLitU 415100000000 2 ((leaves.drop 22288).take 112) 417900000000 2 = true :=
    take_step (n := 2) (t := 112) (b := 22290) rfl rfl ArealUCore.ArealUK.chunk_11144 s45
  have s43 : leavesOK ctxLitU 415050000000 2 ((leaves.drop 22286).take 114) 417900000000 2 = true :=
    take_step (n := 2) (t := 114) (b := 22288) rfl rfl ArealUCore.ArealUK.chunk_11143 s44
  have s42 : leavesOK ctxLitU 415000000000 2 ((leaves.drop 22284).take 116) 417900000000 2 = true :=
    take_step (n := 2) (t := 116) (b := 22286) rfl rfl ArealUCore.ArealUK.chunk_11142 s43
  have s41 : leavesOK ctxLitU 414950000000 2 ((leaves.drop 22282).take 118) 417900000000 2 = true :=
    take_step (n := 2) (t := 118) (b := 22284) rfl rfl ArealUCore.ArealUK.chunk_11141 s42
  have s40 : leavesOK ctxLitU 414900000000 2 ((leaves.drop 22280).take 120) 417900000000 2 = true :=
    take_step (n := 2) (t := 120) (b := 22282) rfl rfl ArealUCore.ArealUK.chunk_11140 s41
  have s39 : leavesOK ctxLitU 414850000000 2 ((leaves.drop 22278).take 122) 417900000000 2 = true :=
    take_step (n := 2) (t := 122) (b := 22280) rfl rfl ArealUCore.ArealUK.chunk_11139 s40
  have s38 : leavesOK ctxLitU 414800000000 2 ((leaves.drop 22276).take 124) 417900000000 2 = true :=
    take_step (n := 2) (t := 124) (b := 22278) rfl rfl ArealUCore.ArealUK.chunk_11138 s39
  have s37 : leavesOK ctxLitU 414750000000 2 ((leaves.drop 22274).take 126) 417900000000 2 = true :=
    take_step (n := 2) (t := 126) (b := 22276) rfl rfl ArealUCore.ArealUK.chunk_11137 s38
  have s36 : leavesOK ctxLitU 414700000000 2 ((leaves.drop 22272).take 128) 417900000000 2 = true :=
    take_step (n := 2) (t := 128) (b := 22274) rfl rfl ArealUCore.ArealUK.chunk_11136 s37
  have s35 : leavesOK ctxLitU 414650000000 2 ((leaves.drop 22270).take 130) 417900000000 2 = true :=
    take_step (n := 2) (t := 130) (b := 22272) rfl rfl ArealUCore.ArealUK.chunk_11135 s36
  have s34 : leavesOK ctxLitU 414600000000 2 ((leaves.drop 22268).take 132) 417900000000 2 = true :=
    take_step (n := 2) (t := 132) (b := 22270) rfl rfl ArealUCore.ArealUK.chunk_11134 s35
  have s33 : leavesOK ctxLitU 414550000000 2 ((leaves.drop 22266).take 134) 417900000000 2 = true :=
    take_step (n := 2) (t := 134) (b := 22268) rfl rfl ArealUCore.ArealUK.chunk_11133 s34
  have s32 : leavesOK ctxLitU 414500000000 2 ((leaves.drop 22264).take 136) 417900000000 2 = true :=
    take_step (n := 2) (t := 136) (b := 22266) rfl rfl ArealUCore.ArealUK.chunk_11132 s33
  have s31 : leavesOK ctxLitU 414450000000 2 ((leaves.drop 22262).take 138) 417900000000 2 = true :=
    take_step (n := 2) (t := 138) (b := 22264) rfl rfl ArealUCore.ArealUK.chunk_11131 s32
  have s30 : leavesOK ctxLitU 414400000000 2 ((leaves.drop 22260).take 140) 417900000000 2 = true :=
    take_step (n := 2) (t := 140) (b := 22262) rfl rfl ArealUCore.ArealUK.chunk_11130 s31
  have s29 : leavesOK ctxLitU 414350000000 2 ((leaves.drop 22258).take 142) 417900000000 2 = true :=
    take_step (n := 2) (t := 142) (b := 22260) rfl rfl ArealUCore.ArealUK.chunk_11129 s30
  have s28 : leavesOK ctxLitU 414300000000 2 ((leaves.drop 22256).take 144) 417900000000 2 = true :=
    take_step (n := 2) (t := 144) (b := 22258) rfl rfl ArealUCore.ArealUK.chunk_11128 s29
  have s27 : leavesOK ctxLitU 414250000000 2 ((leaves.drop 22254).take 146) 417900000000 2 = true :=
    take_step (n := 2) (t := 146) (b := 22256) rfl rfl ArealUCore.ArealUK.chunk_11127 s28
  have s26 : leavesOK ctxLitU 414200000000 2 ((leaves.drop 22252).take 148) 417900000000 2 = true :=
    take_step (n := 2) (t := 148) (b := 22254) rfl rfl ArealUCore.ArealUK.chunk_11126 s27
  have s25 : leavesOK ctxLitU 414150000000 2 ((leaves.drop 22250).take 150) 417900000000 2 = true :=
    take_step (n := 2) (t := 150) (b := 22252) rfl rfl ArealUCore.ArealUK.chunk_11125 s26
  have s24 : leavesOK ctxLitU 414100000000 2 ((leaves.drop 22248).take 152) 417900000000 2 = true :=
    take_step (n := 2) (t := 152) (b := 22250) rfl rfl ArealUCore.ArealUK.chunk_11124 s25
  have s23 : leavesOK ctxLitU 414050000000 2 ((leaves.drop 22246).take 154) 417900000000 2 = true :=
    take_step (n := 2) (t := 154) (b := 22248) rfl rfl ArealUCore.ArealUK.chunk_11123 s24
  have s22 : leavesOK ctxLitU 414000000000 2 ((leaves.drop 22244).take 156) 417900000000 2 = true :=
    take_step (n := 2) (t := 156) (b := 22246) rfl rfl ArealUCore.ArealUK.chunk_11122 s23
  have s21 : leavesOK ctxLitU 413950000000 2 ((leaves.drop 22242).take 158) 417900000000 2 = true :=
    take_step (n := 2) (t := 158) (b := 22244) rfl rfl ArealUCore.ArealUK.chunk_11121 s22
  have s20 : leavesOK ctxLitU 413900000000 2 ((leaves.drop 22240).take 160) 417900000000 2 = true :=
    take_step (n := 2) (t := 160) (b := 22242) rfl rfl ArealUCore.ArealUK.chunk_11120 s21
  have s19 : leavesOK ctxLitU 413850000000 2 ((leaves.drop 22238).take 162) 417900000000 2 = true :=
    take_step (n := 2) (t := 162) (b := 22240) rfl rfl ArealUCore.ArealUK.chunk_11119 s20
  have s18 : leavesOK ctxLitU 413800000000 2 ((leaves.drop 22236).take 164) 417900000000 2 = true :=
    take_step (n := 2) (t := 164) (b := 22238) rfl rfl ArealUCore.ArealUK.chunk_11118 s19
  have s17 : leavesOK ctxLitU 413750000000 2 ((leaves.drop 22234).take 166) 417900000000 2 = true :=
    take_step (n := 2) (t := 166) (b := 22236) rfl rfl ArealUCore.ArealUK.chunk_11117 s18
  have s16 : leavesOK ctxLitU 413700000000 2 ((leaves.drop 22232).take 168) 417900000000 2 = true :=
    take_step (n := 2) (t := 168) (b := 22234) rfl rfl ArealUCore.ArealUK.chunk_11116 s17
  have s15 : leavesOK ctxLitU 413650000000 2 ((leaves.drop 22230).take 170) 417900000000 2 = true :=
    take_step (n := 2) (t := 170) (b := 22232) rfl rfl ArealUCore.ArealUK.chunk_11115 s16
  have s14 : leavesOK ctxLitU 413600000000 2 ((leaves.drop 22228).take 172) 417900000000 2 = true :=
    take_step (n := 2) (t := 172) (b := 22230) rfl rfl ArealUCore.ArealUK.chunk_11114 s15
  have s13 : leavesOK ctxLitU 413550000000 2 ((leaves.drop 22226).take 174) 417900000000 2 = true :=
    take_step (n := 2) (t := 174) (b := 22228) rfl rfl ArealUCore.ArealUK.chunk_11113 s14
  have s12 : leavesOK ctxLitU 413500000000 2 ((leaves.drop 22224).take 176) 417900000000 2 = true :=
    take_step (n := 2) (t := 176) (b := 22226) rfl rfl ArealUCore.ArealUK.chunk_11112 s13
  have s11 : leavesOK ctxLitU 413450000000 2 ((leaves.drop 22222).take 178) 417900000000 2 = true :=
    take_step (n := 2) (t := 178) (b := 22224) rfl rfl ArealUCore.ArealUK.chunk_11111 s12
  have s10 : leavesOK ctxLitU 413400000000 2 ((leaves.drop 22220).take 180) 417900000000 2 = true :=
    take_step (n := 2) (t := 180) (b := 22222) rfl rfl ArealUCore.ArealUK.chunk_11110 s11
  have s9 : leavesOK ctxLitU 413350000000 2 ((leaves.drop 22218).take 182) 417900000000 2 = true :=
    take_step (n := 2) (t := 182) (b := 22220) rfl rfl ArealUCore.ArealUK.chunk_11109 s10
  have s8 : leavesOK ctxLitU 413300000000 2 ((leaves.drop 22216).take 184) 417900000000 2 = true :=
    take_step (n := 2) (t := 184) (b := 22218) rfl rfl ArealUCore.ArealUK.chunk_11108 s9
  have s7 : leavesOK ctxLitU 413250000000 2 ((leaves.drop 22214).take 186) 417900000000 2 = true :=
    take_step (n := 2) (t := 186) (b := 22216) rfl rfl ArealUCore.ArealUK.chunk_11107 s8
  have s6 : leavesOK ctxLitU 413200000000 2 ((leaves.drop 22212).take 188) 417900000000 2 = true :=
    take_step (n := 2) (t := 188) (b := 22214) rfl rfl ArealUCore.ArealUK.chunk_11106 s7
  have s5 : leavesOK ctxLitU 413150000000 2 ((leaves.drop 22210).take 190) 417900000000 2 = true :=
    take_step (n := 2) (t := 190) (b := 22212) rfl rfl ArealUCore.ArealUK.chunk_11105 s6
  have s4 : leavesOK ctxLitU 413100000000 2 ((leaves.drop 22208).take 192) 417900000000 2 = true :=
    take_step (n := 2) (t := 192) (b := 22210) rfl rfl ArealUCore.ArealUK.chunk_11104 s5
  have s3 : leavesOK ctxLitU 413050000000 2 ((leaves.drop 22206).take 194) 417900000000 2 = true :=
    take_step (n := 2) (t := 194) (b := 22208) rfl rfl ArealUCore.ArealUK.chunk_11103 s4
  have s2 : leavesOK ctxLitU 413000000000 2 ((leaves.drop 22204).take 196) 417900000000 2 = true :=
    take_step (n := 2) (t := 196) (b := 22206) rfl rfl ArealUCore.ArealUK.chunk_11102 s3
  have s1 : leavesOK ctxLitU 412950000000 2 ((leaves.drop 22202).take 198) 417900000000 2 = true :=
    take_step (n := 2) (t := 198) (b := 22204) rfl rfl ArealUCore.ArealUK.chunk_11101 s2
  have s0 : leavesOK ctxLitU 412900000000 2 ((leaves.drop 22200).take 200) 417900000000 2 = true :=
    take_step (n := 2) (t := 200) (b := 22202) rfl rfl ArealUCore.ArealUK.chunk_11100 s1
  exact s0

end Areal.UCert

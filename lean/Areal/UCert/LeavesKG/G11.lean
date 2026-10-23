import ArealUK.Chunk1100
import ArealUK.Chunk1101
import ArealUK.Chunk1102
import ArealUK.Chunk1103
import ArealUK.Chunk1104
import ArealUK.Chunk1105
import ArealUK.Chunk1106
import ArealUK.Chunk1107
import ArealUK.Chunk1108
import ArealUK.Chunk1109
import ArealUK.Chunk1110
import ArealUK.Chunk1111
import ArealUK.Chunk1112
import ArealUK.Chunk1113
import ArealUK.Chunk1114
import ArealUK.Chunk1115
import ArealUK.Chunk1116
import ArealUK.Chunk1117
import ArealUK.Chunk1118
import ArealUK.Chunk1119
import ArealUK.Chunk1120
import ArealUK.Chunk1121
import ArealUK.Chunk1122
import ArealUK.Chunk1123
import ArealUK.Chunk1124
import ArealUK.Chunk1125
import ArealUK.Chunk1126
import ArealUK.Chunk1127
import ArealUK.Chunk1128
import ArealUK.Chunk1129
import ArealUK.Chunk1130
import ArealUK.Chunk1131
import ArealUK.Chunk1132
import ArealUK.Chunk1133
import ArealUK.Chunk1134
import ArealUK.Chunk1135
import ArealUK.Chunk1136
import ArealUK.Chunk1137
import ArealUK.Chunk1138
import ArealUK.Chunk1139
import ArealUK.Chunk1140
import ArealUK.Chunk1141
import ArealUK.Chunk1142
import ArealUK.Chunk1143
import ArealUK.Chunk1144
import ArealUK.Chunk1145
import ArealUK.Chunk1146
import ArealUK.Chunk1147
import ArealUK.Chunk1148
import ArealUK.Chunk1149
import ArealUK.Chunk1150
import ArealUK.Chunk1151
import ArealUK.Chunk1152
import ArealUK.Chunk1153
import ArealUK.Chunk1154
import ArealUK.Chunk1155
import ArealUK.Chunk1156
import ArealUK.Chunk1157
import ArealUK.Chunk1158
import ArealUK.Chunk1159
import ArealUK.Chunk1160
import ArealUK.Chunk1161
import ArealUK.Chunk1162
import ArealUK.Chunk1163
import ArealUK.Chunk1164
import ArealUK.Chunk1165
import ArealUK.Chunk1166
import ArealUK.Chunk1167
import ArealUK.Chunk1168
import ArealUK.Chunk1169
import ArealUK.Chunk1170
import ArealUK.Chunk1171
import ArealUK.Chunk1172
import ArealUK.Chunk1173
import ArealUK.Chunk1174
import ArealUK.Chunk1175
import ArealUK.Chunk1176
import ArealUK.Chunk1177
import ArealUK.Chunk1178
import ArealUK.Chunk1179
import ArealUK.Chunk1180
import ArealUK.Chunk1181
import ArealUK.Chunk1182
import ArealUK.Chunk1183
import ArealUK.Chunk1184
import ArealUK.Chunk1185
import ArealUK.Chunk1186
import ArealUK.Chunk1187
import ArealUK.Chunk1188
import ArealUK.Chunk1189
import ArealUK.Chunk1190
import ArealUK.Chunk1191
import ArealUK.Chunk1192
import ArealUK.Chunk1193
import ArealUK.Chunk1194
import ArealUK.Chunk1195
import ArealUK.Chunk1196
import ArealUK.Chunk1197
import ArealUK.Chunk1198
import ArealUK.Chunk1199
import Areal.UCert.LeavesKGen

/-! Group 11 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_11 : leavesOK ctxLitU 43868750000 3 ((leaves.drop 2200).take 200) 45700000000 3 = true := by
  have s99 := ArealUCore.ArealUK.chunk_1199
  have s98 : leavesOK ctxLitU 45675000000 3 ((leaves.drop 2396).take 4) 45700000000 3 = true :=
    take_step (n := 2) (t := 4) (b := 2398) rfl rfl ArealUCore.ArealUK.chunk_1198 s99
  have s97 : leavesOK ctxLitU 45662500000 3 ((leaves.drop 2394).take 6) 45700000000 3 = true :=
    take_step (n := 2) (t := 6) (b := 2396) rfl rfl ArealUCore.ArealUK.chunk_1197 s98
  have s96 : leavesOK ctxLitU 45650000000 3 ((leaves.drop 2392).take 8) 45700000000 3 = true :=
    take_step (n := 2) (t := 8) (b := 2394) rfl rfl ArealUCore.ArealUK.chunk_1196 s97
  have s95 : leavesOK ctxLitU 45637500000 3 ((leaves.drop 2390).take 10) 45700000000 3 = true :=
    take_step (n := 2) (t := 10) (b := 2392) rfl rfl ArealUCore.ArealUK.chunk_1195 s96
  have s94 : leavesOK ctxLitU 91262500000 4 ((leaves.drop 2388).take 12) 45700000000 3 = true :=
    take_step (n := 2) (t := 12) (b := 2390) rfl rfl ArealUCore.ArealUK.chunk_1194 s95
  have s93 : leavesOK ctxLitU 91250000000 4 ((leaves.drop 2386).take 14) 45700000000 3 = true :=
    take_step (n := 2) (t := 14) (b := 2388) rfl rfl ArealUCore.ArealUK.chunk_1193 s94
  have s92 : leavesOK ctxLitU 91237500000 4 ((leaves.drop 2384).take 16) 45700000000 3 = true :=
    take_step (n := 2) (t := 16) (b := 2386) rfl rfl ArealUCore.ArealUK.chunk_1192 s93
  have s91 : leavesOK ctxLitU 45606250000 3 ((leaves.drop 2382).take 18) 45700000000 3 = true :=
    take_step (n := 2) (t := 18) (b := 2384) rfl rfl ArealUCore.ArealUK.chunk_1191 s92
  have s90 : leavesOK ctxLitU 45593750000 3 ((leaves.drop 2380).take 20) 45700000000 3 = true :=
    take_step (n := 2) (t := 20) (b := 2382) rfl rfl ArealUCore.ArealUK.chunk_1190 s91
  have s89 : leavesOK ctxLitU 22787500000 2 ((leaves.drop 2378).take 22) 45700000000 3 = true :=
    take_step (n := 2) (t := 22) (b := 2380) rfl rfl ArealUCore.ArealUK.chunk_1189 s90
  have s88 : leavesOK ctxLitU 22775000000 2 ((leaves.drop 2376).take 24) 45700000000 3 = true :=
    take_step (n := 2) (t := 24) (b := 2378) rfl rfl ArealUCore.ArealUK.chunk_1188 s89
  have s87 : leavesOK ctxLitU 45537500000 3 ((leaves.drop 2374).take 26) 45700000000 3 = true :=
    take_step (n := 2) (t := 26) (b := 2376) rfl rfl ArealUCore.ArealUK.chunk_1187 s88
  have s86 : leavesOK ctxLitU 91062500000 4 ((leaves.drop 2372).take 28) 45700000000 3 = true :=
    take_step (n := 2) (t := 28) (b := 2374) rfl rfl ArealUCore.ArealUK.chunk_1186 s87
  have s85 : leavesOK ctxLitU 91050000000 4 ((leaves.drop 2370).take 30) 45700000000 3 = true :=
    take_step (n := 2) (t := 30) (b := 2372) rfl rfl ArealUCore.ArealUK.chunk_1185 s86
  have s84 : leavesOK ctxLitU 45512500000 3 ((leaves.drop 2368).take 32) 45700000000 3 = true :=
    take_step (n := 2) (t := 32) (b := 2370) rfl rfl ArealUCore.ArealUK.chunk_1184 s85
  have s83 : leavesOK ctxLitU 45500000000 3 ((leaves.drop 2366).take 34) 45700000000 3 = true :=
    take_step (n := 2) (t := 34) (b := 2368) rfl rfl ArealUCore.ArealUK.chunk_1183 s84
  have s82 : leavesOK ctxLitU 11362500000 1 ((leaves.drop 2364).take 36) 45700000000 3 = true :=
    take_step (n := 2) (t := 36) (b := 2366) rfl rfl ArealUCore.ArealUK.chunk_1182 s83
  have s81 : leavesOK ctxLitU 23244434999736 12 ((leaves.drop 2362).take 38) 45700000000 3 = true :=
    take_step (n := 2) (t := 38) (b := 2364) rfl rfl ArealUCore.ArealUK.chunk_1181 s82
  have s80 : leavesOK ctxLitU 23219200000000 12 ((leaves.drop 2360).take 40) 45700000000 3 = true :=
    take_step (n := 2) (t := 40) (b := 2362) rfl rfl ArealUCore.ArealUK.chunk_1180 s81
  have s79 : leavesOK ctxLitU 11325000000 1 ((leaves.drop 2358).take 42) 45700000000 3 = true :=
    take_step (n := 2) (t := 42) (b := 2360) rfl rfl ArealUCore.ArealUK.chunk_1179 s80
  have s78 : leavesOK ctxLitU 45287500000 3 ((leaves.drop 2356).take 44) 45700000000 3 = true :=
    take_step (n := 2) (t := 44) (b := 2358) rfl rfl ArealUCore.ArealUK.chunk_1178 s79
  have s77 : leavesOK ctxLitU 45268750000 3 ((leaves.drop 2354).take 46) 45700000000 3 = true :=
    take_step (n := 2) (t := 46) (b := 2356) rfl rfl ArealUCore.ArealUK.chunk_1177 s78
  have s76 : leavesOK ctxLitU 90525000000 4 ((leaves.drop 2352).take 48) 45700000000 3 = true :=
    take_step (n := 2) (t := 48) (b := 2354) rfl rfl ArealUCore.ArealUK.chunk_1176 s77
  have s75 : leavesOK ctxLitU 45250000000 3 ((leaves.drop 2350).take 50) 45700000000 3 = true :=
    take_step (n := 2) (t := 50) (b := 2352) rfl rfl ArealUCore.ArealUK.chunk_1175 s76
  have s74 : leavesOK ctxLitU 22612500000 2 ((leaves.drop 2348).take 52) 45700000000 3 = true :=
    take_step (n := 2) (t := 52) (b := 2350) rfl rfl ArealUCore.ArealUK.chunk_1174 s75
  have s73 : leavesOK ctxLitU 45212500000 3 ((leaves.drop 2346).take 54) 45700000000 3 = true :=
    take_step (n := 2) (t := 54) (b := 2348) rfl rfl ArealUCore.ArealUK.chunk_1173 s74
  have s72 : leavesOK ctxLitU 45200000000 3 ((leaves.drop 2344).take 56) 45700000000 3 = true :=
    take_step (n := 2) (t := 56) (b := 2346) rfl rfl ArealUCore.ArealUK.chunk_1172 s73
  have s71 : leavesOK ctxLitU 45187500000 3 ((leaves.drop 2342).take 58) 45700000000 3 = true :=
    take_step (n := 2) (t := 58) (b := 2344) rfl rfl ArealUCore.ArealUK.chunk_1171 s72
  have s70 : leavesOK ctxLitU 45175000000 3 ((leaves.drop 2340).take 60) 45700000000 3 = true :=
    take_step (n := 2) (t := 60) (b := 2342) rfl rfl ArealUCore.ArealUK.chunk_1170 s71
  have s69 : leavesOK ctxLitU 45162500000 3 ((leaves.drop 2338).take 62) 45700000000 3 = true :=
    take_step (n := 2) (t := 62) (b := 2340) rfl rfl ArealUCore.ArealUK.chunk_1169 s70
  have s68 : leavesOK ctxLitU 45150000000 3 ((leaves.drop 2336).take 64) 45700000000 3 = true :=
    take_step (n := 2) (t := 64) (b := 2338) rfl rfl ArealUCore.ArealUK.chunk_1168 s69
  have s67 : leavesOK ctxLitU 45137500000 3 ((leaves.drop 2334).take 66) 45700000000 3 = true :=
    take_step (n := 2) (t := 66) (b := 2336) rfl rfl ArealUCore.ArealUK.chunk_1167 s68
  have s66 : leavesOK ctxLitU 45125000000 3 ((leaves.drop 2332).take 68) 45700000000 3 = true :=
    take_step (n := 2) (t := 68) (b := 2334) rfl rfl ArealUCore.ArealUK.chunk_1166 s67
  have s65 : leavesOK ctxLitU 45112500000 3 ((leaves.drop 2330).take 70) 45700000000 3 = true :=
    take_step (n := 2) (t := 70) (b := 2332) rfl rfl ArealUCore.ArealUK.chunk_1165 s66
  have s64 : leavesOK ctxLitU 45100000000 3 ((leaves.drop 2328).take 72) 45700000000 3 = true :=
    take_step (n := 2) (t := 72) (b := 2330) rfl rfl ArealUCore.ArealUK.chunk_1164 s65
  have s63 : leavesOK ctxLitU 45087500000 3 ((leaves.drop 2326).take 74) 45700000000 3 = true :=
    take_step (n := 2) (t := 74) (b := 2328) rfl rfl ArealUCore.ArealUK.chunk_1163 s64
  have s62 : leavesOK ctxLitU 45075000000 3 ((leaves.drop 2324).take 76) 45700000000 3 = true :=
    take_step (n := 2) (t := 76) (b := 2326) rfl rfl ArealUCore.ArealUK.chunk_1162 s63
  have s61 : leavesOK ctxLitU 45062500000 3 ((leaves.drop 2322).take 78) 45700000000 3 = true :=
    take_step (n := 2) (t := 78) (b := 2324) rfl rfl ArealUCore.ArealUK.chunk_1161 s62
  have s60 : leavesOK ctxLitU 45050000000 3 ((leaves.drop 2320).take 80) 45700000000 3 = true :=
    take_step (n := 2) (t := 80) (b := 2322) rfl rfl ArealUCore.ArealUK.chunk_1160 s61
  have s59 : leavesOK ctxLitU 45037500000 3 ((leaves.drop 2318).take 82) 45700000000 3 = true :=
    take_step (n := 2) (t := 82) (b := 2320) rfl rfl ArealUCore.ArealUK.chunk_1159 s60
  have s58 : leavesOK ctxLitU 45025000000 3 ((leaves.drop 2316).take 84) 45700000000 3 = true :=
    take_step (n := 2) (t := 84) (b := 2318) rfl rfl ArealUCore.ArealUK.chunk_1158 s59
  have s57 : leavesOK ctxLitU 45012500000 3 ((leaves.drop 2314).take 86) 45700000000 3 = true :=
    take_step (n := 2) (t := 86) (b := 2316) rfl rfl ArealUCore.ArealUK.chunk_1157 s58
  have s56 : leavesOK ctxLitU 45000000000 3 ((leaves.drop 2312).take 88) 45700000000 3 = true :=
    take_step (n := 2) (t := 88) (b := 2314) rfl rfl ArealUCore.ArealUK.chunk_1156 s57
  have s55 : leavesOK ctxLitU 44987500000 3 ((leaves.drop 2310).take 90) 45700000000 3 = true :=
    take_step (n := 2) (t := 90) (b := 2312) rfl rfl ArealUCore.ArealUK.chunk_1155 s56
  have s54 : leavesOK ctxLitU 44975000000 3 ((leaves.drop 2308).take 92) 45700000000 3 = true :=
    take_step (n := 2) (t := 92) (b := 2310) rfl rfl ArealUCore.ArealUK.chunk_1154 s55
  have s53 : leavesOK ctxLitU 44962500000 3 ((leaves.drop 2306).take 94) 45700000000 3 = true :=
    take_step (n := 2) (t := 94) (b := 2308) rfl rfl ArealUCore.ArealUK.chunk_1153 s54
  have s52 : leavesOK ctxLitU 44950000000 3 ((leaves.drop 2304).take 96) 45700000000 3 = true :=
    take_step (n := 2) (t := 96) (b := 2306) rfl rfl ArealUCore.ArealUK.chunk_1152 s53
  have s51 : leavesOK ctxLitU 44937500000 3 ((leaves.drop 2302).take 98) 45700000000 3 = true :=
    take_step (n := 2) (t := 98) (b := 2304) rfl rfl ArealUCore.ArealUK.chunk_1151 s52
  have s50 : leavesOK ctxLitU 44925000000 3 ((leaves.drop 2300).take 100) 45700000000 3 = true :=
    take_step (n := 2) (t := 100) (b := 2302) rfl rfl ArealUCore.ArealUK.chunk_1150 s51
  have s49 : leavesOK ctxLitU 44912500000 3 ((leaves.drop 2298).take 102) 45700000000 3 = true :=
    take_step (n := 2) (t := 102) (b := 2300) rfl rfl ArealUCore.ArealUK.chunk_1149 s50
  have s48 : leavesOK ctxLitU 44900000000 3 ((leaves.drop 2296).take 104) 45700000000 3 = true :=
    take_step (n := 2) (t := 104) (b := 2298) rfl rfl ArealUCore.ArealUK.chunk_1148 s49
  have s47 : leavesOK ctxLitU 22437500000 2 ((leaves.drop 2294).take 106) 45700000000 3 = true :=
    take_step (n := 2) (t := 106) (b := 2296) rfl rfl ArealUCore.ArealUK.chunk_1147 s48
  have s46 : leavesOK ctxLitU 22425000000 2 ((leaves.drop 2292).take 108) 45700000000 3 = true :=
    take_step (n := 2) (t := 108) (b := 2294) rfl rfl ArealUCore.ArealUK.chunk_1146 s47
  have s45 : leavesOK ctxLitU 22412500000 2 ((leaves.drop 2290).take 110) 45700000000 3 = true :=
    take_step (n := 2) (t := 110) (b := 2292) rfl rfl ArealUCore.ArealUK.chunk_1145 s46
  have s44 : leavesOK ctxLitU 44812500000 3 ((leaves.drop 2288).take 112) 45700000000 3 = true :=
    take_step (n := 2) (t := 112) (b := 2290) rfl rfl ArealUCore.ArealUK.chunk_1144 s45
  have s43 : leavesOK ctxLitU 89606250000 4 ((leaves.drop 2286).take 114) 45700000000 3 = true :=
    take_step (n := 2) (t := 114) (b := 2288) rfl rfl ArealUCore.ArealUK.chunk_1143 s44
  have s42 : leavesOK ctxLitU 91724562072709 14 ((leaves.drop 2284).take 116) 45700000000 3 = true :=
    take_step (n := 2) (t := 116) (b := 2286) rfl rfl ArealUCore.ArealUK.chunk_1142 s43
  have s41 : leavesOK ctxLitU 45823524145418 13 ((leaves.drop 2282).take 118) 45700000000 3 = true :=
    take_step (n := 2) (t := 118) (b := 2284) rfl rfl ArealUCore.ArealUK.chunk_1141 s42
  have s40 : leavesOK ctxLitU 45798162072706 13 ((leaves.drop 2280).take 120) 45700000000 3 = true :=
    take_step (n := 2) (t := 120) (b := 2282) rfl rfl ArealUCore.ArealUK.chunk_1140 s41
  have s39 : leavesOK ctxLitU 44687500000 3 ((leaves.drop 2278).take 122) 45700000000 3 = true :=
    take_step (n := 2) (t := 122) (b := 2280) rfl rfl ArealUCore.ArealUK.chunk_1139 s40
  have s38 : leavesOK ctxLitU 44662500000 3 ((leaves.drop 2276).take 124) 45700000000 3 = true :=
    take_step (n := 2) (t := 124) (b := 2278) rfl rfl ArealUCore.ArealUK.chunk_1138 s39
  have s37 : leavesOK ctxLitU 89300000000 4 ((leaves.drop 2274).take 126) 45700000000 3 = true :=
    take_step (n := 2) (t := 126) (b := 2276) rfl rfl ArealUCore.ArealUK.chunk_1137 s38
  have s36 : leavesOK ctxLitU 89275000000 4 ((leaves.drop 2272).take 128) 45700000000 3 = true :=
    take_step (n := 2) (t := 128) (b := 2274) rfl rfl ArealUCore.ArealUK.chunk_1136 s37
  have s35 : leavesOK ctxLitU 44612500000 3 ((leaves.drop 2270).take 130) 45700000000 3 = true :=
    take_step (n := 2) (t := 130) (b := 2272) rfl rfl ArealUCore.ArealUK.chunk_1135 s36
  have s34 : leavesOK ctxLitU 89175000000 4 ((leaves.drop 2268).take 132) 45700000000 3 = true :=
    take_step (n := 2) (t := 132) (b := 2270) rfl rfl ArealUCore.ArealUK.chunk_1134 s35
  have s33 : leavesOK ctxLitU 89125000000 4 ((leaves.drop 2266).take 134) 45700000000 3 = true :=
    take_step (n := 2) (t := 134) (b := 2268) rfl rfl ArealUCore.ArealUK.chunk_1133 s34
  have s32 : leavesOK ctxLitU 89075000000 4 ((leaves.drop 2264).take 136) 45700000000 3 = true :=
    take_step (n := 2) (t := 136) (b := 2266) rfl rfl ArealUCore.ArealUK.chunk_1132 s33
  have s31 : leavesOK ctxLitU 178075000000 5 ((leaves.drop 2262).take 138) 45700000000 3 = true :=
    take_step (n := 2) (t := 138) (b := 2264) rfl rfl ArealUCore.ArealUK.chunk_1131 s32
  have s30 : leavesOK ctxLitU 178025000000 5 ((leaves.drop 2260).take 140) 45700000000 3 = true :=
    take_step (n := 2) (t := 140) (b := 2262) rfl rfl ArealUCore.ArealUK.chunk_1130 s31
  have s29 : leavesOK ctxLitU 177975000000 5 ((leaves.drop 2258).take 142) 45700000000 3 = true :=
    take_step (n := 2) (t := 142) (b := 2260) rfl rfl ArealUCore.ArealUK.chunk_1129 s30
  have s28 : leavesOK ctxLitU 88950000000 4 ((leaves.drop 2256).take 144) 45700000000 3 = true :=
    take_step (n := 2) (t := 144) (b := 2258) rfl rfl ArealUCore.ArealUK.chunk_1128 s29
  have s27 : leavesOK ctxLitU 88900000000 4 ((leaves.drop 2254).take 146) 45700000000 3 = true :=
    take_step (n := 2) (t := 146) (b := 2256) rfl rfl ArealUCore.ArealUK.chunk_1127 s28
  have s26 : leavesOK ctxLitU 44400000000 3 ((leaves.drop 2252).take 148) 45700000000 3 = true :=
    take_step (n := 2) (t := 148) (b := 2254) rfl rfl ArealUCore.ArealUK.chunk_1126 s27
  have s25 : leavesOK ctxLitU 44375000000 3 ((leaves.drop 2250).take 150) 45700000000 3 = true :=
    take_step (n := 2) (t := 150) (b := 2252) rfl rfl ArealUCore.ArealUK.chunk_1125 s26
  have s24 : leavesOK ctxLitU 177462500000 5 ((leaves.drop 2248).take 152) 45700000000 3 = true :=
    take_step (n := 2) (t := 152) (b := 2250) rfl rfl ArealUCore.ArealUK.chunk_1124 s25
  have s23 : leavesOK ctxLitU 88712500000 4 ((leaves.drop 2246).take 154) 45700000000 3 = true :=
    take_step (n := 2) (t := 154) (b := 2248) rfl rfl ArealUCore.ArealUK.chunk_1123 s24
  have s22 : leavesOK ctxLitU 44337500000 3 ((leaves.drop 2244).take 156) 45700000000 3 = true :=
    take_step (n := 2) (t := 156) (b := 2246) rfl rfl ArealUCore.ArealUK.chunk_1122 s23
  have s21 : leavesOK ctxLitU 44312500000 3 ((leaves.drop 2242).take 158) 45700000000 3 = true :=
    take_step (n := 2) (t := 158) (b := 2244) rfl rfl ArealUCore.ArealUK.chunk_1121 s22
  have s20 : leavesOK ctxLitU 11062500000 1 ((leaves.drop 2240).take 160) 45700000000 3 = true :=
    take_step (n := 2) (t := 160) (b := 2242) rfl rfl ArealUCore.ArealUK.chunk_1120 s21
  have s19 : leavesOK ctxLitU 22628837434593 12 ((leaves.drop 2238).take 162) 45700000000 3 = true :=
    take_step (n := 2) (t := 162) (b := 2240) rfl rfl ArealUCore.ArealUK.chunk_1119 s20
  have s18 : leavesOK ctxLitU 22604800000000 12 ((leaves.drop 2236).take 164) 45700000000 3 = true :=
    take_step (n := 2) (t := 164) (b := 2238) rfl rfl ArealUCore.ArealUK.chunk_1118 s19
  have s17 : leavesOK ctxLitU 22056250000 2 ((leaves.drop 2234).take 166) 45700000000 3 = true :=
    take_step (n := 2) (t := 166) (b := 2236) rfl rfl ArealUCore.ArealUK.chunk_1117 s18
  have s16 : leavesOK ctxLitU 44093750000 3 ((leaves.drop 2232).take 168) 45700000000 3 = true :=
    take_step (n := 2) (t := 168) (b := 2234) rfl rfl ArealUCore.ArealUK.chunk_1116 s17
  have s15 : leavesOK ctxLitU 44081250000 3 ((leaves.drop 2230).take 170) 45700000000 3 = true :=
    take_step (n := 2) (t := 170) (b := 2232) rfl rfl ArealUCore.ArealUK.chunk_1115 s16
  have s14 : leavesOK ctxLitU 88143750000 4 ((leaves.drop 2228).take 172) 45700000000 3 = true :=
    take_step (n := 2) (t := 172) (b := 2230) rfl rfl ArealUCore.ArealUK.chunk_1114 s15
  have s13 : leavesOK ctxLitU 88131250000 4 ((leaves.drop 2226).take 174) 45700000000 3 = true :=
    take_step (n := 2) (t := 174) (b := 2228) rfl rfl ArealUCore.ArealUK.chunk_1113 s14
  have s12 : leavesOK ctxLitU 22025000000 2 ((leaves.drop 2224).take 176) 45700000000 3 = true :=
    take_step (n := 2) (t := 176) (b := 2226) rfl rfl ArealUCore.ArealUK.chunk_1112 s13
  have s11 : leavesOK ctxLitU 22012500000 2 ((leaves.drop 2222).take 178) 45700000000 3 = true :=
    take_step (n := 2) (t := 178) (b := 2224) rfl rfl ArealUCore.ArealUK.chunk_1111 s12
  have s10 : leavesOK ctxLitU 22000000000 2 ((leaves.drop 2220).take 180) 45700000000 3 = true :=
    take_step (n := 2) (t := 180) (b := 2222) rfl rfl ArealUCore.ArealUK.chunk_1110 s11
  have s9 : leavesOK ctxLitU 43987500000 3 ((leaves.drop 2218).take 182) 45700000000 3 = true :=
    take_step (n := 2) (t := 182) (b := 2220) rfl rfl ArealUCore.ArealUK.chunk_1109 s10
  have s8 : leavesOK ctxLitU 87956250000 4 ((leaves.drop 2216).take 184) 45700000000 3 = true :=
    take_step (n := 2) (t := 184) (b := 2218) rfl rfl ArealUCore.ArealUK.chunk_1108 s9
  have s7 : leavesOK ctxLitU 87943750000 4 ((leaves.drop 2214).take 186) 45700000000 3 = true :=
    take_step (n := 2) (t := 186) (b := 2216) rfl rfl ArealUCore.ArealUK.chunk_1107 s8
  have s6 : leavesOK ctxLitU 43962500000 3 ((leaves.drop 2212).take 188) 45700000000 3 = true :=
    take_step (n := 2) (t := 188) (b := 2214) rfl rfl ArealUCore.ArealUK.chunk_1106 s7
  have s5 : leavesOK ctxLitU 43950000000 3 ((leaves.drop 2210).take 190) 45700000000 3 = true :=
    take_step (n := 2) (t := 190) (b := 2212) rfl rfl ArealUCore.ArealUK.chunk_1105 s6
  have s4 : leavesOK ctxLitU 21962500000 2 ((leaves.drop 2208).take 192) 45700000000 3 = true :=
    take_step (n := 2) (t := 192) (b := 2210) rfl rfl ArealUCore.ArealUK.chunk_1104 s5
  have s3 : leavesOK ctxLitU 21950000000 2 ((leaves.drop 2206).take 194) 45700000000 3 = true :=
    take_step (n := 2) (t := 194) (b := 2208) rfl rfl ArealUCore.ArealUK.chunk_1103 s4
  have s2 : leavesOK ctxLitU 43887500000 3 ((leaves.drop 2204).take 196) 45700000000 3 = true :=
    take_step (n := 2) (t := 196) (b := 2206) rfl rfl ArealUCore.ArealUK.chunk_1102 s3
  have s1 : leavesOK ctxLitU 87756250000 4 ((leaves.drop 2202).take 198) 45700000000 3 = true :=
    take_step (n := 2) (t := 198) (b := 2204) rfl rfl ArealUCore.ArealUK.chunk_1101 s2
  have s0 : leavesOK ctxLitU 43868750000 3 ((leaves.drop 2200).take 200) 45700000000 3 = true :=
    take_step (n := 2) (t := 200) (b := 2202) rfl rfl ArealUCore.ArealUK.chunk_1100 s1
  exact s0

end Areal.UCert

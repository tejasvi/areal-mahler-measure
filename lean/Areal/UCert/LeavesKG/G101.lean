import ArealUK.Chunk10100
import ArealUK.Chunk10101
import ArealUK.Chunk10102
import ArealUK.Chunk10103
import ArealUK.Chunk10104
import ArealUK.Chunk10105
import ArealUK.Chunk10106
import ArealUK.Chunk10107
import ArealUK.Chunk10108
import ArealUK.Chunk10109
import ArealUK.Chunk10110
import ArealUK.Chunk10111
import ArealUK.Chunk10112
import ArealUK.Chunk10113
import ArealUK.Chunk10114
import ArealUK.Chunk10115
import ArealUK.Chunk10116
import ArealUK.Chunk10117
import ArealUK.Chunk10118
import ArealUK.Chunk10119
import ArealUK.Chunk10120
import ArealUK.Chunk10121
import ArealUK.Chunk10122
import ArealUK.Chunk10123
import ArealUK.Chunk10124
import ArealUK.Chunk10125
import ArealUK.Chunk10126
import ArealUK.Chunk10127
import ArealUK.Chunk10128
import ArealUK.Chunk10129
import ArealUK.Chunk10130
import ArealUK.Chunk10131
import ArealUK.Chunk10132
import ArealUK.Chunk10133
import ArealUK.Chunk10134
import ArealUK.Chunk10135
import ArealUK.Chunk10136
import ArealUK.Chunk10137
import ArealUK.Chunk10138
import ArealUK.Chunk10139
import ArealUK.Chunk10140
import ArealUK.Chunk10141
import ArealUK.Chunk10142
import ArealUK.Chunk10143
import ArealUK.Chunk10144
import ArealUK.Chunk10145
import ArealUK.Chunk10146
import ArealUK.Chunk10147
import ArealUK.Chunk10148
import ArealUK.Chunk10149
import ArealUK.Chunk10150
import ArealUK.Chunk10151
import ArealUK.Chunk10152
import ArealUK.Chunk10153
import ArealUK.Chunk10154
import ArealUK.Chunk10155
import ArealUK.Chunk10156
import ArealUK.Chunk10157
import ArealUK.Chunk10158
import ArealUK.Chunk10159
import ArealUK.Chunk10160
import ArealUK.Chunk10161
import ArealUK.Chunk10162
import ArealUK.Chunk10163
import ArealUK.Chunk10164
import ArealUK.Chunk10165
import ArealUK.Chunk10166
import ArealUK.Chunk10167
import ArealUK.Chunk10168
import ArealUK.Chunk10169
import ArealUK.Chunk10170
import ArealUK.Chunk10171
import ArealUK.Chunk10172
import ArealUK.Chunk10173
import ArealUK.Chunk10174
import ArealUK.Chunk10175
import ArealUK.Chunk10176
import ArealUK.Chunk10177
import ArealUK.Chunk10178
import ArealUK.Chunk10179
import ArealUK.Chunk10180
import ArealUK.Chunk10181
import ArealUK.Chunk10182
import ArealUK.Chunk10183
import ArealUK.Chunk10184
import ArealUK.Chunk10185
import ArealUK.Chunk10186
import ArealUK.Chunk10187
import ArealUK.Chunk10188
import ArealUK.Chunk10189
import ArealUK.Chunk10190
import ArealUK.Chunk10191
import ArealUK.Chunk10192
import ArealUK.Chunk10193
import ArealUK.Chunk10194
import ArealUK.Chunk10195
import ArealUK.Chunk10196
import ArealUK.Chunk10197
import ArealUK.Chunk10198
import ArealUK.Chunk10199
import Areal.UCert.LeavesKGen

/-! Group 101 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_101 : leavesOK ctxLitU 362175000000 2 ((leaves.drop 20200).take 200) 367175000000 2 = true := by
  have s99 := ArealUCore.ArealUK.chunk_10199
  have s98 : leavesOK ctxLitU 367075000000 2 ((leaves.drop 20396).take 4) 367175000000 2 = true :=
    take_step (n := 2) (t := 4) (b := 20398) rfl rfl ArealUCore.ArealUK.chunk_10198 s99
  have s97 : leavesOK ctxLitU 367025000000 2 ((leaves.drop 20394).take 6) 367175000000 2 = true :=
    take_step (n := 2) (t := 6) (b := 20396) rfl rfl ArealUCore.ArealUK.chunk_10197 s98
  have s96 : leavesOK ctxLitU 366975000000 2 ((leaves.drop 20392).take 8) 367175000000 2 = true :=
    take_step (n := 2) (t := 8) (b := 20394) rfl rfl ArealUCore.ArealUK.chunk_10196 s97
  have s95 : leavesOK ctxLitU 366925000000 2 ((leaves.drop 20390).take 10) 367175000000 2 = true :=
    take_step (n := 2) (t := 10) (b := 20392) rfl rfl ArealUCore.ArealUK.chunk_10195 s96
  have s94 : leavesOK ctxLitU 366875000000 2 ((leaves.drop 20388).take 12) 367175000000 2 = true :=
    take_step (n := 2) (t := 12) (b := 20390) rfl rfl ArealUCore.ArealUK.chunk_10194 s95
  have s93 : leavesOK ctxLitU 366825000000 2 ((leaves.drop 20386).take 14) 367175000000 2 = true :=
    take_step (n := 2) (t := 14) (b := 20388) rfl rfl ArealUCore.ArealUK.chunk_10193 s94
  have s92 : leavesOK ctxLitU 366775000000 2 ((leaves.drop 20384).take 16) 367175000000 2 = true :=
    take_step (n := 2) (t := 16) (b := 20386) rfl rfl ArealUCore.ArealUK.chunk_10192 s93
  have s91 : leavesOK ctxLitU 366725000000 2 ((leaves.drop 20382).take 18) 367175000000 2 = true :=
    take_step (n := 2) (t := 18) (b := 20384) rfl rfl ArealUCore.ArealUK.chunk_10191 s92
  have s90 : leavesOK ctxLitU 366675000000 2 ((leaves.drop 20380).take 20) 367175000000 2 = true :=
    take_step (n := 2) (t := 20) (b := 20382) rfl rfl ArealUCore.ArealUK.chunk_10190 s91
  have s89 : leavesOK ctxLitU 366625000000 2 ((leaves.drop 20378).take 22) 367175000000 2 = true :=
    take_step (n := 2) (t := 22) (b := 20380) rfl rfl ArealUCore.ArealUK.chunk_10189 s90
  have s88 : leavesOK ctxLitU 366575000000 2 ((leaves.drop 20376).take 24) 367175000000 2 = true :=
    take_step (n := 2) (t := 24) (b := 20378) rfl rfl ArealUCore.ArealUK.chunk_10188 s89
  have s87 : leavesOK ctxLitU 366525000000 2 ((leaves.drop 20374).take 26) 367175000000 2 = true :=
    take_step (n := 2) (t := 26) (b := 20376) rfl rfl ArealUCore.ArealUK.chunk_10187 s88
  have s86 : leavesOK ctxLitU 366475000000 2 ((leaves.drop 20372).take 28) 367175000000 2 = true :=
    take_step (n := 2) (t := 28) (b := 20374) rfl rfl ArealUCore.ArealUK.chunk_10186 s87
  have s85 : leavesOK ctxLitU 366425000000 2 ((leaves.drop 20370).take 30) 367175000000 2 = true :=
    take_step (n := 2) (t := 30) (b := 20372) rfl rfl ArealUCore.ArealUK.chunk_10185 s86
  have s84 : leavesOK ctxLitU 366375000000 2 ((leaves.drop 20368).take 32) 367175000000 2 = true :=
    take_step (n := 2) (t := 32) (b := 20370) rfl rfl ArealUCore.ArealUK.chunk_10184 s85
  have s83 : leavesOK ctxLitU 366325000000 2 ((leaves.drop 20366).take 34) 367175000000 2 = true :=
    take_step (n := 2) (t := 34) (b := 20368) rfl rfl ArealUCore.ArealUK.chunk_10183 s84
  have s82 : leavesOK ctxLitU 366275000000 2 ((leaves.drop 20364).take 36) 367175000000 2 = true :=
    take_step (n := 2) (t := 36) (b := 20366) rfl rfl ArealUCore.ArealUK.chunk_10182 s83
  have s81 : leavesOK ctxLitU 366225000000 2 ((leaves.drop 20362).take 38) 367175000000 2 = true :=
    take_step (n := 2) (t := 38) (b := 20364) rfl rfl ArealUCore.ArealUK.chunk_10181 s82
  have s80 : leavesOK ctxLitU 366175000000 2 ((leaves.drop 20360).take 40) 367175000000 2 = true :=
    take_step (n := 2) (t := 40) (b := 20362) rfl rfl ArealUCore.ArealUK.chunk_10180 s81
  have s79 : leavesOK ctxLitU 366125000000 2 ((leaves.drop 20358).take 42) 367175000000 2 = true :=
    take_step (n := 2) (t := 42) (b := 20360) rfl rfl ArealUCore.ArealUK.chunk_10179 s80
  have s78 : leavesOK ctxLitU 366075000000 2 ((leaves.drop 20356).take 44) 367175000000 2 = true :=
    take_step (n := 2) (t := 44) (b := 20358) rfl rfl ArealUCore.ArealUK.chunk_10178 s79
  have s77 : leavesOK ctxLitU 366025000000 2 ((leaves.drop 20354).take 46) 367175000000 2 = true :=
    take_step (n := 2) (t := 46) (b := 20356) rfl rfl ArealUCore.ArealUK.chunk_10177 s78
  have s76 : leavesOK ctxLitU 365975000000 2 ((leaves.drop 20352).take 48) 367175000000 2 = true :=
    take_step (n := 2) (t := 48) (b := 20354) rfl rfl ArealUCore.ArealUK.chunk_10176 s77
  have s75 : leavesOK ctxLitU 365925000000 2 ((leaves.drop 20350).take 50) 367175000000 2 = true :=
    take_step (n := 2) (t := 50) (b := 20352) rfl rfl ArealUCore.ArealUK.chunk_10175 s76
  have s74 : leavesOK ctxLitU 365875000000 2 ((leaves.drop 20348).take 52) 367175000000 2 = true :=
    take_step (n := 2) (t := 52) (b := 20350) rfl rfl ArealUCore.ArealUK.chunk_10174 s75
  have s73 : leavesOK ctxLitU 365825000000 2 ((leaves.drop 20346).take 54) 367175000000 2 = true :=
    take_step (n := 2) (t := 54) (b := 20348) rfl rfl ArealUCore.ArealUK.chunk_10173 s74
  have s72 : leavesOK ctxLitU 365775000000 2 ((leaves.drop 20344).take 56) 367175000000 2 = true :=
    take_step (n := 2) (t := 56) (b := 20346) rfl rfl ArealUCore.ArealUK.chunk_10172 s73
  have s71 : leavesOK ctxLitU 365725000000 2 ((leaves.drop 20342).take 58) 367175000000 2 = true :=
    take_step (n := 2) (t := 58) (b := 20344) rfl rfl ArealUCore.ArealUK.chunk_10171 s72
  have s70 : leavesOK ctxLitU 365675000000 2 ((leaves.drop 20340).take 60) 367175000000 2 = true :=
    take_step (n := 2) (t := 60) (b := 20342) rfl rfl ArealUCore.ArealUK.chunk_10170 s71
  have s69 : leavesOK ctxLitU 365625000000 2 ((leaves.drop 20338).take 62) 367175000000 2 = true :=
    take_step (n := 2) (t := 62) (b := 20340) rfl rfl ArealUCore.ArealUK.chunk_10169 s70
  have s68 : leavesOK ctxLitU 365575000000 2 ((leaves.drop 20336).take 64) 367175000000 2 = true :=
    take_step (n := 2) (t := 64) (b := 20338) rfl rfl ArealUCore.ArealUK.chunk_10168 s69
  have s67 : leavesOK ctxLitU 365525000000 2 ((leaves.drop 20334).take 66) 367175000000 2 = true :=
    take_step (n := 2) (t := 66) (b := 20336) rfl rfl ArealUCore.ArealUK.chunk_10167 s68
  have s66 : leavesOK ctxLitU 365475000000 2 ((leaves.drop 20332).take 68) 367175000000 2 = true :=
    take_step (n := 2) (t := 68) (b := 20334) rfl rfl ArealUCore.ArealUK.chunk_10166 s67
  have s65 : leavesOK ctxLitU 365425000000 2 ((leaves.drop 20330).take 70) 367175000000 2 = true :=
    take_step (n := 2) (t := 70) (b := 20332) rfl rfl ArealUCore.ArealUK.chunk_10165 s66
  have s64 : leavesOK ctxLitU 365375000000 2 ((leaves.drop 20328).take 72) 367175000000 2 = true :=
    take_step (n := 2) (t := 72) (b := 20330) rfl rfl ArealUCore.ArealUK.chunk_10164 s65
  have s63 : leavesOK ctxLitU 365325000000 2 ((leaves.drop 20326).take 74) 367175000000 2 = true :=
    take_step (n := 2) (t := 74) (b := 20328) rfl rfl ArealUCore.ArealUK.chunk_10163 s64
  have s62 : leavesOK ctxLitU 365275000000 2 ((leaves.drop 20324).take 76) 367175000000 2 = true :=
    take_step (n := 2) (t := 76) (b := 20326) rfl rfl ArealUCore.ArealUK.chunk_10162 s63
  have s61 : leavesOK ctxLitU 365225000000 2 ((leaves.drop 20322).take 78) 367175000000 2 = true :=
    take_step (n := 2) (t := 78) (b := 20324) rfl rfl ArealUCore.ArealUK.chunk_10161 s62
  have s60 : leavesOK ctxLitU 365175000000 2 ((leaves.drop 20320).take 80) 367175000000 2 = true :=
    take_step (n := 2) (t := 80) (b := 20322) rfl rfl ArealUCore.ArealUK.chunk_10160 s61
  have s59 : leavesOK ctxLitU 365125000000 2 ((leaves.drop 20318).take 82) 367175000000 2 = true :=
    take_step (n := 2) (t := 82) (b := 20320) rfl rfl ArealUCore.ArealUK.chunk_10159 s60
  have s58 : leavesOK ctxLitU 365075000000 2 ((leaves.drop 20316).take 84) 367175000000 2 = true :=
    take_step (n := 2) (t := 84) (b := 20318) rfl rfl ArealUCore.ArealUK.chunk_10158 s59
  have s57 : leavesOK ctxLitU 365025000000 2 ((leaves.drop 20314).take 86) 367175000000 2 = true :=
    take_step (n := 2) (t := 86) (b := 20316) rfl rfl ArealUCore.ArealUK.chunk_10157 s58
  have s56 : leavesOK ctxLitU 364975000000 2 ((leaves.drop 20312).take 88) 367175000000 2 = true :=
    take_step (n := 2) (t := 88) (b := 20314) rfl rfl ArealUCore.ArealUK.chunk_10156 s57
  have s55 : leavesOK ctxLitU 364925000000 2 ((leaves.drop 20310).take 90) 367175000000 2 = true :=
    take_step (n := 2) (t := 90) (b := 20312) rfl rfl ArealUCore.ArealUK.chunk_10155 s56
  have s54 : leavesOK ctxLitU 364875000000 2 ((leaves.drop 20308).take 92) 367175000000 2 = true :=
    take_step (n := 2) (t := 92) (b := 20310) rfl rfl ArealUCore.ArealUK.chunk_10154 s55
  have s53 : leavesOK ctxLitU 364825000000 2 ((leaves.drop 20306).take 94) 367175000000 2 = true :=
    take_step (n := 2) (t := 94) (b := 20308) rfl rfl ArealUCore.ArealUK.chunk_10153 s54
  have s52 : leavesOK ctxLitU 364775000000 2 ((leaves.drop 20304).take 96) 367175000000 2 = true :=
    take_step (n := 2) (t := 96) (b := 20306) rfl rfl ArealUCore.ArealUK.chunk_10152 s53
  have s51 : leavesOK ctxLitU 364725000000 2 ((leaves.drop 20302).take 98) 367175000000 2 = true :=
    take_step (n := 2) (t := 98) (b := 20304) rfl rfl ArealUCore.ArealUK.chunk_10151 s52
  have s50 : leavesOK ctxLitU 364675000000 2 ((leaves.drop 20300).take 100) 367175000000 2 = true :=
    take_step (n := 2) (t := 100) (b := 20302) rfl rfl ArealUCore.ArealUK.chunk_10150 s51
  have s49 : leavesOK ctxLitU 364625000000 2 ((leaves.drop 20298).take 102) 367175000000 2 = true :=
    take_step (n := 2) (t := 102) (b := 20300) rfl rfl ArealUCore.ArealUK.chunk_10149 s50
  have s48 : leavesOK ctxLitU 364575000000 2 ((leaves.drop 20296).take 104) 367175000000 2 = true :=
    take_step (n := 2) (t := 104) (b := 20298) rfl rfl ArealUCore.ArealUK.chunk_10148 s49
  have s47 : leavesOK ctxLitU 364525000000 2 ((leaves.drop 20294).take 106) 367175000000 2 = true :=
    take_step (n := 2) (t := 106) (b := 20296) rfl rfl ArealUCore.ArealUK.chunk_10147 s48
  have s46 : leavesOK ctxLitU 364475000000 2 ((leaves.drop 20292).take 108) 367175000000 2 = true :=
    take_step (n := 2) (t := 108) (b := 20294) rfl rfl ArealUCore.ArealUK.chunk_10146 s47
  have s45 : leavesOK ctxLitU 364425000000 2 ((leaves.drop 20290).take 110) 367175000000 2 = true :=
    take_step (n := 2) (t := 110) (b := 20292) rfl rfl ArealUCore.ArealUK.chunk_10145 s46
  have s44 : leavesOK ctxLitU 364375000000 2 ((leaves.drop 20288).take 112) 367175000000 2 = true :=
    take_step (n := 2) (t := 112) (b := 20290) rfl rfl ArealUCore.ArealUK.chunk_10144 s45
  have s43 : leavesOK ctxLitU 364325000000 2 ((leaves.drop 20286).take 114) 367175000000 2 = true :=
    take_step (n := 2) (t := 114) (b := 20288) rfl rfl ArealUCore.ArealUK.chunk_10143 s44
  have s42 : leavesOK ctxLitU 364275000000 2 ((leaves.drop 20284).take 116) 367175000000 2 = true :=
    take_step (n := 2) (t := 116) (b := 20286) rfl rfl ArealUCore.ArealUK.chunk_10142 s43
  have s41 : leavesOK ctxLitU 364225000000 2 ((leaves.drop 20282).take 118) 367175000000 2 = true :=
    take_step (n := 2) (t := 118) (b := 20284) rfl rfl ArealUCore.ArealUK.chunk_10141 s42
  have s40 : leavesOK ctxLitU 364175000000 2 ((leaves.drop 20280).take 120) 367175000000 2 = true :=
    take_step (n := 2) (t := 120) (b := 20282) rfl rfl ArealUCore.ArealUK.chunk_10140 s41
  have s39 : leavesOK ctxLitU 364125000000 2 ((leaves.drop 20278).take 122) 367175000000 2 = true :=
    take_step (n := 2) (t := 122) (b := 20280) rfl rfl ArealUCore.ArealUK.chunk_10139 s40
  have s38 : leavesOK ctxLitU 364075000000 2 ((leaves.drop 20276).take 124) 367175000000 2 = true :=
    take_step (n := 2) (t := 124) (b := 20278) rfl rfl ArealUCore.ArealUK.chunk_10138 s39
  have s37 : leavesOK ctxLitU 364025000000 2 ((leaves.drop 20274).take 126) 367175000000 2 = true :=
    take_step (n := 2) (t := 126) (b := 20276) rfl rfl ArealUCore.ArealUK.chunk_10137 s38
  have s36 : leavesOK ctxLitU 363975000000 2 ((leaves.drop 20272).take 128) 367175000000 2 = true :=
    take_step (n := 2) (t := 128) (b := 20274) rfl rfl ArealUCore.ArealUK.chunk_10136 s37
  have s35 : leavesOK ctxLitU 363925000000 2 ((leaves.drop 20270).take 130) 367175000000 2 = true :=
    take_step (n := 2) (t := 130) (b := 20272) rfl rfl ArealUCore.ArealUK.chunk_10135 s36
  have s34 : leavesOK ctxLitU 363875000000 2 ((leaves.drop 20268).take 132) 367175000000 2 = true :=
    take_step (n := 2) (t := 132) (b := 20270) rfl rfl ArealUCore.ArealUK.chunk_10134 s35
  have s33 : leavesOK ctxLitU 363825000000 2 ((leaves.drop 20266).take 134) 367175000000 2 = true :=
    take_step (n := 2) (t := 134) (b := 20268) rfl rfl ArealUCore.ArealUK.chunk_10133 s34
  have s32 : leavesOK ctxLitU 363775000000 2 ((leaves.drop 20264).take 136) 367175000000 2 = true :=
    take_step (n := 2) (t := 136) (b := 20266) rfl rfl ArealUCore.ArealUK.chunk_10132 s33
  have s31 : leavesOK ctxLitU 363725000000 2 ((leaves.drop 20262).take 138) 367175000000 2 = true :=
    take_step (n := 2) (t := 138) (b := 20264) rfl rfl ArealUCore.ArealUK.chunk_10131 s32
  have s30 : leavesOK ctxLitU 363675000000 2 ((leaves.drop 20260).take 140) 367175000000 2 = true :=
    take_step (n := 2) (t := 140) (b := 20262) rfl rfl ArealUCore.ArealUK.chunk_10130 s31
  have s29 : leavesOK ctxLitU 363625000000 2 ((leaves.drop 20258).take 142) 367175000000 2 = true :=
    take_step (n := 2) (t := 142) (b := 20260) rfl rfl ArealUCore.ArealUK.chunk_10129 s30
  have s28 : leavesOK ctxLitU 363575000000 2 ((leaves.drop 20256).take 144) 367175000000 2 = true :=
    take_step (n := 2) (t := 144) (b := 20258) rfl rfl ArealUCore.ArealUK.chunk_10128 s29
  have s27 : leavesOK ctxLitU 363525000000 2 ((leaves.drop 20254).take 146) 367175000000 2 = true :=
    take_step (n := 2) (t := 146) (b := 20256) rfl rfl ArealUCore.ArealUK.chunk_10127 s28
  have s26 : leavesOK ctxLitU 363475000000 2 ((leaves.drop 20252).take 148) 367175000000 2 = true :=
    take_step (n := 2) (t := 148) (b := 20254) rfl rfl ArealUCore.ArealUK.chunk_10126 s27
  have s25 : leavesOK ctxLitU 363425000000 2 ((leaves.drop 20250).take 150) 367175000000 2 = true :=
    take_step (n := 2) (t := 150) (b := 20252) rfl rfl ArealUCore.ArealUK.chunk_10125 s26
  have s24 : leavesOK ctxLitU 363375000000 2 ((leaves.drop 20248).take 152) 367175000000 2 = true :=
    take_step (n := 2) (t := 152) (b := 20250) rfl rfl ArealUCore.ArealUK.chunk_10124 s25
  have s23 : leavesOK ctxLitU 363325000000 2 ((leaves.drop 20246).take 154) 367175000000 2 = true :=
    take_step (n := 2) (t := 154) (b := 20248) rfl rfl ArealUCore.ArealUK.chunk_10123 s24
  have s22 : leavesOK ctxLitU 363275000000 2 ((leaves.drop 20244).take 156) 367175000000 2 = true :=
    take_step (n := 2) (t := 156) (b := 20246) rfl rfl ArealUCore.ArealUK.chunk_10122 s23
  have s21 : leavesOK ctxLitU 363225000000 2 ((leaves.drop 20242).take 158) 367175000000 2 = true :=
    take_step (n := 2) (t := 158) (b := 20244) rfl rfl ArealUCore.ArealUK.chunk_10121 s22
  have s20 : leavesOK ctxLitU 363175000000 2 ((leaves.drop 20240).take 160) 367175000000 2 = true :=
    take_step (n := 2) (t := 160) (b := 20242) rfl rfl ArealUCore.ArealUK.chunk_10120 s21
  have s19 : leavesOK ctxLitU 363125000000 2 ((leaves.drop 20238).take 162) 367175000000 2 = true :=
    take_step (n := 2) (t := 162) (b := 20240) rfl rfl ArealUCore.ArealUK.chunk_10119 s20
  have s18 : leavesOK ctxLitU 363075000000 2 ((leaves.drop 20236).take 164) 367175000000 2 = true :=
    take_step (n := 2) (t := 164) (b := 20238) rfl rfl ArealUCore.ArealUK.chunk_10118 s19
  have s17 : leavesOK ctxLitU 363025000000 2 ((leaves.drop 20234).take 166) 367175000000 2 = true :=
    take_step (n := 2) (t := 166) (b := 20236) rfl rfl ArealUCore.ArealUK.chunk_10117 s18
  have s16 : leavesOK ctxLitU 362975000000 2 ((leaves.drop 20232).take 168) 367175000000 2 = true :=
    take_step (n := 2) (t := 168) (b := 20234) rfl rfl ArealUCore.ArealUK.chunk_10116 s17
  have s15 : leavesOK ctxLitU 362925000000 2 ((leaves.drop 20230).take 170) 367175000000 2 = true :=
    take_step (n := 2) (t := 170) (b := 20232) rfl rfl ArealUCore.ArealUK.chunk_10115 s16
  have s14 : leavesOK ctxLitU 362875000000 2 ((leaves.drop 20228).take 172) 367175000000 2 = true :=
    take_step (n := 2) (t := 172) (b := 20230) rfl rfl ArealUCore.ArealUK.chunk_10114 s15
  have s13 : leavesOK ctxLitU 362825000000 2 ((leaves.drop 20226).take 174) 367175000000 2 = true :=
    take_step (n := 2) (t := 174) (b := 20228) rfl rfl ArealUCore.ArealUK.chunk_10113 s14
  have s12 : leavesOK ctxLitU 362775000000 2 ((leaves.drop 20224).take 176) 367175000000 2 = true :=
    take_step (n := 2) (t := 176) (b := 20226) rfl rfl ArealUCore.ArealUK.chunk_10112 s13
  have s11 : leavesOK ctxLitU 362725000000 2 ((leaves.drop 20222).take 178) 367175000000 2 = true :=
    take_step (n := 2) (t := 178) (b := 20224) rfl rfl ArealUCore.ArealUK.chunk_10111 s12
  have s10 : leavesOK ctxLitU 362675000000 2 ((leaves.drop 20220).take 180) 367175000000 2 = true :=
    take_step (n := 2) (t := 180) (b := 20222) rfl rfl ArealUCore.ArealUK.chunk_10110 s11
  have s9 : leavesOK ctxLitU 362625000000 2 ((leaves.drop 20218).take 182) 367175000000 2 = true :=
    take_step (n := 2) (t := 182) (b := 20220) rfl rfl ArealUCore.ArealUK.chunk_10109 s10
  have s8 : leavesOK ctxLitU 362575000000 2 ((leaves.drop 20216).take 184) 367175000000 2 = true :=
    take_step (n := 2) (t := 184) (b := 20218) rfl rfl ArealUCore.ArealUK.chunk_10108 s9
  have s7 : leavesOK ctxLitU 362525000000 2 ((leaves.drop 20214).take 186) 367175000000 2 = true :=
    take_step (n := 2) (t := 186) (b := 20216) rfl rfl ArealUCore.ArealUK.chunk_10107 s8
  have s6 : leavesOK ctxLitU 362475000000 2 ((leaves.drop 20212).take 188) 367175000000 2 = true :=
    take_step (n := 2) (t := 188) (b := 20214) rfl rfl ArealUCore.ArealUK.chunk_10106 s7
  have s5 : leavesOK ctxLitU 362425000000 2 ((leaves.drop 20210).take 190) 367175000000 2 = true :=
    take_step (n := 2) (t := 190) (b := 20212) rfl rfl ArealUCore.ArealUK.chunk_10105 s6
  have s4 : leavesOK ctxLitU 362375000000 2 ((leaves.drop 20208).take 192) 367175000000 2 = true :=
    take_step (n := 2) (t := 192) (b := 20210) rfl rfl ArealUCore.ArealUK.chunk_10104 s5
  have s3 : leavesOK ctxLitU 362325000000 2 ((leaves.drop 20206).take 194) 367175000000 2 = true :=
    take_step (n := 2) (t := 194) (b := 20208) rfl rfl ArealUCore.ArealUK.chunk_10103 s4
  have s2 : leavesOK ctxLitU 362275000000 2 ((leaves.drop 20204).take 196) 367175000000 2 = true :=
    take_step (n := 2) (t := 196) (b := 20206) rfl rfl ArealUCore.ArealUK.chunk_10102 s3
  have s1 : leavesOK ctxLitU 362225000000 2 ((leaves.drop 20202).take 198) 367175000000 2 = true :=
    take_step (n := 2) (t := 198) (b := 20204) rfl rfl ArealUCore.ArealUK.chunk_10101 s2
  have s0 : leavesOK ctxLitU 362175000000 2 ((leaves.drop 20200).take 200) 367175000000 2 = true :=
    take_step (n := 2) (t := 200) (b := 20202) rfl rfl ArealUCore.ArealUK.chunk_10100 s1
  exact s0

end Areal.UCert

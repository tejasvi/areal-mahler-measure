import ArealUK.Chunk2100
import ArealUK.Chunk2101
import ArealUK.Chunk2102
import ArealUK.Chunk2103
import ArealUK.Chunk2104
import ArealUK.Chunk2105
import ArealUK.Chunk2106
import ArealUK.Chunk2107
import ArealUK.Chunk2108
import ArealUK.Chunk2109
import ArealUK.Chunk2110
import ArealUK.Chunk2111
import ArealUK.Chunk2112
import ArealUK.Chunk2113
import ArealUK.Chunk2114
import ArealUK.Chunk2115
import ArealUK.Chunk2116
import ArealUK.Chunk2117
import ArealUK.Chunk2118
import ArealUK.Chunk2119
import ArealUK.Chunk2120
import ArealUK.Chunk2121
import ArealUK.Chunk2122
import ArealUK.Chunk2123
import ArealUK.Chunk2124
import ArealUK.Chunk2125
import ArealUK.Chunk2126
import ArealUK.Chunk2127
import ArealUK.Chunk2128
import ArealUK.Chunk2129
import ArealUK.Chunk2130
import ArealUK.Chunk2131
import ArealUK.Chunk2132
import ArealUK.Chunk2133
import ArealUK.Chunk2134
import ArealUK.Chunk2135
import ArealUK.Chunk2136
import ArealUK.Chunk2137
import ArealUK.Chunk2138
import ArealUK.Chunk2139
import ArealUK.Chunk2140
import ArealUK.Chunk2141
import ArealUK.Chunk2142
import ArealUK.Chunk2143
import ArealUK.Chunk2144
import ArealUK.Chunk2145
import ArealUK.Chunk2146
import ArealUK.Chunk2147
import ArealUK.Chunk2148
import ArealUK.Chunk2149
import ArealUK.Chunk2150
import ArealUK.Chunk2151
import ArealUK.Chunk2152
import ArealUK.Chunk2153
import ArealUK.Chunk2154
import ArealUK.Chunk2155
import ArealUK.Chunk2156
import ArealUK.Chunk2157
import ArealUK.Chunk2158
import ArealUK.Chunk2159
import ArealUK.Chunk2160
import ArealUK.Chunk2161
import ArealUK.Chunk2162
import ArealUK.Chunk2163
import ArealUK.Chunk2164
import ArealUK.Chunk2165
import ArealUK.Chunk2166
import ArealUK.Chunk2167
import ArealUK.Chunk2168
import ArealUK.Chunk2169
import ArealUK.Chunk2170
import ArealUK.Chunk2171
import ArealUK.Chunk2172
import ArealUK.Chunk2173
import ArealUK.Chunk2174
import ArealUK.Chunk2175
import ArealUK.Chunk2176
import ArealUK.Chunk2177
import ArealUK.Chunk2178
import ArealUK.Chunk2179
import ArealUK.Chunk2180
import ArealUK.Chunk2181
import ArealUK.Chunk2182
import ArealUK.Chunk2183
import ArealUK.Chunk2184
import ArealUK.Chunk2185
import ArealUK.Chunk2186
import ArealUK.Chunk2187
import ArealUK.Chunk2188
import ArealUK.Chunk2189
import ArealUK.Chunk2190
import ArealUK.Chunk2191
import ArealUK.Chunk2192
import ArealUK.Chunk2193
import ArealUK.Chunk2194
import ArealUK.Chunk2195
import ArealUK.Chunk2196
import ArealUK.Chunk2197
import ArealUK.Chunk2198
import ArealUK.Chunk2199
import Areal.UCert.LeavesKGen

/-! Group 21 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_21 : leavesOK ctxLitU 235200000000 4 ((leaves.drop 4200).take 200) 60018750000 2 = true := by
  have s99 := ArealUCore.ArealUK.chunk_2199
  have s98 : leavesOK ctxLitU 120012500000 3 ((leaves.drop 4396).take 4) 60018750000 2 = true :=
    take_step (n := 2) (t := 4) (b := 4398) rfl rfl ArealUCore.ArealUK.chunk_2198 s99
  have s97 : leavesOK ctxLitU 120000000000 3 ((leaves.drop 4394).take 6) 60018750000 2 = true :=
    take_step (n := 2) (t := 6) (b := 4396) rfl rfl ArealUCore.ArealUK.chunk_2197 s98
  have s96 : leavesOK ctxLitU 61435525926357 12 ((leaves.drop 4392).take 8) 60018750000 2 = true :=
    take_step (n := 2) (t := 8) (b := 4394) rfl rfl ArealUCore.ArealUK.chunk_2196 s97
  have s95 : leavesOK ctxLitU 122828800000000 13 ((leaves.drop 4390).take 10) 60018750000 2 = true :=
    take_step (n := 2) (t := 10) (b := 4392) rfl rfl ArealUCore.ArealUK.chunk_2195 s96
  have s94 : leavesOK ctxLitU 119931250000 3 ((leaves.drop 4388).take 12) 60018750000 2 = true :=
    take_step (n := 2) (t := 12) (b := 4390) rfl rfl ArealUCore.ArealUK.chunk_2194 s95
  have s93 : leavesOK ctxLitU 59956250000 2 ((leaves.drop 4386).take 14) 60018750000 2 = true :=
    take_step (n := 2) (t := 14) (b := 4388) rfl rfl ArealUCore.ArealUK.chunk_2193 s94
  have s92 : leavesOK ctxLitU 59943750000 2 ((leaves.drop 4384).take 16) 60018750000 2 = true :=
    take_step (n := 2) (t := 16) (b := 4386) rfl rfl ArealUCore.ArealUK.chunk_2192 s93
  have s91 : leavesOK ctxLitU 59931250000 2 ((leaves.drop 4382).take 18) 60018750000 2 = true :=
    take_step (n := 2) (t := 18) (b := 4384) rfl rfl ArealUCore.ArealUK.chunk_2191 s92
  have s90 : leavesOK ctxLitU 119843750000 3 ((leaves.drop 4380).take 20) 60018750000 2 = true :=
    take_step (n := 2) (t := 20) (b := 4382) rfl rfl ArealUCore.ArealUK.chunk_2190 s91
  have s89 : leavesOK ctxLitU 59912500000 2 ((leaves.drop 4378).take 22) 60018750000 2 = true :=
    take_step (n := 2) (t := 22) (b := 4380) rfl rfl ArealUCore.ArealUK.chunk_2189 s90
  have s88 : leavesOK ctxLitU 59900000000 2 ((leaves.drop 4376).take 24) 60018750000 2 = true :=
    take_step (n := 2) (t := 24) (b := 4378) rfl rfl ArealUCore.ArealUK.chunk_2188 s89
  have s87 : leavesOK ctxLitU 119775000000 3 ((leaves.drop 4374).take 26) 60018750000 2 = true :=
    take_step (n := 2) (t := 26) (b := 4376) rfl rfl ArealUCore.ArealUK.chunk_2187 s88
  have s86 : leavesOK ctxLitU 119750000000 3 ((leaves.drop 4372).take 28) 60018750000 2 = true :=
    take_step (n := 2) (t := 28) (b := 4374) rfl rfl ArealUCore.ArealUK.chunk_2186 s87
  have s85 : leavesOK ctxLitU 119725000000 3 ((leaves.drop 4370).take 30) 60018750000 2 = true :=
    take_step (n := 2) (t := 30) (b := 4372) rfl rfl ArealUCore.ArealUK.chunk_2185 s86
  have s84 : leavesOK ctxLitU 119700000000 3 ((leaves.drop 4368).take 32) 60018750000 2 = true :=
    take_step (n := 2) (t := 32) (b := 4370) rfl rfl ArealUCore.ArealUK.chunk_2184 s85
  have s83 : leavesOK ctxLitU 119675000000 3 ((leaves.drop 4366).take 34) 60018750000 2 = true :=
    take_step (n := 2) (t := 34) (b := 4368) rfl rfl ArealUCore.ArealUK.chunk_2183 s84
  have s82 : leavesOK ctxLitU 119650000000 3 ((leaves.drop 4364).take 36) 60018750000 2 = true :=
    take_step (n := 2) (t := 36) (b := 4366) rfl rfl ArealUCore.ArealUK.chunk_2182 s83
  have s81 : leavesOK ctxLitU 119625000000 3 ((leaves.drop 4362).take 38) 60018750000 2 = true :=
    take_step (n := 2) (t := 38) (b := 4364) rfl rfl ArealUCore.ArealUK.chunk_2181 s82
  have s80 : leavesOK ctxLitU 119600000000 3 ((leaves.drop 4360).take 40) 60018750000 2 = true :=
    take_step (n := 2) (t := 40) (b := 4362) rfl rfl ArealUCore.ArealUK.chunk_2180 s81
  have s79 : leavesOK ctxLitU 239150000000 4 ((leaves.drop 4358).take 42) 60018750000 2 = true :=
    take_step (n := 2) (t := 42) (b := 4360) rfl rfl ArealUCore.ArealUK.chunk_2179 s80
  have s78 : leavesOK ctxLitU 239100000000 4 ((leaves.drop 4356).take 44) 60018750000 2 = true :=
    take_step (n := 2) (t := 44) (b := 4358) rfl rfl ArealUCore.ArealUK.chunk_2178 s79
  have s77 : leavesOK ctxLitU 239050000000 4 ((leaves.drop 4354).take 46) 60018750000 2 = true :=
    take_step (n := 2) (t := 46) (b := 4356) rfl rfl ArealUCore.ArealUK.chunk_2177 s78
  have s76 : leavesOK ctxLitU 239000000000 4 ((leaves.drop 4352).take 48) 60018750000 2 = true :=
    take_step (n := 2) (t := 48) (b := 4354) rfl rfl ArealUCore.ArealUK.chunk_2176 s77
  have s75 : leavesOK ctxLitU 238950000000 4 ((leaves.drop 4350).take 50) 60018750000 2 = true :=
    take_step (n := 2) (t := 50) (b := 4352) rfl rfl ArealUCore.ArealUK.chunk_2175 s76
  have s74 : leavesOK ctxLitU 238900000000 4 ((leaves.drop 4348).take 52) 60018750000 2 = true :=
    take_step (n := 2) (t := 52) (b := 4350) rfl rfl ArealUCore.ArealUK.chunk_2174 s75
  have s73 : leavesOK ctxLitU 238850000000 4 ((leaves.drop 4346).take 54) 60018750000 2 = true :=
    take_step (n := 2) (t := 54) (b := 4348) rfl rfl ArealUCore.ArealUK.chunk_2173 s74
  have s72 : leavesOK ctxLitU 238800000000 4 ((leaves.drop 4344).take 56) 60018750000 2 = true :=
    take_step (n := 2) (t := 56) (b := 4346) rfl rfl ArealUCore.ArealUK.chunk_2172 s73
  have s71 : leavesOK ctxLitU 238750000000 4 ((leaves.drop 4342).take 58) 60018750000 2 = true :=
    take_step (n := 2) (t := 58) (b := 4344) rfl rfl ArealUCore.ArealUK.chunk_2171 s72
  have s70 : leavesOK ctxLitU 238700000000 4 ((leaves.drop 4340).take 60) 60018750000 2 = true :=
    take_step (n := 2) (t := 60) (b := 4342) rfl rfl ArealUCore.ArealUK.chunk_2170 s71
  have s69 : leavesOK ctxLitU 238650000000 4 ((leaves.drop 4338).take 62) 60018750000 2 = true :=
    take_step (n := 2) (t := 62) (b := 4340) rfl rfl ArealUCore.ArealUK.chunk_2169 s70
  have s68 : leavesOK ctxLitU 238600000000 4 ((leaves.drop 4336).take 64) 60018750000 2 = true :=
    take_step (n := 2) (t := 64) (b := 4338) rfl rfl ArealUCore.ArealUK.chunk_2168 s69
  have s67 : leavesOK ctxLitU 238550000000 4 ((leaves.drop 4334).take 66) 60018750000 2 = true :=
    take_step (n := 2) (t := 66) (b := 4336) rfl rfl ArealUCore.ArealUK.chunk_2167 s68
  have s66 : leavesOK ctxLitU 238500000000 4 ((leaves.drop 4332).take 68) 60018750000 2 = true :=
    take_step (n := 2) (t := 68) (b := 4334) rfl rfl ArealUCore.ArealUK.chunk_2166 s67
  have s65 : leavesOK ctxLitU 238450000000 4 ((leaves.drop 4330).take 70) 60018750000 2 = true :=
    take_step (n := 2) (t := 70) (b := 4332) rfl rfl ArealUCore.ArealUK.chunk_2165 s66
  have s64 : leavesOK ctxLitU 238400000000 4 ((leaves.drop 4328).take 72) 60018750000 2 = true :=
    take_step (n := 2) (t := 72) (b := 4330) rfl rfl ArealUCore.ArealUK.chunk_2164 s65
  have s63 : leavesOK ctxLitU 238350000000 4 ((leaves.drop 4326).take 74) 60018750000 2 = true :=
    take_step (n := 2) (t := 74) (b := 4328) rfl rfl ArealUCore.ArealUK.chunk_2163 s64
  have s62 : leavesOK ctxLitU 238300000000 4 ((leaves.drop 4324).take 76) 60018750000 2 = true :=
    take_step (n := 2) (t := 76) (b := 4326) rfl rfl ArealUCore.ArealUK.chunk_2162 s63
  have s61 : leavesOK ctxLitU 238250000000 4 ((leaves.drop 4322).take 78) 60018750000 2 = true :=
    take_step (n := 2) (t := 78) (b := 4324) rfl rfl ArealUCore.ArealUK.chunk_2161 s62
  have s60 : leavesOK ctxLitU 238200000000 4 ((leaves.drop 4320).take 80) 60018750000 2 = true :=
    take_step (n := 2) (t := 80) (b := 4322) rfl rfl ArealUCore.ArealUK.chunk_2160 s61
  have s59 : leavesOK ctxLitU 238150000000 4 ((leaves.drop 4318).take 82) 60018750000 2 = true :=
    take_step (n := 2) (t := 82) (b := 4320) rfl rfl ArealUCore.ArealUK.chunk_2159 s60
  have s58 : leavesOK ctxLitU 238100000000 4 ((leaves.drop 4316).take 84) 60018750000 2 = true :=
    take_step (n := 2) (t := 84) (b := 4318) rfl rfl ArealUCore.ArealUK.chunk_2158 s59
  have s57 : leavesOK ctxLitU 238050000000 4 ((leaves.drop 4314).take 86) 60018750000 2 = true :=
    take_step (n := 2) (t := 86) (b := 4316) rfl rfl ArealUCore.ArealUK.chunk_2157 s58
  have s56 : leavesOK ctxLitU 238000000000 4 ((leaves.drop 4312).take 88) 60018750000 2 = true :=
    take_step (n := 2) (t := 88) (b := 4314) rfl rfl ArealUCore.ArealUK.chunk_2156 s57
  have s55 : leavesOK ctxLitU 237950000000 4 ((leaves.drop 4310).take 90) 60018750000 2 = true :=
    take_step (n := 2) (t := 90) (b := 4312) rfl rfl ArealUCore.ArealUK.chunk_2155 s56
  have s54 : leavesOK ctxLitU 237900000000 4 ((leaves.drop 4308).take 92) 60018750000 2 = true :=
    take_step (n := 2) (t := 92) (b := 4310) rfl rfl ArealUCore.ArealUK.chunk_2154 s55
  have s53 : leavesOK ctxLitU 237850000000 4 ((leaves.drop 4306).take 94) 60018750000 2 = true :=
    take_step (n := 2) (t := 94) (b := 4308) rfl rfl ArealUCore.ArealUK.chunk_2153 s54
  have s52 : leavesOK ctxLitU 237800000000 4 ((leaves.drop 4304).take 96) 60018750000 2 = true :=
    take_step (n := 2) (t := 96) (b := 4306) rfl rfl ArealUCore.ArealUK.chunk_2152 s53
  have s51 : leavesOK ctxLitU 237750000000 4 ((leaves.drop 4302).take 98) 60018750000 2 = true :=
    take_step (n := 2) (t := 98) (b := 4304) rfl rfl ArealUCore.ArealUK.chunk_2151 s52
  have s50 : leavesOK ctxLitU 237700000000 4 ((leaves.drop 4300).take 100) 60018750000 2 = true :=
    take_step (n := 2) (t := 100) (b := 4302) rfl rfl ArealUCore.ArealUK.chunk_2150 s51
  have s49 : leavesOK ctxLitU 237650000000 4 ((leaves.drop 4298).take 102) 60018750000 2 = true :=
    take_step (n := 2) (t := 102) (b := 4300) rfl rfl ArealUCore.ArealUK.chunk_2149 s50
  have s48 : leavesOK ctxLitU 237600000000 4 ((leaves.drop 4296).take 104) 60018750000 2 = true :=
    take_step (n := 2) (t := 104) (b := 4298) rfl rfl ArealUCore.ArealUK.chunk_2148 s49
  have s47 : leavesOK ctxLitU 237550000000 4 ((leaves.drop 4294).take 106) 60018750000 2 = true :=
    take_step (n := 2) (t := 106) (b := 4296) rfl rfl ArealUCore.ArealUK.chunk_2147 s48
  have s46 : leavesOK ctxLitU 237500000000 4 ((leaves.drop 4292).take 108) 60018750000 2 = true :=
    take_step (n := 2) (t := 108) (b := 4294) rfl rfl ArealUCore.ArealUK.chunk_2146 s47
  have s45 : leavesOK ctxLitU 237450000000 4 ((leaves.drop 4290).take 110) 60018750000 2 = true :=
    take_step (n := 2) (t := 110) (b := 4292) rfl rfl ArealUCore.ArealUK.chunk_2145 s46
  have s44 : leavesOK ctxLitU 237400000000 4 ((leaves.drop 4288).take 112) 60018750000 2 = true :=
    take_step (n := 2) (t := 112) (b := 4290) rfl rfl ArealUCore.ArealUK.chunk_2144 s45
  have s43 : leavesOK ctxLitU 237350000000 4 ((leaves.drop 4286).take 114) 60018750000 2 = true :=
    take_step (n := 2) (t := 114) (b := 4288) rfl rfl ArealUCore.ArealUK.chunk_2143 s44
  have s42 : leavesOK ctxLitU 237300000000 4 ((leaves.drop 4284).take 116) 60018750000 2 = true :=
    take_step (n := 2) (t := 116) (b := 4286) rfl rfl ArealUCore.ArealUK.chunk_2142 s43
  have s41 : leavesOK ctxLitU 237250000000 4 ((leaves.drop 4282).take 118) 60018750000 2 = true :=
    take_step (n := 2) (t := 118) (b := 4284) rfl rfl ArealUCore.ArealUK.chunk_2141 s42
  have s40 : leavesOK ctxLitU 237200000000 4 ((leaves.drop 4280).take 120) 60018750000 2 = true :=
    take_step (n := 2) (t := 120) (b := 4282) rfl rfl ArealUCore.ArealUK.chunk_2140 s41
  have s39 : leavesOK ctxLitU 237150000000 4 ((leaves.drop 4278).take 122) 60018750000 2 = true :=
    take_step (n := 2) (t := 122) (b := 4280) rfl rfl ArealUCore.ArealUK.chunk_2139 s40
  have s38 : leavesOK ctxLitU 237100000000 4 ((leaves.drop 4276).take 124) 60018750000 2 = true :=
    take_step (n := 2) (t := 124) (b := 4278) rfl rfl ArealUCore.ArealUK.chunk_2138 s39
  have s37 : leavesOK ctxLitU 237050000000 4 ((leaves.drop 4274).take 126) 60018750000 2 = true :=
    take_step (n := 2) (t := 126) (b := 4276) rfl rfl ArealUCore.ArealUK.chunk_2137 s38
  have s36 : leavesOK ctxLitU 237000000000 4 ((leaves.drop 4272).take 128) 60018750000 2 = true :=
    take_step (n := 2) (t := 128) (b := 4274) rfl rfl ArealUCore.ArealUK.chunk_2136 s37
  have s35 : leavesOK ctxLitU 236950000000 4 ((leaves.drop 4270).take 130) 60018750000 2 = true :=
    take_step (n := 2) (t := 130) (b := 4272) rfl rfl ArealUCore.ArealUK.chunk_2135 s36
  have s34 : leavesOK ctxLitU 236900000000 4 ((leaves.drop 4268).take 132) 60018750000 2 = true :=
    take_step (n := 2) (t := 132) (b := 4270) rfl rfl ArealUCore.ArealUK.chunk_2134 s35
  have s33 : leavesOK ctxLitU 236850000000 4 ((leaves.drop 4266).take 134) 60018750000 2 = true :=
    take_step (n := 2) (t := 134) (b := 4268) rfl rfl ArealUCore.ArealUK.chunk_2133 s34
  have s32 : leavesOK ctxLitU 236800000000 4 ((leaves.drop 4264).take 136) 60018750000 2 = true :=
    take_step (n := 2) (t := 136) (b := 4266) rfl rfl ArealUCore.ArealUK.chunk_2132 s33
  have s31 : leavesOK ctxLitU 236750000000 4 ((leaves.drop 4262).take 138) 60018750000 2 = true :=
    take_step (n := 2) (t := 138) (b := 4264) rfl rfl ArealUCore.ArealUK.chunk_2131 s32
  have s30 : leavesOK ctxLitU 236700000000 4 ((leaves.drop 4260).take 140) 60018750000 2 = true :=
    take_step (n := 2) (t := 140) (b := 4262) rfl rfl ArealUCore.ArealUK.chunk_2130 s31
  have s29 : leavesOK ctxLitU 236650000000 4 ((leaves.drop 4258).take 142) 60018750000 2 = true :=
    take_step (n := 2) (t := 142) (b := 4260) rfl rfl ArealUCore.ArealUK.chunk_2129 s30
  have s28 : leavesOK ctxLitU 236600000000 4 ((leaves.drop 4256).take 144) 60018750000 2 = true :=
    take_step (n := 2) (t := 144) (b := 4258) rfl rfl ArealUCore.ArealUK.chunk_2128 s29
  have s27 : leavesOK ctxLitU 236550000000 4 ((leaves.drop 4254).take 146) 60018750000 2 = true :=
    take_step (n := 2) (t := 146) (b := 4256) rfl rfl ArealUCore.ArealUK.chunk_2127 s28
  have s26 : leavesOK ctxLitU 236500000000 4 ((leaves.drop 4252).take 148) 60018750000 2 = true :=
    take_step (n := 2) (t := 148) (b := 4254) rfl rfl ArealUCore.ArealUK.chunk_2126 s27
  have s25 : leavesOK ctxLitU 236450000000 4 ((leaves.drop 4250).take 150) 60018750000 2 = true :=
    take_step (n := 2) (t := 150) (b := 4252) rfl rfl ArealUCore.ArealUK.chunk_2125 s26
  have s24 : leavesOK ctxLitU 236400000000 4 ((leaves.drop 4248).take 152) 60018750000 2 = true :=
    take_step (n := 2) (t := 152) (b := 4250) rfl rfl ArealUCore.ArealUK.chunk_2124 s25
  have s23 : leavesOK ctxLitU 236350000000 4 ((leaves.drop 4246).take 154) 60018750000 2 = true :=
    take_step (n := 2) (t := 154) (b := 4248) rfl rfl ArealUCore.ArealUK.chunk_2123 s24
  have s22 : leavesOK ctxLitU 236300000000 4 ((leaves.drop 4244).take 156) 60018750000 2 = true :=
    take_step (n := 2) (t := 156) (b := 4246) rfl rfl ArealUCore.ArealUK.chunk_2122 s23
  have s21 : leavesOK ctxLitU 236250000000 4 ((leaves.drop 4242).take 158) 60018750000 2 = true :=
    take_step (n := 2) (t := 158) (b := 4244) rfl rfl ArealUCore.ArealUK.chunk_2121 s22
  have s20 : leavesOK ctxLitU 236200000000 4 ((leaves.drop 4240).take 160) 60018750000 2 = true :=
    take_step (n := 2) (t := 160) (b := 4242) rfl rfl ArealUCore.ArealUK.chunk_2120 s21
  have s19 : leavesOK ctxLitU 236150000000 4 ((leaves.drop 4238).take 162) 60018750000 2 = true :=
    take_step (n := 2) (t := 162) (b := 4240) rfl rfl ArealUCore.ArealUK.chunk_2119 s20
  have s18 : leavesOK ctxLitU 236100000000 4 ((leaves.drop 4236).take 164) 60018750000 2 = true :=
    take_step (n := 2) (t := 164) (b := 4238) rfl rfl ArealUCore.ArealUK.chunk_2118 s19
  have s17 : leavesOK ctxLitU 236050000000 4 ((leaves.drop 4234).take 166) 60018750000 2 = true :=
    take_step (n := 2) (t := 166) (b := 4236) rfl rfl ArealUCore.ArealUK.chunk_2117 s18
  have s16 : leavesOK ctxLitU 236000000000 4 ((leaves.drop 4232).take 168) 60018750000 2 = true :=
    take_step (n := 2) (t := 168) (b := 4234) rfl rfl ArealUCore.ArealUK.chunk_2116 s17
  have s15 : leavesOK ctxLitU 235950000000 4 ((leaves.drop 4230).take 170) 60018750000 2 = true :=
    take_step (n := 2) (t := 170) (b := 4232) rfl rfl ArealUCore.ArealUK.chunk_2115 s16
  have s14 : leavesOK ctxLitU 235900000000 4 ((leaves.drop 4228).take 172) 60018750000 2 = true :=
    take_step (n := 2) (t := 172) (b := 4230) rfl rfl ArealUCore.ArealUK.chunk_2114 s15
  have s13 : leavesOK ctxLitU 235850000000 4 ((leaves.drop 4226).take 174) 60018750000 2 = true :=
    take_step (n := 2) (t := 174) (b := 4228) rfl rfl ArealUCore.ArealUK.chunk_2113 s14
  have s12 : leavesOK ctxLitU 235800000000 4 ((leaves.drop 4224).take 176) 60018750000 2 = true :=
    take_step (n := 2) (t := 176) (b := 4226) rfl rfl ArealUCore.ArealUK.chunk_2112 s13
  have s11 : leavesOK ctxLitU 235750000000 4 ((leaves.drop 4222).take 178) 60018750000 2 = true :=
    take_step (n := 2) (t := 178) (b := 4224) rfl rfl ArealUCore.ArealUK.chunk_2111 s12
  have s10 : leavesOK ctxLitU 235700000000 4 ((leaves.drop 4220).take 180) 60018750000 2 = true :=
    take_step (n := 2) (t := 180) (b := 4222) rfl rfl ArealUCore.ArealUK.chunk_2110 s11
  have s9 : leavesOK ctxLitU 235650000000 4 ((leaves.drop 4218).take 182) 60018750000 2 = true :=
    take_step (n := 2) (t := 182) (b := 4220) rfl rfl ArealUCore.ArealUK.chunk_2109 s10
  have s8 : leavesOK ctxLitU 235600000000 4 ((leaves.drop 4216).take 184) 60018750000 2 = true :=
    take_step (n := 2) (t := 184) (b := 4218) rfl rfl ArealUCore.ArealUK.chunk_2108 s9
  have s7 : leavesOK ctxLitU 235550000000 4 ((leaves.drop 4214).take 186) 60018750000 2 = true :=
    take_step (n := 2) (t := 186) (b := 4216) rfl rfl ArealUCore.ArealUK.chunk_2107 s8
  have s6 : leavesOK ctxLitU 235500000000 4 ((leaves.drop 4212).take 188) 60018750000 2 = true :=
    take_step (n := 2) (t := 188) (b := 4214) rfl rfl ArealUCore.ArealUK.chunk_2106 s7
  have s5 : leavesOK ctxLitU 235450000000 4 ((leaves.drop 4210).take 190) 60018750000 2 = true :=
    take_step (n := 2) (t := 190) (b := 4212) rfl rfl ArealUCore.ArealUK.chunk_2105 s6
  have s4 : leavesOK ctxLitU 235400000000 4 ((leaves.drop 4208).take 192) 60018750000 2 = true :=
    take_step (n := 2) (t := 192) (b := 4210) rfl rfl ArealUCore.ArealUK.chunk_2104 s5
  have s3 : leavesOK ctxLitU 235350000000 4 ((leaves.drop 4206).take 194) 60018750000 2 = true :=
    take_step (n := 2) (t := 194) (b := 4208) rfl rfl ArealUCore.ArealUK.chunk_2103 s4
  have s2 : leavesOK ctxLitU 235300000000 4 ((leaves.drop 4204).take 196) 60018750000 2 = true :=
    take_step (n := 2) (t := 196) (b := 4206) rfl rfl ArealUCore.ArealUK.chunk_2102 s3
  have s1 : leavesOK ctxLitU 235250000000 4 ((leaves.drop 4202).take 198) 60018750000 2 = true :=
    take_step (n := 2) (t := 198) (b := 4204) rfl rfl ArealUCore.ArealUK.chunk_2101 s2
  have s0 : leavesOK ctxLitU 235200000000 4 ((leaves.drop 4200).take 200) 60018750000 2 = true :=
    take_step (n := 2) (t := 200) (b := 4202) rfl rfl ArealUCore.ArealUK.chunk_2100 s1
  exact s0

end Areal.UCert

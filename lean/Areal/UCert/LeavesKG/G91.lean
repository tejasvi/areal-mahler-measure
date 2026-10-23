import ArealUK.Chunk9100
import ArealUK.Chunk9101
import ArealUK.Chunk9102
import ArealUK.Chunk9103
import ArealUK.Chunk9104
import ArealUK.Chunk9105
import ArealUK.Chunk9106
import ArealUK.Chunk9107
import ArealUK.Chunk9108
import ArealUK.Chunk9109
import ArealUK.Chunk9110
import ArealUK.Chunk9111
import ArealUK.Chunk9112
import ArealUK.Chunk9113
import ArealUK.Chunk9114
import ArealUK.Chunk9115
import ArealUK.Chunk9116
import ArealUK.Chunk9117
import ArealUK.Chunk9118
import ArealUK.Chunk9119
import ArealUK.Chunk9120
import ArealUK.Chunk9121
import ArealUK.Chunk9122
import ArealUK.Chunk9123
import ArealUK.Chunk9124
import ArealUK.Chunk9125
import ArealUK.Chunk9126
import ArealUK.Chunk9127
import ArealUK.Chunk9128
import ArealUK.Chunk9129
import ArealUK.Chunk9130
import ArealUK.Chunk9131
import ArealUK.Chunk9132
import ArealUK.Chunk9133
import ArealUK.Chunk9134
import ArealUK.Chunk9135
import ArealUK.Chunk9136
import ArealUK.Chunk9137
import ArealUK.Chunk9138
import ArealUK.Chunk9139
import ArealUK.Chunk9140
import ArealUK.Chunk9141
import ArealUK.Chunk9142
import ArealUK.Chunk9143
import ArealUK.Chunk9144
import ArealUK.Chunk9145
import ArealUK.Chunk9146
import ArealUK.Chunk9147
import ArealUK.Chunk9148
import ArealUK.Chunk9149
import ArealUK.Chunk9150
import ArealUK.Chunk9151
import ArealUK.Chunk9152
import ArealUK.Chunk9153
import ArealUK.Chunk9154
import ArealUK.Chunk9155
import ArealUK.Chunk9156
import ArealUK.Chunk9157
import ArealUK.Chunk9158
import ArealUK.Chunk9159
import ArealUK.Chunk9160
import ArealUK.Chunk9161
import ArealUK.Chunk9162
import ArealUK.Chunk9163
import ArealUK.Chunk9164
import ArealUK.Chunk9165
import ArealUK.Chunk9166
import ArealUK.Chunk9167
import ArealUK.Chunk9168
import ArealUK.Chunk9169
import ArealUK.Chunk9170
import ArealUK.Chunk9171
import ArealUK.Chunk9172
import ArealUK.Chunk9173
import ArealUK.Chunk9174
import ArealUK.Chunk9175
import ArealUK.Chunk9176
import ArealUK.Chunk9177
import ArealUK.Chunk9178
import ArealUK.Chunk9179
import ArealUK.Chunk9180
import ArealUK.Chunk9181
import ArealUK.Chunk9182
import ArealUK.Chunk9183
import ArealUK.Chunk9184
import ArealUK.Chunk9185
import ArealUK.Chunk9186
import ArealUK.Chunk9187
import ArealUK.Chunk9188
import ArealUK.Chunk9189
import ArealUK.Chunk9190
import ArealUK.Chunk9191
import ArealUK.Chunk9192
import ArealUK.Chunk9193
import ArealUK.Chunk9194
import ArealUK.Chunk9195
import ArealUK.Chunk9196
import ArealUK.Chunk9197
import ArealUK.Chunk9198
import ArealUK.Chunk9199
import Areal.UCert.LeavesKGen

/-! Group 91 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_91 : leavesOK ctxLitU 76750000000 0 ((leaves.drop 18200).take 200) 314875000000 2 = true := by
  have s99 := ArealUCore.ArealUK.chunk_9199
  have s98 : leavesOK ctxLitU 314775000000 2 ((leaves.drop 18396).take 4) 314875000000 2 = true :=
    take_step (n := 2) (t := 4) (b := 18398) rfl rfl ArealUCore.ArealUK.chunk_9198 s99
  have s97 : leavesOK ctxLitU 314725000000 2 ((leaves.drop 18394).take 6) 314875000000 2 = true :=
    take_step (n := 2) (t := 6) (b := 18396) rfl rfl ArealUCore.ArealUK.chunk_9197 s98
  have s96 : leavesOK ctxLitU 314675000000 2 ((leaves.drop 18392).take 8) 314875000000 2 = true :=
    take_step (n := 2) (t := 8) (b := 18394) rfl rfl ArealUCore.ArealUK.chunk_9196 s97
  have s95 : leavesOK ctxLitU 314625000000 2 ((leaves.drop 18390).take 10) 314875000000 2 = true :=
    take_step (n := 2) (t := 10) (b := 18392) rfl rfl ArealUCore.ArealUK.chunk_9195 s96
  have s94 : leavesOK ctxLitU 314575000000 2 ((leaves.drop 18388).take 12) 314875000000 2 = true :=
    take_step (n := 2) (t := 12) (b := 18390) rfl rfl ArealUCore.ArealUK.chunk_9194 s95
  have s93 : leavesOK ctxLitU 314525000000 2 ((leaves.drop 18386).take 14) 314875000000 2 = true :=
    take_step (n := 2) (t := 14) (b := 18388) rfl rfl ArealUCore.ArealUK.chunk_9193 s94
  have s92 : leavesOK ctxLitU 314475000000 2 ((leaves.drop 18384).take 16) 314875000000 2 = true :=
    take_step (n := 2) (t := 16) (b := 18386) rfl rfl ArealUCore.ArealUK.chunk_9192 s93
  have s91 : leavesOK ctxLitU 314425000000 2 ((leaves.drop 18382).take 18) 314875000000 2 = true :=
    take_step (n := 2) (t := 18) (b := 18384) rfl rfl ArealUCore.ArealUK.chunk_9191 s92
  have s90 : leavesOK ctxLitU 314375000000 2 ((leaves.drop 18380).take 20) 314875000000 2 = true :=
    take_step (n := 2) (t := 20) (b := 18382) rfl rfl ArealUCore.ArealUK.chunk_9190 s91
  have s89 : leavesOK ctxLitU 314325000000 2 ((leaves.drop 18378).take 22) 314875000000 2 = true :=
    take_step (n := 2) (t := 22) (b := 18380) rfl rfl ArealUCore.ArealUK.chunk_9189 s90
  have s88 : leavesOK ctxLitU 314275000000 2 ((leaves.drop 18376).take 24) 314875000000 2 = true :=
    take_step (n := 2) (t := 24) (b := 18378) rfl rfl ArealUCore.ArealUK.chunk_9188 s89
  have s87 : leavesOK ctxLitU 314225000000 2 ((leaves.drop 18374).take 26) 314875000000 2 = true :=
    take_step (n := 2) (t := 26) (b := 18376) rfl rfl ArealUCore.ArealUK.chunk_9187 s88
  have s86 : leavesOK ctxLitU 314175000000 2 ((leaves.drop 18372).take 28) 314875000000 2 = true :=
    take_step (n := 2) (t := 28) (b := 18374) rfl rfl ArealUCore.ArealUK.chunk_9186 s87
  have s85 : leavesOK ctxLitU 314125000000 2 ((leaves.drop 18370).take 30) 314875000000 2 = true :=
    take_step (n := 2) (t := 30) (b := 18372) rfl rfl ArealUCore.ArealUK.chunk_9185 s86
  have s84 : leavesOK ctxLitU 314075000000 2 ((leaves.drop 18368).take 32) 314875000000 2 = true :=
    take_step (n := 2) (t := 32) (b := 18370) rfl rfl ArealUCore.ArealUK.chunk_9184 s85
  have s83 : leavesOK ctxLitU 314025000000 2 ((leaves.drop 18366).take 34) 314875000000 2 = true :=
    take_step (n := 2) (t := 34) (b := 18368) rfl rfl ArealUCore.ArealUK.chunk_9183 s84
  have s82 : leavesOK ctxLitU 313975000000 2 ((leaves.drop 18364).take 36) 314875000000 2 = true :=
    take_step (n := 2) (t := 36) (b := 18366) rfl rfl ArealUCore.ArealUK.chunk_9182 s83
  have s81 : leavesOK ctxLitU 313925000000 2 ((leaves.drop 18362).take 38) 314875000000 2 = true :=
    take_step (n := 2) (t := 38) (b := 18364) rfl rfl ArealUCore.ArealUK.chunk_9181 s82
  have s80 : leavesOK ctxLitU 313875000000 2 ((leaves.drop 18360).take 40) 314875000000 2 = true :=
    take_step (n := 2) (t := 40) (b := 18362) rfl rfl ArealUCore.ArealUK.chunk_9180 s81
  have s79 : leavesOK ctxLitU 313825000000 2 ((leaves.drop 18358).take 42) 314875000000 2 = true :=
    take_step (n := 2) (t := 42) (b := 18360) rfl rfl ArealUCore.ArealUK.chunk_9179 s80
  have s78 : leavesOK ctxLitU 313775000000 2 ((leaves.drop 18356).take 44) 314875000000 2 = true :=
    take_step (n := 2) (t := 44) (b := 18358) rfl rfl ArealUCore.ArealUK.chunk_9178 s79
  have s77 : leavesOK ctxLitU 313725000000 2 ((leaves.drop 18354).take 46) 314875000000 2 = true :=
    take_step (n := 2) (t := 46) (b := 18356) rfl rfl ArealUCore.ArealUK.chunk_9177 s78
  have s76 : leavesOK ctxLitU 313675000000 2 ((leaves.drop 18352).take 48) 314875000000 2 = true :=
    take_step (n := 2) (t := 48) (b := 18354) rfl rfl ArealUCore.ArealUK.chunk_9176 s77
  have s75 : leavesOK ctxLitU 313625000000 2 ((leaves.drop 18350).take 50) 314875000000 2 = true :=
    take_step (n := 2) (t := 50) (b := 18352) rfl rfl ArealUCore.ArealUK.chunk_9175 s76
  have s74 : leavesOK ctxLitU 313575000000 2 ((leaves.drop 18348).take 52) 314875000000 2 = true :=
    take_step (n := 2) (t := 52) (b := 18350) rfl rfl ArealUCore.ArealUK.chunk_9174 s75
  have s73 : leavesOK ctxLitU 313525000000 2 ((leaves.drop 18346).take 54) 314875000000 2 = true :=
    take_step (n := 2) (t := 54) (b := 18348) rfl rfl ArealUCore.ArealUK.chunk_9173 s74
  have s72 : leavesOK ctxLitU 313475000000 2 ((leaves.drop 18344).take 56) 314875000000 2 = true :=
    take_step (n := 2) (t := 56) (b := 18346) rfl rfl ArealUCore.ArealUK.chunk_9172 s73
  have s71 : leavesOK ctxLitU 313425000000 2 ((leaves.drop 18342).take 58) 314875000000 2 = true :=
    take_step (n := 2) (t := 58) (b := 18344) rfl rfl ArealUCore.ArealUK.chunk_9171 s72
  have s70 : leavesOK ctxLitU 313375000000 2 ((leaves.drop 18340).take 60) 314875000000 2 = true :=
    take_step (n := 2) (t := 60) (b := 18342) rfl rfl ArealUCore.ArealUK.chunk_9170 s71
  have s69 : leavesOK ctxLitU 313325000000 2 ((leaves.drop 18338).take 62) 314875000000 2 = true :=
    take_step (n := 2) (t := 62) (b := 18340) rfl rfl ArealUCore.ArealUK.chunk_9169 s70
  have s68 : leavesOK ctxLitU 313275000000 2 ((leaves.drop 18336).take 64) 314875000000 2 = true :=
    take_step (n := 2) (t := 64) (b := 18338) rfl rfl ArealUCore.ArealUK.chunk_9168 s69
  have s67 : leavesOK ctxLitU 313225000000 2 ((leaves.drop 18334).take 66) 314875000000 2 = true :=
    take_step (n := 2) (t := 66) (b := 18336) rfl rfl ArealUCore.ArealUK.chunk_9167 s68
  have s66 : leavesOK ctxLitU 313175000000 2 ((leaves.drop 18332).take 68) 314875000000 2 = true :=
    take_step (n := 2) (t := 68) (b := 18334) rfl rfl ArealUCore.ArealUK.chunk_9166 s67
  have s65 : leavesOK ctxLitU 313125000000 2 ((leaves.drop 18330).take 70) 314875000000 2 = true :=
    take_step (n := 2) (t := 70) (b := 18332) rfl rfl ArealUCore.ArealUK.chunk_9165 s66
  have s64 : leavesOK ctxLitU 313075000000 2 ((leaves.drop 18328).take 72) 314875000000 2 = true :=
    take_step (n := 2) (t := 72) (b := 18330) rfl rfl ArealUCore.ArealUK.chunk_9164 s65
  have s63 : leavesOK ctxLitU 313025000000 2 ((leaves.drop 18326).take 74) 314875000000 2 = true :=
    take_step (n := 2) (t := 74) (b := 18328) rfl rfl ArealUCore.ArealUK.chunk_9163 s64
  have s62 : leavesOK ctxLitU 312975000000 2 ((leaves.drop 18324).take 76) 314875000000 2 = true :=
    take_step (n := 2) (t := 76) (b := 18326) rfl rfl ArealUCore.ArealUK.chunk_9162 s63
  have s61 : leavesOK ctxLitU 312925000000 2 ((leaves.drop 18322).take 78) 314875000000 2 = true :=
    take_step (n := 2) (t := 78) (b := 18324) rfl rfl ArealUCore.ArealUK.chunk_9161 s62
  have s60 : leavesOK ctxLitU 312875000000 2 ((leaves.drop 18320).take 80) 314875000000 2 = true :=
    take_step (n := 2) (t := 80) (b := 18322) rfl rfl ArealUCore.ArealUK.chunk_9160 s61
  have s59 : leavesOK ctxLitU 312825000000 2 ((leaves.drop 18318).take 82) 314875000000 2 = true :=
    take_step (n := 2) (t := 82) (b := 18320) rfl rfl ArealUCore.ArealUK.chunk_9159 s60
  have s58 : leavesOK ctxLitU 312775000000 2 ((leaves.drop 18316).take 84) 314875000000 2 = true :=
    take_step (n := 2) (t := 84) (b := 18318) rfl rfl ArealUCore.ArealUK.chunk_9158 s59
  have s57 : leavesOK ctxLitU 312725000000 2 ((leaves.drop 18314).take 86) 314875000000 2 = true :=
    take_step (n := 2) (t := 86) (b := 18316) rfl rfl ArealUCore.ArealUK.chunk_9157 s58
  have s56 : leavesOK ctxLitU 312675000000 2 ((leaves.drop 18312).take 88) 314875000000 2 = true :=
    take_step (n := 2) (t := 88) (b := 18314) rfl rfl ArealUCore.ArealUK.chunk_9156 s57
  have s55 : leavesOK ctxLitU 312625000000 2 ((leaves.drop 18310).take 90) 314875000000 2 = true :=
    take_step (n := 2) (t := 90) (b := 18312) rfl rfl ArealUCore.ArealUK.chunk_9155 s56
  have s54 : leavesOK ctxLitU 312575000000 2 ((leaves.drop 18308).take 92) 314875000000 2 = true :=
    take_step (n := 2) (t := 92) (b := 18310) rfl rfl ArealUCore.ArealUK.chunk_9154 s55
  have s53 : leavesOK ctxLitU 312525000000 2 ((leaves.drop 18306).take 94) 314875000000 2 = true :=
    take_step (n := 2) (t := 94) (b := 18308) rfl rfl ArealUCore.ArealUK.chunk_9153 s54
  have s52 : leavesOK ctxLitU 312475000000 2 ((leaves.drop 18304).take 96) 314875000000 2 = true :=
    take_step (n := 2) (t := 96) (b := 18306) rfl rfl ArealUCore.ArealUK.chunk_9152 s53
  have s51 : leavesOK ctxLitU 312425000000 2 ((leaves.drop 18302).take 98) 314875000000 2 = true :=
    take_step (n := 2) (t := 98) (b := 18304) rfl rfl ArealUCore.ArealUK.chunk_9151 s52
  have s50 : leavesOK ctxLitU 312375000000 2 ((leaves.drop 18300).take 100) 314875000000 2 = true :=
    take_step (n := 2) (t := 100) (b := 18302) rfl rfl ArealUCore.ArealUK.chunk_9150 s51
  have s49 : leavesOK ctxLitU 312325000000 2 ((leaves.drop 18298).take 102) 314875000000 2 = true :=
    take_step (n := 2) (t := 102) (b := 18300) rfl rfl ArealUCore.ArealUK.chunk_9149 s50
  have s48 : leavesOK ctxLitU 312275000000 2 ((leaves.drop 18296).take 104) 314875000000 2 = true :=
    take_step (n := 2) (t := 104) (b := 18298) rfl rfl ArealUCore.ArealUK.chunk_9148 s49
  have s47 : leavesOK ctxLitU 312225000000 2 ((leaves.drop 18294).take 106) 314875000000 2 = true :=
    take_step (n := 2) (t := 106) (b := 18296) rfl rfl ArealUCore.ArealUK.chunk_9147 s48
  have s46 : leavesOK ctxLitU 312175000000 2 ((leaves.drop 18292).take 108) 314875000000 2 = true :=
    take_step (n := 2) (t := 108) (b := 18294) rfl rfl ArealUCore.ArealUK.chunk_9146 s47
  have s45 : leavesOK ctxLitU 312125000000 2 ((leaves.drop 18290).take 110) 314875000000 2 = true :=
    take_step (n := 2) (t := 110) (b := 18292) rfl rfl ArealUCore.ArealUK.chunk_9145 s46
  have s44 : leavesOK ctxLitU 312075000000 2 ((leaves.drop 18288).take 112) 314875000000 2 = true :=
    take_step (n := 2) (t := 112) (b := 18290) rfl rfl ArealUCore.ArealUK.chunk_9144 s45
  have s43 : leavesOK ctxLitU 312025000000 2 ((leaves.drop 18286).take 114) 314875000000 2 = true :=
    take_step (n := 2) (t := 114) (b := 18288) rfl rfl ArealUCore.ArealUK.chunk_9143 s44
  have s42 : leavesOK ctxLitU 311975000000 2 ((leaves.drop 18284).take 116) 314875000000 2 = true :=
    take_step (n := 2) (t := 116) (b := 18286) rfl rfl ArealUCore.ArealUK.chunk_9142 s43
  have s41 : leavesOK ctxLitU 311925000000 2 ((leaves.drop 18282).take 118) 314875000000 2 = true :=
    take_step (n := 2) (t := 118) (b := 18284) rfl rfl ArealUCore.ArealUK.chunk_9141 s42
  have s40 : leavesOK ctxLitU 311875000000 2 ((leaves.drop 18280).take 120) 314875000000 2 = true :=
    take_step (n := 2) (t := 120) (b := 18282) rfl rfl ArealUCore.ArealUK.chunk_9140 s41
  have s39 : leavesOK ctxLitU 311825000000 2 ((leaves.drop 18278).take 122) 314875000000 2 = true :=
    take_step (n := 2) (t := 122) (b := 18280) rfl rfl ArealUCore.ArealUK.chunk_9139 s40
  have s38 : leavesOK ctxLitU 311775000000 2 ((leaves.drop 18276).take 124) 314875000000 2 = true :=
    take_step (n := 2) (t := 124) (b := 18278) rfl rfl ArealUCore.ArealUK.chunk_9138 s39
  have s37 : leavesOK ctxLitU 311725000000 2 ((leaves.drop 18274).take 126) 314875000000 2 = true :=
    take_step (n := 2) (t := 126) (b := 18276) rfl rfl ArealUCore.ArealUK.chunk_9137 s38
  have s36 : leavesOK ctxLitU 311675000000 2 ((leaves.drop 18272).take 128) 314875000000 2 = true :=
    take_step (n := 2) (t := 128) (b := 18274) rfl rfl ArealUCore.ArealUK.chunk_9136 s37
  have s35 : leavesOK ctxLitU 311625000000 2 ((leaves.drop 18270).take 130) 314875000000 2 = true :=
    take_step (n := 2) (t := 130) (b := 18272) rfl rfl ArealUCore.ArealUK.chunk_9135 s36
  have s34 : leavesOK ctxLitU 311575000000 2 ((leaves.drop 18268).take 132) 314875000000 2 = true :=
    take_step (n := 2) (t := 132) (b := 18270) rfl rfl ArealUCore.ArealUK.chunk_9134 s35
  have s33 : leavesOK ctxLitU 311525000000 2 ((leaves.drop 18266).take 134) 314875000000 2 = true :=
    take_step (n := 2) (t := 134) (b := 18268) rfl rfl ArealUCore.ArealUK.chunk_9133 s34
  have s32 : leavesOK ctxLitU 623000000000 3 ((leaves.drop 18264).take 136) 314875000000 2 = true :=
    take_step (n := 2) (t := 136) (b := 18266) rfl rfl ArealUCore.ArealUK.chunk_9132 s33
  have s31 : leavesOK ctxLitU 311450000000 2 ((leaves.drop 18262).take 138) 314875000000 2 = true :=
    take_step (n := 2) (t := 138) (b := 18264) rfl rfl ArealUCore.ArealUK.chunk_9131 s32
  have s30 : leavesOK ctxLitU 311400000000 2 ((leaves.drop 18260).take 140) 314875000000 2 = true :=
    take_step (n := 2) (t := 140) (b := 18262) rfl rfl ArealUCore.ArealUK.chunk_9130 s31
  have s29 : leavesOK ctxLitU 155650000000 1 ((leaves.drop 18258).take 142) 314875000000 2 = true :=
    take_step (n := 2) (t := 142) (b := 18260) rfl rfl ArealUCore.ArealUK.chunk_9129 s30
  have s28 : leavesOK ctxLitU 155625000000 1 ((leaves.drop 18256).take 144) 314875000000 2 = true :=
    take_step (n := 2) (t := 144) (b := 18258) rfl rfl ArealUCore.ArealUK.chunk_9128 s29
  have s27 : leavesOK ctxLitU 311212500000 2 ((leaves.drop 18254).take 146) 314875000000 2 = true :=
    take_step (n := 2) (t := 146) (b := 18256) rfl rfl ArealUCore.ArealUK.chunk_9127 s28
  have s26 : leavesOK ctxLitU 622400000000 3 ((leaves.drop 18252).take 148) 314875000000 2 = true :=
    take_step (n := 2) (t := 148) (b := 18254) rfl rfl ArealUCore.ArealUK.chunk_9126 s27
  have s25 : leavesOK ctxLitU 77787500000 0 ((leaves.drop 18250).take 150) 314875000000 2 = true :=
    take_step (n := 2) (t := 150) (b := 18252) rfl rfl ArealUCore.ArealUK.chunk_9125 s26
  have s24 : leavesOK ctxLitU 77775000000 0 ((leaves.drop 18248).take 152) 314875000000 2 = true :=
    take_step (n := 2) (t := 152) (b := 18250) rfl rfl ArealUCore.ArealUK.chunk_9124 s25
  have s23 : leavesOK ctxLitU 77762500000 0 ((leaves.drop 18246).take 154) 314875000000 2 = true :=
    take_step (n := 2) (t := 154) (b := 18248) rfl rfl ArealUCore.ArealUK.chunk_9123 s24
  have s22 : leavesOK ctxLitU 77750000000 0 ((leaves.drop 18244).take 156) 314875000000 2 = true :=
    take_step (n := 2) (t := 156) (b := 18246) rfl rfl ArealUCore.ArealUK.chunk_9122 s23
  have s21 : leavesOK ctxLitU 77737500000 0 ((leaves.drop 18242).take 158) 314875000000 2 = true :=
    take_step (n := 2) (t := 158) (b := 18244) rfl rfl ArealUCore.ArealUK.chunk_9121 s22
  have s20 : leavesOK ctxLitU 77725000000 0 ((leaves.drop 18240).take 160) 314875000000 2 = true :=
    take_step (n := 2) (t := 160) (b := 18242) rfl rfl ArealUCore.ArealUK.chunk_9120 s21
  have s19 : leavesOK ctxLitU 77700000000 0 ((leaves.drop 18238).take 162) 314875000000 2 = true :=
    take_step (n := 2) (t := 162) (b := 18240) rfl rfl ArealUCore.ArealUK.chunk_9119 s20
  have s18 : leavesOK ctxLitU 77650000000 0 ((leaves.drop 18236).take 164) 314875000000 2 = true :=
    take_step (n := 2) (t := 164) (b := 18238) rfl rfl ArealUCore.ArealUK.chunk_9118 s19
  have s17 : leavesOK ctxLitU 77600000000 0 ((leaves.drop 18234).take 166) 314875000000 2 = true :=
    take_step (n := 2) (t := 166) (b := 18236) rfl rfl ArealUCore.ArealUK.chunk_9117 s18
  have s16 : leavesOK ctxLitU 77550000000 0 ((leaves.drop 18232).take 168) 314875000000 2 = true :=
    take_step (n := 2) (t := 168) (b := 18234) rfl rfl ArealUCore.ArealUK.chunk_9116 s17
  have s15 : leavesOK ctxLitU 77500000000 0 ((leaves.drop 18230).take 170) 314875000000 2 = true :=
    take_step (n := 2) (t := 170) (b := 18232) rfl rfl ArealUCore.ArealUK.chunk_9115 s16
  have s14 : leavesOK ctxLitU 77450000000 0 ((leaves.drop 18228).take 172) 314875000000 2 = true :=
    take_step (n := 2) (t := 172) (b := 18230) rfl rfl ArealUCore.ArealUK.chunk_9114 s15
  have s13 : leavesOK ctxLitU 77400000000 0 ((leaves.drop 18226).take 174) 314875000000 2 = true :=
    take_step (n := 2) (t := 174) (b := 18228) rfl rfl ArealUCore.ArealUK.chunk_9113 s14
  have s12 : leavesOK ctxLitU 77350000000 0 ((leaves.drop 18224).take 176) 314875000000 2 = true :=
    take_step (n := 2) (t := 176) (b := 18226) rfl rfl ArealUCore.ArealUK.chunk_9112 s13
  have s11 : leavesOK ctxLitU 77300000000 0 ((leaves.drop 18222).take 178) 314875000000 2 = true :=
    take_step (n := 2) (t := 178) (b := 18224) rfl rfl ArealUCore.ArealUK.chunk_9111 s12
  have s10 : leavesOK ctxLitU 77250000000 0 ((leaves.drop 18220).take 180) 314875000000 2 = true :=
    take_step (n := 2) (t := 180) (b := 18222) rfl rfl ArealUCore.ArealUK.chunk_9110 s11
  have s9 : leavesOK ctxLitU 77200000000 0 ((leaves.drop 18218).take 182) 314875000000 2 = true :=
    take_step (n := 2) (t := 182) (b := 18220) rfl rfl ArealUCore.ArealUK.chunk_9109 s10
  have s8 : leavesOK ctxLitU 77150000000 0 ((leaves.drop 18216).take 184) 314875000000 2 = true :=
    take_step (n := 2) (t := 184) (b := 18218) rfl rfl ArealUCore.ArealUK.chunk_9108 s9
  have s7 : leavesOK ctxLitU 77100000000 0 ((leaves.drop 18214).take 186) 314875000000 2 = true :=
    take_step (n := 2) (t := 186) (b := 18216) rfl rfl ArealUCore.ArealUK.chunk_9107 s8
  have s6 : leavesOK ctxLitU 77050000000 0 ((leaves.drop 18212).take 188) 314875000000 2 = true :=
    take_step (n := 2) (t := 188) (b := 18214) rfl rfl ArealUCore.ArealUK.chunk_9106 s7
  have s5 : leavesOK ctxLitU 77000000000 0 ((leaves.drop 18210).take 190) 314875000000 2 = true :=
    take_step (n := 2) (t := 190) (b := 18212) rfl rfl ArealUCore.ArealUK.chunk_9105 s6
  have s4 : leavesOK ctxLitU 76950000000 0 ((leaves.drop 18208).take 192) 314875000000 2 = true :=
    take_step (n := 2) (t := 192) (b := 18210) rfl rfl ArealUCore.ArealUK.chunk_9104 s5
  have s3 : leavesOK ctxLitU 76900000000 0 ((leaves.drop 18206).take 194) 314875000000 2 = true :=
    take_step (n := 2) (t := 194) (b := 18208) rfl rfl ArealUCore.ArealUK.chunk_9103 s4
  have s2 : leavesOK ctxLitU 76850000000 0 ((leaves.drop 18204).take 196) 314875000000 2 = true :=
    take_step (n := 2) (t := 196) (b := 18206) rfl rfl ArealUCore.ArealUK.chunk_9102 s3
  have s1 : leavesOK ctxLitU 76800000000 0 ((leaves.drop 18202).take 198) 314875000000 2 = true :=
    take_step (n := 2) (t := 198) (b := 18204) rfl rfl ArealUCore.ArealUK.chunk_9101 s2
  have s0 : leavesOK ctxLitU 76750000000 0 ((leaves.drop 18200).take 200) 314875000000 2 = true :=
    take_step (n := 2) (t := 200) (b := 18202) rfl rfl ArealUCore.ArealUK.chunk_9100 s1
  exact s0

end Areal.UCert

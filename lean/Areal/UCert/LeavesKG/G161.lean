import ArealUK.Chunk16100
import ArealUK.Chunk16101
import ArealUK.Chunk16102
import ArealUK.Chunk16103
import ArealUK.Chunk16104
import ArealUK.Chunk16105
import ArealUK.Chunk16106
import ArealUK.Chunk16107
import ArealUK.Chunk16108
import ArealUK.Chunk16109
import ArealUK.Chunk16110
import ArealUK.Chunk16111
import ArealUK.Chunk16112
import ArealUK.Chunk16113
import ArealUK.Chunk16114
import ArealUK.Chunk16115
import ArealUK.Chunk16116
import ArealUK.Chunk16117
import ArealUK.Chunk16118
import ArealUK.Chunk16119
import ArealUK.Chunk16120
import ArealUK.Chunk16121
import ArealUK.Chunk16122
import ArealUK.Chunk16123
import ArealUK.Chunk16124
import ArealUK.Chunk16125
import ArealUK.Chunk16126
import ArealUK.Chunk16127
import ArealUK.Chunk16128
import ArealUK.Chunk16129
import ArealUK.Chunk16130
import ArealUK.Chunk16131
import ArealUK.Chunk16132
import ArealUK.Chunk16133
import ArealUK.Chunk16134
import ArealUK.Chunk16135
import ArealUK.Chunk16136
import ArealUK.Chunk16137
import ArealUK.Chunk16138
import ArealUK.Chunk16139
import ArealUK.Chunk16140
import ArealUK.Chunk16141
import ArealUK.Chunk16142
import ArealUK.Chunk16143
import ArealUK.Chunk16144
import ArealUK.Chunk16145
import ArealUK.Chunk16146
import ArealUK.Chunk16147
import ArealUK.Chunk16148
import ArealUK.Chunk16149
import ArealUK.Chunk16150
import ArealUK.Chunk16151
import ArealUK.Chunk16152
import ArealUK.Chunk16153
import ArealUK.Chunk16154
import ArealUK.Chunk16155
import ArealUK.Chunk16156
import ArealUK.Chunk16157
import ArealUK.Chunk16158
import ArealUK.Chunk16159
import ArealUK.Chunk16160
import ArealUK.Chunk16161
import ArealUK.Chunk16162
import ArealUK.Chunk16163
import ArealUK.Chunk16164
import ArealUK.Chunk16165
import ArealUK.Chunk16166
import ArealUK.Chunk16167
import ArealUK.Chunk16168
import ArealUK.Chunk16169
import ArealUK.Chunk16170
import ArealUK.Chunk16171
import ArealUK.Chunk16172
import ArealUK.Chunk16173
import ArealUK.Chunk16174
import ArealUK.Chunk16175
import ArealUK.Chunk16176
import ArealUK.Chunk16177
import ArealUK.Chunk16178
import ArealUK.Chunk16179
import ArealUK.Chunk16180
import ArealUK.Chunk16181
import ArealUK.Chunk16182
import ArealUK.Chunk16183
import ArealUK.Chunk16184
import ArealUK.Chunk16185
import ArealUK.Chunk16186
import ArealUK.Chunk16187
import ArealUK.Chunk16188
import ArealUK.Chunk16189
import ArealUK.Chunk16190
import ArealUK.Chunk16191
import ArealUK.Chunk16192
import ArealUK.Chunk16193
import ArealUK.Chunk16194
import ArealUK.Chunk16195
import ArealUK.Chunk16196
import ArealUK.Chunk16197
import ArealUK.Chunk16198
import ArealUK.Chunk16199
import Areal.UCert.LeavesKGen

/-! Group 161 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_161 : leavesOK ctxLitU 172556250000 0 ((leaves.drop 32200).take 200) 173993750000 0 = true := by
  have s99 := ArealUCore.ArealUK.chunk_16199
  have s98 : leavesOK ctxLitU 173968750000 0 ((leaves.drop 32396).take 4) 173993750000 0 = true :=
    take_step (n := 2) (t := 4) (b := 32398) rfl rfl ArealUCore.ArealUK.chunk_16198 s99
  have s97 : leavesOK ctxLitU 173956250000 0 ((leaves.drop 32394).take 6) 173993750000 0 = true :=
    take_step (n := 2) (t := 6) (b := 32396) rfl rfl ArealUCore.ArealUK.chunk_16197 s98
  have s96 : leavesOK ctxLitU 173943750000 0 ((leaves.drop 32392).take 8) 173993750000 0 = true :=
    take_step (n := 2) (t := 8) (b := 32394) rfl rfl ArealUCore.ArealUK.chunk_16196 s97
  have s95 : leavesOK ctxLitU 173931250000 0 ((leaves.drop 32390).take 10) 173993750000 0 = true :=
    take_step (n := 2) (t := 10) (b := 32392) rfl rfl ArealUCore.ArealUK.chunk_16195 s96
  have s94 : leavesOK ctxLitU 173918750000 0 ((leaves.drop 32388).take 12) 173993750000 0 = true :=
    take_step (n := 2) (t := 12) (b := 32390) rfl rfl ArealUCore.ArealUK.chunk_16194 s95
  have s93 : leavesOK ctxLitU 173906250000 0 ((leaves.drop 32386).take 14) 173993750000 0 = true :=
    take_step (n := 2) (t := 14) (b := 32388) rfl rfl ArealUCore.ArealUK.chunk_16193 s94
  have s92 : leavesOK ctxLitU 173893750000 0 ((leaves.drop 32384).take 16) 173993750000 0 = true :=
    take_step (n := 2) (t := 16) (b := 32386) rfl rfl ArealUCore.ArealUK.chunk_16192 s93
  have s91 : leavesOK ctxLitU 173881250000 0 ((leaves.drop 32382).take 18) 173993750000 0 = true :=
    take_step (n := 2) (t := 18) (b := 32384) rfl rfl ArealUCore.ArealUK.chunk_16191 s92
  have s90 : leavesOK ctxLitU 173868750000 0 ((leaves.drop 32380).take 20) 173993750000 0 = true :=
    take_step (n := 2) (t := 20) (b := 32382) rfl rfl ArealUCore.ArealUK.chunk_16190 s91
  have s89 : leavesOK ctxLitU 173856250000 0 ((leaves.drop 32378).take 22) 173993750000 0 = true :=
    take_step (n := 2) (t := 22) (b := 32380) rfl rfl ArealUCore.ArealUK.chunk_16189 s90
  have s88 : leavesOK ctxLitU 173843750000 0 ((leaves.drop 32376).take 24) 173993750000 0 = true :=
    take_step (n := 2) (t := 24) (b := 32378) rfl rfl ArealUCore.ArealUK.chunk_16188 s89
  have s87 : leavesOK ctxLitU 173831250000 0 ((leaves.drop 32374).take 26) 173993750000 0 = true :=
    take_step (n := 2) (t := 26) (b := 32376) rfl rfl ArealUCore.ArealUK.chunk_16187 s88
  have s86 : leavesOK ctxLitU 173818750000 0 ((leaves.drop 32372).take 28) 173993750000 0 = true :=
    take_step (n := 2) (t := 28) (b := 32374) rfl rfl ArealUCore.ArealUK.chunk_16186 s87
  have s85 : leavesOK ctxLitU 173806250000 0 ((leaves.drop 32370).take 30) 173993750000 0 = true :=
    take_step (n := 2) (t := 30) (b := 32372) rfl rfl ArealUCore.ArealUK.chunk_16185 s86
  have s84 : leavesOK ctxLitU 173793750000 0 ((leaves.drop 32368).take 32) 173993750000 0 = true :=
    take_step (n := 2) (t := 32) (b := 32370) rfl rfl ArealUCore.ArealUK.chunk_16184 s85
  have s83 : leavesOK ctxLitU 173781250000 0 ((leaves.drop 32366).take 34) 173993750000 0 = true :=
    take_step (n := 2) (t := 34) (b := 32368) rfl rfl ArealUCore.ArealUK.chunk_16183 s84
  have s82 : leavesOK ctxLitU 173768750000 0 ((leaves.drop 32364).take 36) 173993750000 0 = true :=
    take_step (n := 2) (t := 36) (b := 32366) rfl rfl ArealUCore.ArealUK.chunk_16182 s83
  have s81 : leavesOK ctxLitU 173756250000 0 ((leaves.drop 32362).take 38) 173993750000 0 = true :=
    take_step (n := 2) (t := 38) (b := 32364) rfl rfl ArealUCore.ArealUK.chunk_16181 s82
  have s80 : leavesOK ctxLitU 173743750000 0 ((leaves.drop 32360).take 40) 173993750000 0 = true :=
    take_step (n := 2) (t := 40) (b := 32362) rfl rfl ArealUCore.ArealUK.chunk_16180 s81
  have s79 : leavesOK ctxLitU 173731250000 0 ((leaves.drop 32358).take 42) 173993750000 0 = true :=
    take_step (n := 2) (t := 42) (b := 32360) rfl rfl ArealUCore.ArealUK.chunk_16179 s80
  have s78 : leavesOK ctxLitU 173718750000 0 ((leaves.drop 32356).take 44) 173993750000 0 = true :=
    take_step (n := 2) (t := 44) (b := 32358) rfl rfl ArealUCore.ArealUK.chunk_16178 s79
  have s77 : leavesOK ctxLitU 173706250000 0 ((leaves.drop 32354).take 46) 173993750000 0 = true :=
    take_step (n := 2) (t := 46) (b := 32356) rfl rfl ArealUCore.ArealUK.chunk_16177 s78
  have s76 : leavesOK ctxLitU 347387500000 1 ((leaves.drop 32352).take 48) 173993750000 0 = true :=
    take_step (n := 2) (t := 48) (b := 32354) rfl rfl ArealUCore.ArealUK.chunk_16176 s77
  have s75 : leavesOK ctxLitU 173675000000 0 ((leaves.drop 32350).take 50) 173993750000 0 = true :=
    take_step (n := 2) (t := 50) (b := 32352) rfl rfl ArealUCore.ArealUK.chunk_16175 s76
  have s74 : leavesOK ctxLitU 173662500000 0 ((leaves.drop 32348).take 52) 173993750000 0 = true :=
    take_step (n := 2) (t := 52) (b := 32350) rfl rfl ArealUCore.ArealUK.chunk_16174 s75
  have s73 : leavesOK ctxLitU 173650000000 0 ((leaves.drop 32346).take 54) 173993750000 0 = true :=
    take_step (n := 2) (t := 54) (b := 32348) rfl rfl ArealUCore.ArealUK.chunk_16173 s74
  have s72 : leavesOK ctxLitU 173625000000 0 ((leaves.drop 32344).take 56) 173993750000 0 = true :=
    take_step (n := 2) (t := 56) (b := 32346) rfl rfl ArealUCore.ArealUK.chunk_16172 s73
  have s71 : leavesOK ctxLitU 173612500000 0 ((leaves.drop 32342).take 58) 173993750000 0 = true :=
    take_step (n := 2) (t := 58) (b := 32344) rfl rfl ArealUCore.ArealUK.chunk_16171 s72
  have s70 : leavesOK ctxLitU 173600000000 0 ((leaves.drop 32340).take 60) 173993750000 0 = true :=
    take_step (n := 2) (t := 60) (b := 32342) rfl rfl ArealUCore.ArealUK.chunk_16170 s71
  have s69 : leavesOK ctxLitU 173587500000 0 ((leaves.drop 32338).take 62) 173993750000 0 = true :=
    take_step (n := 2) (t := 62) (b := 32340) rfl rfl ArealUCore.ArealUK.chunk_16169 s70
  have s68 : leavesOK ctxLitU 173575000000 0 ((leaves.drop 32336).take 64) 173993750000 0 = true :=
    take_step (n := 2) (t := 64) (b := 32338) rfl rfl ArealUCore.ArealUK.chunk_16168 s69
  have s67 : leavesOK ctxLitU 173562500000 0 ((leaves.drop 32334).take 66) 173993750000 0 = true :=
    take_step (n := 2) (t := 66) (b := 32336) rfl rfl ArealUCore.ArealUK.chunk_16167 s68
  have s66 : leavesOK ctxLitU 173550000000 0 ((leaves.drop 32332).take 68) 173993750000 0 = true :=
    take_step (n := 2) (t := 68) (b := 32334) rfl rfl ArealUCore.ArealUK.chunk_16166 s67
  have s65 : leavesOK ctxLitU 173537500000 0 ((leaves.drop 32330).take 70) 173993750000 0 = true :=
    take_step (n := 2) (t := 70) (b := 32332) rfl rfl ArealUCore.ArealUK.chunk_16165 s66
  have s64 : leavesOK ctxLitU 173525000000 0 ((leaves.drop 32328).take 72) 173993750000 0 = true :=
    take_step (n := 2) (t := 72) (b := 32330) rfl rfl ArealUCore.ArealUK.chunk_16164 s65
  have s63 : leavesOK ctxLitU 173500000000 0 ((leaves.drop 32326).take 74) 173993750000 0 = true :=
    take_step (n := 2) (t := 74) (b := 32328) rfl rfl ArealUCore.ArealUK.chunk_16163 s64
  have s62 : leavesOK ctxLitU 346975000000 1 ((leaves.drop 32324).take 76) 173993750000 0 = true :=
    take_step (n := 2) (t := 76) (b := 32326) rfl rfl ArealUCore.ArealUK.chunk_16162 s63
  have s61 : leavesOK ctxLitU 346950000000 1 ((leaves.drop 32322).take 78) 173993750000 0 = true :=
    take_step (n := 2) (t := 78) (b := 32324) rfl rfl ArealUCore.ArealUK.chunk_16161 s62
  have s60 : leavesOK ctxLitU 173462500000 0 ((leaves.drop 32320).take 80) 173993750000 0 = true :=
    take_step (n := 2) (t := 80) (b := 32322) rfl rfl ArealUCore.ArealUK.chunk_16160 s61
  have s59 : leavesOK ctxLitU 173450000000 0 ((leaves.drop 32318).take 82) 173993750000 0 = true :=
    take_step (n := 2) (t := 82) (b := 32320) rfl rfl ArealUCore.ArealUK.chunk_16159 s60
  have s58 : leavesOK ctxLitU 173437500000 0 ((leaves.drop 32316).take 84) 173993750000 0 = true :=
    take_step (n := 2) (t := 84) (b := 32318) rfl rfl ArealUCore.ArealUK.chunk_16158 s59
  have s57 : leavesOK ctxLitU 346856250000 1 ((leaves.drop 32314).take 86) 173993750000 0 = true :=
    take_step (n := 2) (t := 86) (b := 32316) rfl rfl ArealUCore.ArealUK.chunk_16157 s58
  have s56 : leavesOK ctxLitU 173412500000 0 ((leaves.drop 32312).take 88) 173993750000 0 = true :=
    take_step (n := 2) (t := 88) (b := 32314) rfl rfl ArealUCore.ArealUK.chunk_16156 s57
  have s55 : leavesOK ctxLitU 346775000000 1 ((leaves.drop 32310).take 90) 173993750000 0 = true :=
    take_step (n := 2) (t := 90) (b := 32312) rfl rfl ArealUCore.ArealUK.chunk_16155 s56
  have s54 : leavesOK ctxLitU 346725000000 1 ((leaves.drop 32308).take 92) 173993750000 0 = true :=
    take_step (n := 2) (t := 92) (b := 32310) rfl rfl ArealUCore.ArealUK.chunk_16154 s55
  have s53 : leavesOK ctxLitU 346675000000 1 ((leaves.drop 32306).take 94) 173993750000 0 = true :=
    take_step (n := 2) (t := 94) (b := 32308) rfl rfl ArealUCore.ArealUK.chunk_16153 s54
  have s52 : leavesOK ctxLitU 346625000000 1 ((leaves.drop 32304).take 96) 173993750000 0 = true :=
    take_step (n := 2) (t := 96) (b := 32306) rfl rfl ArealUCore.ArealUK.chunk_16152 s53
  have s51 : leavesOK ctxLitU 346587500000 1 ((leaves.drop 32302).take 98) 173993750000 0 = true :=
    take_step (n := 2) (t := 98) (b := 32304) rfl rfl ArealUCore.ArealUK.chunk_16151 s52
  have s50 : leavesOK ctxLitU 173275000000 0 ((leaves.drop 32300).take 100) 173993750000 0 = true :=
    take_step (n := 2) (t := 100) (b := 32302) rfl rfl ArealUCore.ArealUK.chunk_16150 s51
  have s49 : leavesOK ctxLitU 173262500000 0 ((leaves.drop 32298).take 102) 173993750000 0 = true :=
    take_step (n := 2) (t := 102) (b := 32300) rfl rfl ArealUCore.ArealUK.chunk_16149 s50
  have s48 : leavesOK ctxLitU 173250000000 0 ((leaves.drop 32296).take 104) 173993750000 0 = true :=
    take_step (n := 2) (t := 104) (b := 32298) rfl rfl ArealUCore.ArealUK.chunk_16148 s49
  have s47 : leavesOK ctxLitU 173237500000 0 ((leaves.drop 32294).take 106) 173993750000 0 = true :=
    take_step (n := 2) (t := 106) (b := 32296) rfl rfl ArealUCore.ArealUK.chunk_16147 s48
  have s46 : leavesOK ctxLitU 173225000000 0 ((leaves.drop 32292).take 108) 173993750000 0 = true :=
    take_step (n := 2) (t := 108) (b := 32294) rfl rfl ArealUCore.ArealUK.chunk_16146 s47
  have s45 : leavesOK ctxLitU 173212500000 0 ((leaves.drop 32290).take 110) 173993750000 0 = true :=
    take_step (n := 2) (t := 110) (b := 32292) rfl rfl ArealUCore.ArealUK.chunk_16145 s46
  have s44 : leavesOK ctxLitU 173200000000 0 ((leaves.drop 32288).take 112) 173993750000 0 = true :=
    take_step (n := 2) (t := 112) (b := 32290) rfl rfl ArealUCore.ArealUK.chunk_16144 s45
  have s43 : leavesOK ctxLitU 173187500000 0 ((leaves.drop 32286).take 114) 173993750000 0 = true :=
    take_step (n := 2) (t := 114) (b := 32288) rfl rfl ArealUCore.ArealUK.chunk_16143 s44
  have s42 : leavesOK ctxLitU 173175000000 0 ((leaves.drop 32284).take 116) 173993750000 0 = true :=
    take_step (n := 2) (t := 116) (b := 32286) rfl rfl ArealUCore.ArealUK.chunk_16142 s43
  have s41 : leavesOK ctxLitU 173150000000 0 ((leaves.drop 32282).take 118) 173993750000 0 = true :=
    take_step (n := 2) (t := 118) (b := 32284) rfl rfl ArealUCore.ArealUK.chunk_16141 s42
  have s40 : leavesOK ctxLitU 173137500000 0 ((leaves.drop 32280).take 120) 173993750000 0 = true :=
    take_step (n := 2) (t := 120) (b := 32282) rfl rfl ArealUCore.ArealUK.chunk_16140 s41
  have s39 : leavesOK ctxLitU 173125000000 0 ((leaves.drop 32278).take 122) 173993750000 0 = true :=
    take_step (n := 2) (t := 122) (b := 32280) rfl rfl ArealUCore.ArealUK.chunk_16139 s40
  have s38 : leavesOK ctxLitU 173112500000 0 ((leaves.drop 32276).take 124) 173993750000 0 = true :=
    take_step (n := 2) (t := 124) (b := 32278) rfl rfl ArealUCore.ArealUK.chunk_16138 s39
  have s37 : leavesOK ctxLitU 173100000000 0 ((leaves.drop 32274).take 126) 173993750000 0 = true :=
    take_step (n := 2) (t := 126) (b := 32276) rfl rfl ArealUCore.ArealUK.chunk_16137 s38
  have s36 : leavesOK ctxLitU 173075000000 0 ((leaves.drop 32272).take 128) 173993750000 0 = true :=
    take_step (n := 2) (t := 128) (b := 32274) rfl rfl ArealUCore.ArealUK.chunk_16136 s37
  have s35 : leavesOK ctxLitU 173062500000 0 ((leaves.drop 32270).take 130) 173993750000 0 = true :=
    take_step (n := 2) (t := 130) (b := 32272) rfl rfl ArealUCore.ArealUK.chunk_16135 s36
  have s34 : leavesOK ctxLitU 173050000000 0 ((leaves.drop 32268).take 132) 173993750000 0 = true :=
    take_step (n := 2) (t := 132) (b := 32270) rfl rfl ArealUCore.ArealUK.chunk_16134 s35
  have s33 : leavesOK ctxLitU 173037500000 0 ((leaves.drop 32266).take 134) 173993750000 0 = true :=
    take_step (n := 2) (t := 134) (b := 32268) rfl rfl ArealUCore.ArealUK.chunk_16133 s34
  have s32 : leavesOK ctxLitU 173025000000 0 ((leaves.drop 32264).take 136) 173993750000 0 = true :=
    take_step (n := 2) (t := 136) (b := 32266) rfl rfl ArealUCore.ArealUK.chunk_16132 s33
  have s31 : leavesOK ctxLitU 173012500000 0 ((leaves.drop 32262).take 138) 173993750000 0 = true :=
    take_step (n := 2) (t := 138) (b := 32264) rfl rfl ArealUCore.ArealUK.chunk_16131 s32
  have s30 : leavesOK ctxLitU 173000000000 0 ((leaves.drop 32260).take 140) 173993750000 0 = true :=
    take_step (n := 2) (t := 140) (b := 32262) rfl rfl ArealUCore.ArealUK.chunk_16130 s31
  have s29 : leavesOK ctxLitU 172987500000 0 ((leaves.drop 32258).take 142) 173993750000 0 = true :=
    take_step (n := 2) (t := 142) (b := 32260) rfl rfl ArealUCore.ArealUK.chunk_16129 s30
  have s28 : leavesOK ctxLitU 172975000000 0 ((leaves.drop 32256).take 144) 173993750000 0 = true :=
    take_step (n := 2) (t := 144) (b := 32258) rfl rfl ArealUCore.ArealUK.chunk_16128 s29
  have s27 : leavesOK ctxLitU 172962500000 0 ((leaves.drop 32254).take 146) 173993750000 0 = true :=
    take_step (n := 2) (t := 146) (b := 32256) rfl rfl ArealUCore.ArealUK.chunk_16127 s28
  have s26 : leavesOK ctxLitU 172950000000 0 ((leaves.drop 32252).take 148) 173993750000 0 = true :=
    take_step (n := 2) (t := 148) (b := 32254) rfl rfl ArealUCore.ArealUK.chunk_16126 s27
  have s25 : leavesOK ctxLitU 172937500000 0 ((leaves.drop 32250).take 150) 173993750000 0 = true :=
    take_step (n := 2) (t := 150) (b := 32252) rfl rfl ArealUCore.ArealUK.chunk_16125 s26
  have s24 : leavesOK ctxLitU 172925000000 0 ((leaves.drop 32248).take 152) 173993750000 0 = true :=
    take_step (n := 2) (t := 152) (b := 32250) rfl rfl ArealUCore.ArealUK.chunk_16124 s25
  have s23 : leavesOK ctxLitU 345812500000 1 ((leaves.drop 32246).take 154) 173993750000 0 = true :=
    take_step (n := 2) (t := 154) (b := 32248) rfl rfl ArealUCore.ArealUK.chunk_16123 s24
  have s22 : leavesOK ctxLitU 345775000000 1 ((leaves.drop 32244).take 156) 173993750000 0 = true :=
    take_step (n := 2) (t := 156) (b := 32246) rfl rfl ArealUCore.ArealUK.chunk_16122 s23
  have s21 : leavesOK ctxLitU 172862500000 0 ((leaves.drop 32242).take 158) 173993750000 0 = true :=
    take_step (n := 2) (t := 158) (b := 32244) rfl rfl ArealUCore.ArealUK.chunk_16121 s22
  have s20 : leavesOK ctxLitU 172843750000 0 ((leaves.drop 32240).take 160) 173993750000 0 = true :=
    take_step (n := 2) (t := 160) (b := 32242) rfl rfl ArealUCore.ArealUK.chunk_16120 s21
  have s19 : leavesOK ctxLitU 345668750000 1 ((leaves.drop 32238).take 162) 173993750000 0 = true :=
    take_step (n := 2) (t := 162) (b := 32240) rfl rfl ArealUCore.ArealUK.chunk_16119 s20
  have s18 : leavesOK ctxLitU 345656250000 1 ((leaves.drop 32236).take 164) 173993750000 0 = true :=
    take_step (n := 2) (t := 164) (b := 32238) rfl rfl ArealUCore.ArealUK.chunk_16118 s19
  have s17 : leavesOK ctxLitU 172812500000 0 ((leaves.drop 32234).take 166) 173993750000 0 = true :=
    take_step (n := 2) (t := 166) (b := 32236) rfl rfl ArealUCore.ArealUK.chunk_16117 s18
  have s16 : leavesOK ctxLitU 172787500000 0 ((leaves.drop 32232).take 168) 173993750000 0 = true :=
    take_step (n := 2) (t := 168) (b := 32234) rfl rfl ArealUCore.ArealUK.chunk_16116 s17
  have s15 : leavesOK ctxLitU 172768750000 0 ((leaves.drop 32230).take 170) 173993750000 0 = true :=
    take_step (n := 2) (t := 170) (b := 32232) rfl rfl ArealUCore.ArealUK.chunk_16115 s16
  have s14 : leavesOK ctxLitU 172756250000 0 ((leaves.drop 32228).take 172) 173993750000 0 = true :=
    take_step (n := 2) (t := 172) (b := 32230) rfl rfl ArealUCore.ArealUK.chunk_16114 s15
  have s13 : leavesOK ctxLitU 172743750000 0 ((leaves.drop 32226).take 174) 173993750000 0 = true :=
    take_step (n := 2) (t := 174) (b := 32228) rfl rfl ArealUCore.ArealUK.chunk_16113 s14
  have s12 : leavesOK ctxLitU 172731250000 0 ((leaves.drop 32224).take 176) 173993750000 0 = true :=
    take_step (n := 2) (t := 176) (b := 32226) rfl rfl ArealUCore.ArealUK.chunk_16112 s13
  have s11 : leavesOK ctxLitU 172712500000 0 ((leaves.drop 32222).take 178) 173993750000 0 = true :=
    take_step (n := 2) (t := 178) (b := 32224) rfl rfl ArealUCore.ArealUK.chunk_16111 s12
  have s10 : leavesOK ctxLitU 172687500000 0 ((leaves.drop 32220).take 180) 173993750000 0 = true :=
    take_step (n := 2) (t := 180) (b := 32222) rfl rfl ArealUCore.ArealUK.chunk_16110 s11
  have s9 : leavesOK ctxLitU 172668750000 0 ((leaves.drop 32218).take 182) 173993750000 0 = true :=
    take_step (n := 2) (t := 182) (b := 32220) rfl rfl ArealUCore.ArealUK.chunk_16109 s10
  have s8 : leavesOK ctxLitU 172656250000 0 ((leaves.drop 32216).take 184) 173993750000 0 = true :=
    take_step (n := 2) (t := 184) (b := 32218) rfl rfl ArealUCore.ArealUK.chunk_16108 s9
  have s7 : leavesOK ctxLitU 172643750000 0 ((leaves.drop 32214).take 186) 173993750000 0 = true :=
    take_step (n := 2) (t := 186) (b := 32216) rfl rfl ArealUCore.ArealUK.chunk_16107 s8
  have s6 : leavesOK ctxLitU 172631250000 0 ((leaves.drop 32212).take 188) 173993750000 0 = true :=
    take_step (n := 2) (t := 188) (b := 32214) rfl rfl ArealUCore.ArealUK.chunk_16106 s7
  have s5 : leavesOK ctxLitU 172618750000 0 ((leaves.drop 32210).take 190) 173993750000 0 = true :=
    take_step (n := 2) (t := 190) (b := 32212) rfl rfl ArealUCore.ArealUK.chunk_16105 s6
  have s4 : leavesOK ctxLitU 172606250000 0 ((leaves.drop 32208).take 192) 173993750000 0 = true :=
    take_step (n := 2) (t := 192) (b := 32210) rfl rfl ArealUCore.ArealUK.chunk_16104 s5
  have s3 : leavesOK ctxLitU 172593750000 0 ((leaves.drop 32206).take 194) 173993750000 0 = true :=
    take_step (n := 2) (t := 194) (b := 32208) rfl rfl ArealUCore.ArealUK.chunk_16103 s4
  have s2 : leavesOK ctxLitU 172581250000 0 ((leaves.drop 32204).take 196) 173993750000 0 = true :=
    take_step (n := 2) (t := 196) (b := 32206) rfl rfl ArealUCore.ArealUK.chunk_16102 s3
  have s1 : leavesOK ctxLitU 172568750000 0 ((leaves.drop 32202).take 198) 173993750000 0 = true :=
    take_step (n := 2) (t := 198) (b := 32204) rfl rfl ArealUCore.ArealUK.chunk_16101 s2
  have s0 : leavesOK ctxLitU 172556250000 0 ((leaves.drop 32200).take 200) 173993750000 0 = true :=
    take_step (n := 2) (t := 200) (b := 32202) rfl rfl ArealUCore.ArealUK.chunk_16100 s1
  exact s0

end Areal.UCert

import ArealUK.Chunk12100
import ArealUK.Chunk12101
import ArealUK.Chunk12102
import ArealUK.Chunk12103
import ArealUK.Chunk12104
import ArealUK.Chunk12105
import ArealUK.Chunk12106
import ArealUK.Chunk12107
import ArealUK.Chunk12108
import ArealUK.Chunk12109
import ArealUK.Chunk12110
import ArealUK.Chunk12111
import ArealUK.Chunk12112
import ArealUK.Chunk12113
import ArealUK.Chunk12114
import ArealUK.Chunk12115
import ArealUK.Chunk12116
import ArealUK.Chunk12117
import ArealUK.Chunk12118
import ArealUK.Chunk12119
import ArealUK.Chunk12120
import ArealUK.Chunk12121
import ArealUK.Chunk12122
import ArealUK.Chunk12123
import ArealUK.Chunk12124
import ArealUK.Chunk12125
import ArealUK.Chunk12126
import ArealUK.Chunk12127
import ArealUK.Chunk12128
import ArealUK.Chunk12129
import ArealUK.Chunk12130
import ArealUK.Chunk12131
import ArealUK.Chunk12132
import ArealUK.Chunk12133
import ArealUK.Chunk12134
import ArealUK.Chunk12135
import ArealUK.Chunk12136
import ArealUK.Chunk12137
import ArealUK.Chunk12138
import ArealUK.Chunk12139
import ArealUK.Chunk12140
import ArealUK.Chunk12141
import ArealUK.Chunk12142
import ArealUK.Chunk12143
import ArealUK.Chunk12144
import ArealUK.Chunk12145
import ArealUK.Chunk12146
import ArealUK.Chunk12147
import ArealUK.Chunk12148
import ArealUK.Chunk12149
import ArealUK.Chunk12150
import ArealUK.Chunk12151
import ArealUK.Chunk12152
import ArealUK.Chunk12153
import ArealUK.Chunk12154
import ArealUK.Chunk12155
import ArealUK.Chunk12156
import ArealUK.Chunk12157
import ArealUK.Chunk12158
import ArealUK.Chunk12159
import ArealUK.Chunk12160
import ArealUK.Chunk12161
import ArealUK.Chunk12162
import ArealUK.Chunk12163
import ArealUK.Chunk12164
import ArealUK.Chunk12165
import ArealUK.Chunk12166
import ArealUK.Chunk12167
import ArealUK.Chunk12168
import ArealUK.Chunk12169
import ArealUK.Chunk12170
import ArealUK.Chunk12171
import ArealUK.Chunk12172
import ArealUK.Chunk12173
import ArealUK.Chunk12174
import ArealUK.Chunk12175
import ArealUK.Chunk12176
import ArealUK.Chunk12177
import ArealUK.Chunk12178
import ArealUK.Chunk12179
import ArealUK.Chunk12180
import ArealUK.Chunk12181
import ArealUK.Chunk12182
import ArealUK.Chunk12183
import ArealUK.Chunk12184
import ArealUK.Chunk12185
import ArealUK.Chunk12186
import ArealUK.Chunk12187
import ArealUK.Chunk12188
import ArealUK.Chunk12189
import ArealUK.Chunk12190
import ArealUK.Chunk12191
import ArealUK.Chunk12192
import ArealUK.Chunk12193
import ArealUK.Chunk12194
import ArealUK.Chunk12195
import ArealUK.Chunk12196
import ArealUK.Chunk12197
import ArealUK.Chunk12198
import ArealUK.Chunk12199
import Areal.UCert.LeavesKGen

/-! Group 121 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_121 : leavesOK ctxLitU 481750000000 2 ((leaves.drop 24200).take 200) 487775000000 2 = true := by
  have s99 := ArealUCore.ArealUK.chunk_12199
  have s98 : leavesOK ctxLitU 487675000000 2 ((leaves.drop 24396).take 4) 487775000000 2 = true :=
    take_step (n := 2) (t := 4) (b := 24398) rfl rfl ArealUCore.ArealUK.chunk_12198 s99
  have s97 : leavesOK ctxLitU 487625000000 2 ((leaves.drop 24394).take 6) 487775000000 2 = true :=
    take_step (n := 2) (t := 6) (b := 24396) rfl rfl ArealUCore.ArealUK.chunk_12197 s98
  have s96 : leavesOK ctxLitU 487575000000 2 ((leaves.drop 24392).take 8) 487775000000 2 = true :=
    take_step (n := 2) (t := 8) (b := 24394) rfl rfl ArealUCore.ArealUK.chunk_12196 s97
  have s95 : leavesOK ctxLitU 487525000000 2 ((leaves.drop 24390).take 10) 487775000000 2 = true :=
    take_step (n := 2) (t := 10) (b := 24392) rfl rfl ArealUCore.ArealUK.chunk_12195 s96
  have s94 : leavesOK ctxLitU 487475000000 2 ((leaves.drop 24388).take 12) 487775000000 2 = true :=
    take_step (n := 2) (t := 12) (b := 24390) rfl rfl ArealUCore.ArealUK.chunk_12194 s95
  have s93 : leavesOK ctxLitU 487425000000 2 ((leaves.drop 24386).take 14) 487775000000 2 = true :=
    take_step (n := 2) (t := 14) (b := 24388) rfl rfl ArealUCore.ArealUK.chunk_12193 s94
  have s92 : leavesOK ctxLitU 487375000000 2 ((leaves.drop 24384).take 16) 487775000000 2 = true :=
    take_step (n := 2) (t := 16) (b := 24386) rfl rfl ArealUCore.ArealUK.chunk_12192 s93
  have s91 : leavesOK ctxLitU 487325000000 2 ((leaves.drop 24382).take 18) 487775000000 2 = true :=
    take_step (n := 2) (t := 18) (b := 24384) rfl rfl ArealUCore.ArealUK.chunk_12191 s92
  have s90 : leavesOK ctxLitU 487275000000 2 ((leaves.drop 24380).take 20) 487775000000 2 = true :=
    take_step (n := 2) (t := 20) (b := 24382) rfl rfl ArealUCore.ArealUK.chunk_12190 s91
  have s89 : leavesOK ctxLitU 487225000000 2 ((leaves.drop 24378).take 22) 487775000000 2 = true :=
    take_step (n := 2) (t := 22) (b := 24380) rfl rfl ArealUCore.ArealUK.chunk_12189 s90
  have s88 : leavesOK ctxLitU 487175000000 2 ((leaves.drop 24376).take 24) 487775000000 2 = true :=
    take_step (n := 2) (t := 24) (b := 24378) rfl rfl ArealUCore.ArealUK.chunk_12188 s89
  have s87 : leavesOK ctxLitU 487125000000 2 ((leaves.drop 24374).take 26) 487775000000 2 = true :=
    take_step (n := 2) (t := 26) (b := 24376) rfl rfl ArealUCore.ArealUK.chunk_12187 s88
  have s86 : leavesOK ctxLitU 487075000000 2 ((leaves.drop 24372).take 28) 487775000000 2 = true :=
    take_step (n := 2) (t := 28) (b := 24374) rfl rfl ArealUCore.ArealUK.chunk_12186 s87
  have s85 : leavesOK ctxLitU 487025000000 2 ((leaves.drop 24370).take 30) 487775000000 2 = true :=
    take_step (n := 2) (t := 30) (b := 24372) rfl rfl ArealUCore.ArealUK.chunk_12185 s86
  have s84 : leavesOK ctxLitU 486975000000 2 ((leaves.drop 24368).take 32) 487775000000 2 = true :=
    take_step (n := 2) (t := 32) (b := 24370) rfl rfl ArealUCore.ArealUK.chunk_12184 s85
  have s83 : leavesOK ctxLitU 486925000000 2 ((leaves.drop 24366).take 34) 487775000000 2 = true :=
    take_step (n := 2) (t := 34) (b := 24368) rfl rfl ArealUCore.ArealUK.chunk_12183 s84
  have s82 : leavesOK ctxLitU 486875000000 2 ((leaves.drop 24364).take 36) 487775000000 2 = true :=
    take_step (n := 2) (t := 36) (b := 24366) rfl rfl ArealUCore.ArealUK.chunk_12182 s83
  have s81 : leavesOK ctxLitU 486825000000 2 ((leaves.drop 24362).take 38) 487775000000 2 = true :=
    take_step (n := 2) (t := 38) (b := 24364) rfl rfl ArealUCore.ArealUK.chunk_12181 s82
  have s80 : leavesOK ctxLitU 486775000000 2 ((leaves.drop 24360).take 40) 487775000000 2 = true :=
    take_step (n := 2) (t := 40) (b := 24362) rfl rfl ArealUCore.ArealUK.chunk_12180 s81
  have s79 : leavesOK ctxLitU 486725000000 2 ((leaves.drop 24358).take 42) 487775000000 2 = true :=
    take_step (n := 2) (t := 42) (b := 24360) rfl rfl ArealUCore.ArealUK.chunk_12179 s80
  have s78 : leavesOK ctxLitU 486675000000 2 ((leaves.drop 24356).take 44) 487775000000 2 = true :=
    take_step (n := 2) (t := 44) (b := 24358) rfl rfl ArealUCore.ArealUK.chunk_12178 s79
  have s77 : leavesOK ctxLitU 486625000000 2 ((leaves.drop 24354).take 46) 487775000000 2 = true :=
    take_step (n := 2) (t := 46) (b := 24356) rfl rfl ArealUCore.ArealUK.chunk_12177 s78
  have s76 : leavesOK ctxLitU 486575000000 2 ((leaves.drop 24352).take 48) 487775000000 2 = true :=
    take_step (n := 2) (t := 48) (b := 24354) rfl rfl ArealUCore.ArealUK.chunk_12176 s77
  have s75 : leavesOK ctxLitU 486525000000 2 ((leaves.drop 24350).take 50) 487775000000 2 = true :=
    take_step (n := 2) (t := 50) (b := 24352) rfl rfl ArealUCore.ArealUK.chunk_12175 s76
  have s74 : leavesOK ctxLitU 486475000000 2 ((leaves.drop 24348).take 52) 487775000000 2 = true :=
    take_step (n := 2) (t := 52) (b := 24350) rfl rfl ArealUCore.ArealUK.chunk_12174 s75
  have s73 : leavesOK ctxLitU 486425000000 2 ((leaves.drop 24346).take 54) 487775000000 2 = true :=
    take_step (n := 2) (t := 54) (b := 24348) rfl rfl ArealUCore.ArealUK.chunk_12173 s74
  have s72 : leavesOK ctxLitU 486375000000 2 ((leaves.drop 24344).take 56) 487775000000 2 = true :=
    take_step (n := 2) (t := 56) (b := 24346) rfl rfl ArealUCore.ArealUK.chunk_12172 s73
  have s71 : leavesOK ctxLitU 486325000000 2 ((leaves.drop 24342).take 58) 487775000000 2 = true :=
    take_step (n := 2) (t := 58) (b := 24344) rfl rfl ArealUCore.ArealUK.chunk_12171 s72
  have s70 : leavesOK ctxLitU 486275000000 2 ((leaves.drop 24340).take 60) 487775000000 2 = true :=
    take_step (n := 2) (t := 60) (b := 24342) rfl rfl ArealUCore.ArealUK.chunk_12170 s71
  have s69 : leavesOK ctxLitU 486225000000 2 ((leaves.drop 24338).take 62) 487775000000 2 = true :=
    take_step (n := 2) (t := 62) (b := 24340) rfl rfl ArealUCore.ArealUK.chunk_12169 s70
  have s68 : leavesOK ctxLitU 486175000000 2 ((leaves.drop 24336).take 64) 487775000000 2 = true :=
    take_step (n := 2) (t := 64) (b := 24338) rfl rfl ArealUCore.ArealUK.chunk_12168 s69
  have s67 : leavesOK ctxLitU 486125000000 2 ((leaves.drop 24334).take 66) 487775000000 2 = true :=
    take_step (n := 2) (t := 66) (b := 24336) rfl rfl ArealUCore.ArealUK.chunk_12167 s68
  have s66 : leavesOK ctxLitU 486075000000 2 ((leaves.drop 24332).take 68) 487775000000 2 = true :=
    take_step (n := 2) (t := 68) (b := 24334) rfl rfl ArealUCore.ArealUK.chunk_12166 s67
  have s65 : leavesOK ctxLitU 486025000000 2 ((leaves.drop 24330).take 70) 487775000000 2 = true :=
    take_step (n := 2) (t := 70) (b := 24332) rfl rfl ArealUCore.ArealUK.chunk_12165 s66
  have s64 : leavesOK ctxLitU 485975000000 2 ((leaves.drop 24328).take 72) 487775000000 2 = true :=
    take_step (n := 2) (t := 72) (b := 24330) rfl rfl ArealUCore.ArealUK.chunk_12164 s65
  have s63 : leavesOK ctxLitU 485925000000 2 ((leaves.drop 24326).take 74) 487775000000 2 = true :=
    take_step (n := 2) (t := 74) (b := 24328) rfl rfl ArealUCore.ArealUK.chunk_12163 s64
  have s62 : leavesOK ctxLitU 485875000000 2 ((leaves.drop 24324).take 76) 487775000000 2 = true :=
    take_step (n := 2) (t := 76) (b := 24326) rfl rfl ArealUCore.ArealUK.chunk_12162 s63
  have s61 : leavesOK ctxLitU 242900000000 1 ((leaves.drop 24322).take 78) 487775000000 2 = true :=
    take_step (n := 2) (t := 78) (b := 24324) rfl rfl ArealUCore.ArealUK.chunk_12161 s62
  have s60 : leavesOK ctxLitU 242850000000 1 ((leaves.drop 24320).take 80) 487775000000 2 = true :=
    take_step (n := 2) (t := 80) (b := 24322) rfl rfl ArealUCore.ArealUK.chunk_12160 s61
  have s59 : leavesOK ctxLitU 485650000000 2 ((leaves.drop 24318).take 82) 487775000000 2 = true :=
    take_step (n := 2) (t := 82) (b := 24320) rfl rfl ArealUCore.ArealUK.chunk_12159 s60
  have s58 : leavesOK ctxLitU 485600000000 2 ((leaves.drop 24316).take 84) 487775000000 2 = true :=
    take_step (n := 2) (t := 84) (b := 24318) rfl rfl ArealUCore.ArealUK.chunk_12158 s59
  have s57 : leavesOK ctxLitU 485550000000 2 ((leaves.drop 24314).take 86) 487775000000 2 = true :=
    take_step (n := 2) (t := 86) (b := 24316) rfl rfl ArealUCore.ArealUK.chunk_12157 s58
  have s56 : leavesOK ctxLitU 485500000000 2 ((leaves.drop 24312).take 88) 487775000000 2 = true :=
    take_step (n := 2) (t := 88) (b := 24314) rfl rfl ArealUCore.ArealUK.chunk_12156 s57
  have s55 : leavesOK ctxLitU 242700000000 1 ((leaves.drop 24310).take 90) 487775000000 2 = true :=
    take_step (n := 2) (t := 90) (b := 24312) rfl rfl ArealUCore.ArealUK.chunk_12155 s56
  have s54 : leavesOK ctxLitU 485325000000 2 ((leaves.drop 24308).take 92) 487775000000 2 = true :=
    take_step (n := 2) (t := 92) (b := 24310) rfl rfl ArealUCore.ArealUK.chunk_12154 s55
  have s53 : leavesOK ctxLitU 485275000000 2 ((leaves.drop 24306).take 94) 487775000000 2 = true :=
    take_step (n := 2) (t := 94) (b := 24308) rfl rfl ArealUCore.ArealUK.chunk_12153 s54
  have s52 : leavesOK ctxLitU 485225000000 2 ((leaves.drop 24304).take 96) 487775000000 2 = true :=
    take_step (n := 2) (t := 96) (b := 24306) rfl rfl ArealUCore.ArealUK.chunk_12152 s53
  have s51 : leavesOK ctxLitU 485175000000 2 ((leaves.drop 24302).take 98) 487775000000 2 = true :=
    take_step (n := 2) (t := 98) (b := 24304) rfl rfl ArealUCore.ArealUK.chunk_12151 s52
  have s50 : leavesOK ctxLitU 485125000000 2 ((leaves.drop 24300).take 100) 487775000000 2 = true :=
    take_step (n := 2) (t := 100) (b := 24302) rfl rfl ArealUCore.ArealUK.chunk_12150 s51
  have s49 : leavesOK ctxLitU 485075000000 2 ((leaves.drop 24298).take 102) 487775000000 2 = true :=
    take_step (n := 2) (t := 102) (b := 24300) rfl rfl ArealUCore.ArealUK.chunk_12149 s50
  have s48 : leavesOK ctxLitU 485025000000 2 ((leaves.drop 24296).take 104) 487775000000 2 = true :=
    take_step (n := 2) (t := 104) (b := 24298) rfl rfl ArealUCore.ArealUK.chunk_12148 s49
  have s47 : leavesOK ctxLitU 484975000000 2 ((leaves.drop 24294).take 106) 487775000000 2 = true :=
    take_step (n := 2) (t := 106) (b := 24296) rfl rfl ArealUCore.ArealUK.chunk_12147 s48
  have s46 : leavesOK ctxLitU 484925000000 2 ((leaves.drop 24292).take 108) 487775000000 2 = true :=
    take_step (n := 2) (t := 108) (b := 24294) rfl rfl ArealUCore.ArealUK.chunk_12146 s47
  have s45 : leavesOK ctxLitU 121212500000 0 ((leaves.drop 24290).take 110) 487775000000 2 = true :=
    take_step (n := 2) (t := 110) (b := 24292) rfl rfl ArealUCore.ArealUK.chunk_12145 s46
  have s44 : leavesOK ctxLitU 242400000000 1 ((leaves.drop 24288).take 112) 487775000000 2 = true :=
    take_step (n := 2) (t := 112) (b := 24290) rfl rfl ArealUCore.ArealUK.chunk_12144 s45
  have s43 : leavesOK ctxLitU 242387500000 1 ((leaves.drop 24286).take 114) 487775000000 2 = true :=
    take_step (n := 2) (t := 114) (b := 24288) rfl rfl ArealUCore.ArealUK.chunk_12143 s44
  have s42 : leavesOK ctxLitU 121181250000 0 ((leaves.drop 24284).take 116) 487775000000 2 = true :=
    take_step (n := 2) (t := 116) (b := 24286) rfl rfl ArealUCore.ArealUK.chunk_12142 s43
  have s41 : leavesOK ctxLitU 121168750000 0 ((leaves.drop 24282).take 118) 487775000000 2 = true :=
    take_step (n := 2) (t := 118) (b := 24284) rfl rfl ArealUCore.ArealUK.chunk_12141 s42
  have s40 : leavesOK ctxLitU 121156250000 0 ((leaves.drop 24280).take 120) 487775000000 2 = true :=
    take_step (n := 2) (t := 120) (b := 24282) rfl rfl ArealUCore.ArealUK.chunk_12140 s41
  have s39 : leavesOK ctxLitU 121143750000 0 ((leaves.drop 24278).take 122) 487775000000 2 = true :=
    take_step (n := 2) (t := 122) (b := 24280) rfl rfl ArealUCore.ArealUK.chunk_12139 s40
  have s38 : leavesOK ctxLitU 121131250000 0 ((leaves.drop 24276).take 124) 487775000000 2 = true :=
    take_step (n := 2) (t := 124) (b := 24278) rfl rfl ArealUCore.ArealUK.chunk_12138 s39
  have s37 : leavesOK ctxLitU 121118750000 0 ((leaves.drop 24274).take 126) 487775000000 2 = true :=
    take_step (n := 2) (t := 126) (b := 24276) rfl rfl ArealUCore.ArealUK.chunk_12137 s38
  have s36 : leavesOK ctxLitU 121106250000 0 ((leaves.drop 24272).take 128) 487775000000 2 = true :=
    take_step (n := 2) (t := 128) (b := 24274) rfl rfl ArealUCore.ArealUK.chunk_12136 s37
  have s35 : leavesOK ctxLitU 121087500000 0 ((leaves.drop 24270).take 130) 487775000000 2 = true :=
    take_step (n := 2) (t := 130) (b := 24272) rfl rfl ArealUCore.ArealUK.chunk_12135 s36
  have s34 : leavesOK ctxLitU 121050000000 0 ((leaves.drop 24268).take 132) 487775000000 2 = true :=
    take_step (n := 2) (t := 132) (b := 24270) rfl rfl ArealUCore.ArealUK.chunk_12134 s35
  have s33 : leavesOK ctxLitU 121000000000 0 ((leaves.drop 24266).take 134) 487775000000 2 = true :=
    take_step (n := 2) (t := 134) (b := 24268) rfl rfl ArealUCore.ArealUK.chunk_12133 s34
  have s32 : leavesOK ctxLitU 120950000000 0 ((leaves.drop 24264).take 136) 487775000000 2 = true :=
    take_step (n := 2) (t := 136) (b := 24266) rfl rfl ArealUCore.ArealUK.chunk_12132 s33
  have s31 : leavesOK ctxLitU 495383982475011 12 ((leaves.drop 24262).take 138) 487775000000 2 = true :=
    take_step (n := 2) (t := 138) (b := 24264) rfl rfl ArealUCore.ArealUK.chunk_12131 s32
  have s30 : leavesOK ctxLitU 120900000000 0 ((leaves.drop 24260).take 140) 487775000000 2 = true :=
    take_step (n := 2) (t := 140) (b := 24262) rfl rfl ArealUCore.ArealUK.chunk_12130 s31
  have s29 : leavesOK ctxLitU 120850000000 0 ((leaves.drop 24258).take 142) 487775000000 2 = true :=
    take_step (n := 2) (t := 142) (b := 24260) rfl rfl ArealUCore.ArealUK.chunk_12129 s30
  have s28 : leavesOK ctxLitU 120812500000 0 ((leaves.drop 24256).take 144) 487775000000 2 = true :=
    take_step (n := 2) (t := 144) (b := 24258) rfl rfl ArealUCore.ArealUK.chunk_12128 s29
  have s27 : leavesOK ctxLitU 120793750000 0 ((leaves.drop 24254).take 146) 487775000000 2 = true :=
    take_step (n := 2) (t := 146) (b := 24256) rfl rfl ArealUCore.ArealUK.chunk_12127 s28
  have s26 : leavesOK ctxLitU 120781250000 0 ((leaves.drop 24252).take 148) 487775000000 2 = true :=
    take_step (n := 2) (t := 148) (b := 24254) rfl rfl ArealUCore.ArealUK.chunk_12126 s27
  have s25 : leavesOK ctxLitU 120768750000 0 ((leaves.drop 24250).take 150) 487775000000 2 = true :=
    take_step (n := 2) (t := 150) (b := 24252) rfl rfl ArealUCore.ArealUK.chunk_12125 s26
  have s24 : leavesOK ctxLitU 120756250000 0 ((leaves.drop 24248).take 152) 487775000000 2 = true :=
    take_step (n := 2) (t := 152) (b := 24250) rfl rfl ArealUCore.ArealUK.chunk_12124 s25
  have s23 : leavesOK ctxLitU 120743750000 0 ((leaves.drop 24246).take 154) 487775000000 2 = true :=
    take_step (n := 2) (t := 154) (b := 24248) rfl rfl ArealUCore.ArealUK.chunk_12123 s24
  have s22 : leavesOK ctxLitU 120731250000 0 ((leaves.drop 24244).take 156) 487775000000 2 = true :=
    take_step (n := 2) (t := 156) (b := 24246) rfl rfl ArealUCore.ArealUK.chunk_12122 s23
  have s21 : leavesOK ctxLitU 120718750000 0 ((leaves.drop 24242).take 158) 487775000000 2 = true :=
    take_step (n := 2) (t := 158) (b := 24244) rfl rfl ArealUCore.ArealUK.chunk_12121 s22
  have s20 : leavesOK ctxLitU 120706250000 0 ((leaves.drop 24240).take 160) 487775000000 2 = true :=
    take_step (n := 2) (t := 160) (b := 24242) rfl rfl ArealUCore.ArealUK.chunk_12120 s21
  have s19 : leavesOK ctxLitU 241400000000 1 ((leaves.drop 24238).take 162) 487775000000 2 = true :=
    take_step (n := 2) (t := 162) (b := 24240) rfl rfl ArealUCore.ArealUK.chunk_12119 s20
  have s18 : leavesOK ctxLitU 965575000000 3 ((leaves.drop 24236).take 164) 487775000000 2 = true :=
    take_step (n := 2) (t := 164) (b := 24238) rfl rfl ArealUCore.ArealUK.chunk_12118 s19
  have s17 : leavesOK ctxLitU 241375000000 1 ((leaves.drop 24234).take 166) 487775000000 2 = true :=
    take_step (n := 2) (t := 166) (b := 24236) rfl rfl ArealUCore.ArealUK.chunk_12117 s18
  have s16 : leavesOK ctxLitU 241325000000 1 ((leaves.drop 24232).take 168) 487775000000 2 = true :=
    take_step (n := 2) (t := 168) (b := 24234) rfl rfl ArealUCore.ArealUK.chunk_12116 s17
  have s15 : leavesOK ctxLitU 482600000000 2 ((leaves.drop 24230).take 170) 487775000000 2 = true :=
    take_step (n := 2) (t := 170) (b := 24232) rfl rfl ArealUCore.ArealUK.chunk_12115 s16
  have s14 : leavesOK ctxLitU 482550000000 2 ((leaves.drop 24228).take 172) 487775000000 2 = true :=
    take_step (n := 2) (t := 172) (b := 24230) rfl rfl ArealUCore.ArealUK.chunk_12114 s15
  have s13 : leavesOK ctxLitU 482500000000 2 ((leaves.drop 24226).take 174) 487775000000 2 = true :=
    take_step (n := 2) (t := 174) (b := 24228) rfl rfl ArealUCore.ArealUK.chunk_12113 s14
  have s12 : leavesOK ctxLitU 482450000000 2 ((leaves.drop 24224).take 176) 487775000000 2 = true :=
    take_step (n := 2) (t := 176) (b := 24226) rfl rfl ArealUCore.ArealUK.chunk_12112 s13
  have s11 : leavesOK ctxLitU 482400000000 2 ((leaves.drop 24222).take 178) 487775000000 2 = true :=
    take_step (n := 2) (t := 178) (b := 24224) rfl rfl ArealUCore.ArealUK.chunk_12111 s12
  have s10 : leavesOK ctxLitU 482350000000 2 ((leaves.drop 24220).take 180) 487775000000 2 = true :=
    take_step (n := 2) (t := 180) (b := 24222) rfl rfl ArealUCore.ArealUK.chunk_12110 s11
  have s9 : leavesOK ctxLitU 241125000000 1 ((leaves.drop 24218).take 182) 487775000000 2 = true :=
    take_step (n := 2) (t := 182) (b := 24220) rfl rfl ArealUCore.ArealUK.chunk_12109 s10
  have s8 : leavesOK ctxLitU 241075000000 1 ((leaves.drop 24216).take 184) 487775000000 2 = true :=
    take_step (n := 2) (t := 184) (b := 24218) rfl rfl ArealUCore.ArealUK.chunk_12108 s9
  have s7 : leavesOK ctxLitU 482100000000 2 ((leaves.drop 24214).take 186) 487775000000 2 = true :=
    take_step (n := 2) (t := 186) (b := 24216) rfl rfl ArealUCore.ArealUK.chunk_12107 s8
  have s6 : leavesOK ctxLitU 482050000000 2 ((leaves.drop 24212).take 188) 487775000000 2 = true :=
    take_step (n := 2) (t := 188) (b := 24214) rfl rfl ArealUCore.ArealUK.chunk_12106 s7
  have s5 : leavesOK ctxLitU 482000000000 2 ((leaves.drop 24210).take 190) 487775000000 2 = true :=
    take_step (n := 2) (t := 190) (b := 24212) rfl rfl ArealUCore.ArealUK.chunk_12105 s6
  have s4 : leavesOK ctxLitU 481950000000 2 ((leaves.drop 24208).take 192) 487775000000 2 = true :=
    take_step (n := 2) (t := 192) (b := 24210) rfl rfl ArealUCore.ArealUK.chunk_12104 s5
  have s3 : leavesOK ctxLitU 481900000000 2 ((leaves.drop 24206).take 194) 487775000000 2 = true :=
    take_step (n := 2) (t := 194) (b := 24208) rfl rfl ArealUCore.ArealUK.chunk_12103 s4
  have s2 : leavesOK ctxLitU 481850000000 2 ((leaves.drop 24204).take 196) 487775000000 2 = true :=
    take_step (n := 2) (t := 196) (b := 24206) rfl rfl ArealUCore.ArealUK.chunk_12102 s3
  have s1 : leavesOK ctxLitU 481800000000 2 ((leaves.drop 24202).take 198) 487775000000 2 = true :=
    take_step (n := 2) (t := 198) (b := 24204) rfl rfl ArealUCore.ArealUK.chunk_12101 s2
  have s0 : leavesOK ctxLitU 481750000000 2 ((leaves.drop 24200).take 200) 487775000000 2 = true :=
    take_step (n := 2) (t := 200) (b := 24202) rfl rfl ArealUCore.ArealUK.chunk_12100 s1
  exact s0

end Areal.UCert

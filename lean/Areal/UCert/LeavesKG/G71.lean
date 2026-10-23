import ArealUK.Chunk7100
import ArealUK.Chunk7101
import ArealUK.Chunk7102
import ArealUK.Chunk7103
import ArealUK.Chunk7104
import ArealUK.Chunk7105
import ArealUK.Chunk7106
import ArealUK.Chunk7107
import ArealUK.Chunk7108
import ArealUK.Chunk7109
import ArealUK.Chunk7110
import ArealUK.Chunk7111
import ArealUK.Chunk7112
import ArealUK.Chunk7113
import ArealUK.Chunk7114
import ArealUK.Chunk7115
import ArealUK.Chunk7116
import ArealUK.Chunk7117
import ArealUK.Chunk7118
import ArealUK.Chunk7119
import ArealUK.Chunk7120
import ArealUK.Chunk7121
import ArealUK.Chunk7122
import ArealUK.Chunk7123
import ArealUK.Chunk7124
import ArealUK.Chunk7125
import ArealUK.Chunk7126
import ArealUK.Chunk7127
import ArealUK.Chunk7128
import ArealUK.Chunk7129
import ArealUK.Chunk7130
import ArealUK.Chunk7131
import ArealUK.Chunk7132
import ArealUK.Chunk7133
import ArealUK.Chunk7134
import ArealUK.Chunk7135
import ArealUK.Chunk7136
import ArealUK.Chunk7137
import ArealUK.Chunk7138
import ArealUK.Chunk7139
import ArealUK.Chunk7140
import ArealUK.Chunk7141
import ArealUK.Chunk7142
import ArealUK.Chunk7143
import ArealUK.Chunk7144
import ArealUK.Chunk7145
import ArealUK.Chunk7146
import ArealUK.Chunk7147
import ArealUK.Chunk7148
import ArealUK.Chunk7149
import ArealUK.Chunk7150
import ArealUK.Chunk7151
import ArealUK.Chunk7152
import ArealUK.Chunk7153
import ArealUK.Chunk7154
import ArealUK.Chunk7155
import ArealUK.Chunk7156
import ArealUK.Chunk7157
import ArealUK.Chunk7158
import ArealUK.Chunk7159
import ArealUK.Chunk7160
import ArealUK.Chunk7161
import ArealUK.Chunk7162
import ArealUK.Chunk7163
import ArealUK.Chunk7164
import ArealUK.Chunk7165
import ArealUK.Chunk7166
import ArealUK.Chunk7167
import ArealUK.Chunk7168
import ArealUK.Chunk7169
import ArealUK.Chunk7170
import ArealUK.Chunk7171
import ArealUK.Chunk7172
import ArealUK.Chunk7173
import ArealUK.Chunk7174
import ArealUK.Chunk7175
import ArealUK.Chunk7176
import ArealUK.Chunk7177
import ArealUK.Chunk7178
import ArealUK.Chunk7179
import ArealUK.Chunk7180
import ArealUK.Chunk7181
import ArealUK.Chunk7182
import ArealUK.Chunk7183
import ArealUK.Chunk7184
import ArealUK.Chunk7185
import ArealUK.Chunk7186
import ArealUK.Chunk7187
import ArealUK.Chunk7188
import ArealUK.Chunk7189
import ArealUK.Chunk7190
import ArealUK.Chunk7191
import ArealUK.Chunk7192
import ArealUK.Chunk7193
import ArealUK.Chunk7194
import ArealUK.Chunk7195
import ArealUK.Chunk7196
import ArealUK.Chunk7197
import ArealUK.Chunk7198
import ArealUK.Chunk7199
import Areal.UCert.LeavesKGen

/-! Group 71 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_71 : leavesOK ctxLitU 473625000000 3 ((leaves.drop 14200).take 200) 479100000000 3 = true := by
  have s99 := ArealUCore.ArealUK.chunk_7199
  have s98 : leavesOK ctxLitU 479000000000 3 ((leaves.drop 14396).take 4) 479100000000 3 = true :=
    take_step (n := 2) (t := 4) (b := 14398) rfl rfl ArealUCore.ArealUK.chunk_7198 s99
  have s97 : leavesOK ctxLitU 478950000000 3 ((leaves.drop 14394).take 6) 479100000000 3 = true :=
    take_step (n := 2) (t := 6) (b := 14396) rfl rfl ArealUCore.ArealUK.chunk_7197 s98
  have s96 : leavesOK ctxLitU 478900000000 3 ((leaves.drop 14392).take 8) 479100000000 3 = true :=
    take_step (n := 2) (t := 8) (b := 14394) rfl rfl ArealUCore.ArealUK.chunk_7196 s97
  have s95 : leavesOK ctxLitU 239400000000 2 ((leaves.drop 14390).take 10) 479100000000 3 = true :=
    take_step (n := 2) (t := 10) (b := 14392) rfl rfl ArealUCore.ArealUK.chunk_7195 s96
  have s94 : leavesOK ctxLitU 478725000000 3 ((leaves.drop 14388).take 12) 479100000000 3 = true :=
    take_step (n := 2) (t := 12) (b := 14390) rfl rfl ArealUCore.ArealUK.chunk_7194 s95
  have s93 : leavesOK ctxLitU 478675000000 3 ((leaves.drop 14386).take 14) 479100000000 3 = true :=
    take_step (n := 2) (t := 14) (b := 14388) rfl rfl ArealUCore.ArealUK.chunk_7193 s94
  have s92 : leavesOK ctxLitU 478625000000 3 ((leaves.drop 14384).take 16) 479100000000 3 = true :=
    take_step (n := 2) (t := 16) (b := 14386) rfl rfl ArealUCore.ArealUK.chunk_7192 s93
  have s91 : leavesOK ctxLitU 478575000000 3 ((leaves.drop 14382).take 18) 479100000000 3 = true :=
    take_step (n := 2) (t := 18) (b := 14384) rfl rfl ArealUCore.ArealUK.chunk_7191 s92
  have s90 : leavesOK ctxLitU 478525000000 3 ((leaves.drop 14380).take 20) 479100000000 3 = true :=
    take_step (n := 2) (t := 20) (b := 14382) rfl rfl ArealUCore.ArealUK.chunk_7190 s91
  have s89 : leavesOK ctxLitU 478475000000 3 ((leaves.drop 14378).take 22) 479100000000 3 = true :=
    take_step (n := 2) (t := 22) (b := 14380) rfl rfl ArealUCore.ArealUK.chunk_7189 s90
  have s88 : leavesOK ctxLitU 478425000000 3 ((leaves.drop 14376).take 24) 479100000000 3 = true :=
    take_step (n := 2) (t := 24) (b := 14378) rfl rfl ArealUCore.ArealUK.chunk_7188 s89
  have s87 : leavesOK ctxLitU 478375000000 3 ((leaves.drop 14374).take 26) 479100000000 3 = true :=
    take_step (n := 2) (t := 26) (b := 14376) rfl rfl ArealUCore.ArealUK.chunk_7187 s88
  have s86 : leavesOK ctxLitU 478325000000 3 ((leaves.drop 14372).take 28) 479100000000 3 = true :=
    take_step (n := 2) (t := 28) (b := 14374) rfl rfl ArealUCore.ArealUK.chunk_7186 s87
  have s85 : leavesOK ctxLitU 478275000000 3 ((leaves.drop 14370).take 30) 479100000000 3 = true :=
    take_step (n := 2) (t := 30) (b := 14372) rfl rfl ArealUCore.ArealUK.chunk_7185 s86
  have s84 : leavesOK ctxLitU 478225000000 3 ((leaves.drop 14368).take 32) 479100000000 3 = true :=
    take_step (n := 2) (t := 32) (b := 14370) rfl rfl ArealUCore.ArealUK.chunk_7184 s85
  have s83 : leavesOK ctxLitU 478175000000 3 ((leaves.drop 14366).take 34) 479100000000 3 = true :=
    take_step (n := 2) (t := 34) (b := 14368) rfl rfl ArealUCore.ArealUK.chunk_7183 s84
  have s82 : leavesOK ctxLitU 478125000000 3 ((leaves.drop 14364).take 36) 479100000000 3 = true :=
    take_step (n := 2) (t := 36) (b := 14366) rfl rfl ArealUCore.ArealUK.chunk_7182 s83
  have s81 : leavesOK ctxLitU 239025000000 2 ((leaves.drop 14362).take 38) 479100000000 3 = true :=
    take_step (n := 2) (t := 38) (b := 14364) rfl rfl ArealUCore.ArealUK.chunk_7181 s82
  have s80 : leavesOK ctxLitU 238975000000 2 ((leaves.drop 14360).take 40) 479100000000 3 = true :=
    take_step (n := 2) (t := 40) (b := 14362) rfl rfl ArealUCore.ArealUK.chunk_7180 s81
  have s79 : leavesOK ctxLitU 477875000000 3 ((leaves.drop 14358).take 42) 479100000000 3 = true :=
    take_step (n := 2) (t := 42) (b := 14360) rfl rfl ArealUCore.ArealUK.chunk_7179 s80
  have s78 : leavesOK ctxLitU 477825000000 3 ((leaves.drop 14356).take 44) 479100000000 3 = true :=
    take_step (n := 2) (t := 44) (b := 14358) rfl rfl ArealUCore.ArealUK.chunk_7178 s79
  have s77 : leavesOK ctxLitU 477775000000 3 ((leaves.drop 14354).take 46) 479100000000 3 = true :=
    take_step (n := 2) (t := 46) (b := 14356) rfl rfl ArealUCore.ArealUK.chunk_7177 s78
  have s76 : leavesOK ctxLitU 477725000000 3 ((leaves.drop 14352).take 48) 479100000000 3 = true :=
    take_step (n := 2) (t := 48) (b := 14354) rfl rfl ArealUCore.ArealUK.chunk_7176 s77
  have s75 : leavesOK ctxLitU 477675000000 3 ((leaves.drop 14350).take 50) 479100000000 3 = true :=
    take_step (n := 2) (t := 50) (b := 14352) rfl rfl ArealUCore.ArealUK.chunk_7175 s76
  have s74 : leavesOK ctxLitU 477625000000 3 ((leaves.drop 14348).take 52) 479100000000 3 = true :=
    take_step (n := 2) (t := 52) (b := 14350) rfl rfl ArealUCore.ArealUK.chunk_7174 s75
  have s73 : leavesOK ctxLitU 477575000000 3 ((leaves.drop 14346).take 54) 479100000000 3 = true :=
    take_step (n := 2) (t := 54) (b := 14348) rfl rfl ArealUCore.ArealUK.chunk_7173 s74
  have s72 : leavesOK ctxLitU 477525000000 3 ((leaves.drop 14344).take 56) 479100000000 3 = true :=
    take_step (n := 2) (t := 56) (b := 14346) rfl rfl ArealUCore.ArealUK.chunk_7172 s73
  have s71 : leavesOK ctxLitU 477475000000 3 ((leaves.drop 14342).take 58) 479100000000 3 = true :=
    take_step (n := 2) (t := 58) (b := 14344) rfl rfl ArealUCore.ArealUK.chunk_7171 s72
  have s70 : leavesOK ctxLitU 477425000000 3 ((leaves.drop 14340).take 60) 479100000000 3 = true :=
    take_step (n := 2) (t := 60) (b := 14342) rfl rfl ArealUCore.ArealUK.chunk_7170 s71
  have s69 : leavesOK ctxLitU 477375000000 3 ((leaves.drop 14338).take 62) 479100000000 3 = true :=
    take_step (n := 2) (t := 62) (b := 14340) rfl rfl ArealUCore.ArealUK.chunk_7169 s70
  have s68 : leavesOK ctxLitU 477325000000 3 ((leaves.drop 14336).take 64) 479100000000 3 = true :=
    take_step (n := 2) (t := 64) (b := 14338) rfl rfl ArealUCore.ArealUK.chunk_7168 s69
  have s67 : leavesOK ctxLitU 477275000000 3 ((leaves.drop 14334).take 66) 479100000000 3 = true :=
    take_step (n := 2) (t := 66) (b := 14336) rfl rfl ArealUCore.ArealUK.chunk_7167 s68
  have s66 : leavesOK ctxLitU 238600000000 2 ((leaves.drop 14332).take 68) 479100000000 3 = true :=
    take_step (n := 2) (t := 68) (b := 14334) rfl rfl ArealUCore.ArealUK.chunk_7166 s67
  have s65 : leavesOK ctxLitU 477125000000 3 ((leaves.drop 14330).take 70) 479100000000 3 = true :=
    take_step (n := 2) (t := 70) (b := 14332) rfl rfl ArealUCore.ArealUK.chunk_7165 s66
  have s64 : leavesOK ctxLitU 477075000000 3 ((leaves.drop 14328).take 72) 479100000000 3 = true :=
    take_step (n := 2) (t := 72) (b := 14330) rfl rfl ArealUCore.ArealUK.chunk_7164 s65
  have s63 : leavesOK ctxLitU 477025000000 3 ((leaves.drop 14326).take 74) 479100000000 3 = true :=
    take_step (n := 2) (t := 74) (b := 14328) rfl rfl ArealUCore.ArealUK.chunk_7163 s64
  have s62 : leavesOK ctxLitU 476975000000 3 ((leaves.drop 14324).take 76) 479100000000 3 = true :=
    take_step (n := 2) (t := 76) (b := 14326) rfl rfl ArealUCore.ArealUK.chunk_7162 s63
  have s61 : leavesOK ctxLitU 476925000000 3 ((leaves.drop 14322).take 78) 479100000000 3 = true :=
    take_step (n := 2) (t := 78) (b := 14324) rfl rfl ArealUCore.ArealUK.chunk_7161 s62
  have s60 : leavesOK ctxLitU 476875000000 3 ((leaves.drop 14320).take 80) 479100000000 3 = true :=
    take_step (n := 2) (t := 80) (b := 14322) rfl rfl ArealUCore.ArealUK.chunk_7160 s61
  have s59 : leavesOK ctxLitU 476825000000 3 ((leaves.drop 14318).take 82) 479100000000 3 = true :=
    take_step (n := 2) (t := 82) (b := 14320) rfl rfl ArealUCore.ArealUK.chunk_7159 s60
  have s58 : leavesOK ctxLitU 476775000000 3 ((leaves.drop 14316).take 84) 479100000000 3 = true :=
    take_step (n := 2) (t := 84) (b := 14318) rfl rfl ArealUCore.ArealUK.chunk_7158 s59
  have s57 : leavesOK ctxLitU 476725000000 3 ((leaves.drop 14314).take 86) 479100000000 3 = true :=
    take_step (n := 2) (t := 86) (b := 14316) rfl rfl ArealUCore.ArealUK.chunk_7157 s58
  have s56 : leavesOK ctxLitU 476675000000 3 ((leaves.drop 14312).take 88) 479100000000 3 = true :=
    take_step (n := 2) (t := 88) (b := 14314) rfl rfl ArealUCore.ArealUK.chunk_7156 s57
  have s55 : leavesOK ctxLitU 476625000000 3 ((leaves.drop 14310).take 90) 479100000000 3 = true :=
    take_step (n := 2) (t := 90) (b := 14312) rfl rfl ArealUCore.ArealUK.chunk_7155 s56
  have s54 : leavesOK ctxLitU 476575000000 3 ((leaves.drop 14308).take 92) 479100000000 3 = true :=
    take_step (n := 2) (t := 92) (b := 14310) rfl rfl ArealUCore.ArealUK.chunk_7154 s55
  have s53 : leavesOK ctxLitU 476525000000 3 ((leaves.drop 14306).take 94) 479100000000 3 = true :=
    take_step (n := 2) (t := 94) (b := 14308) rfl rfl ArealUCore.ArealUK.chunk_7153 s54
  have s52 : leavesOK ctxLitU 476475000000 3 ((leaves.drop 14304).take 96) 479100000000 3 = true :=
    take_step (n := 2) (t := 96) (b := 14306) rfl rfl ArealUCore.ArealUK.chunk_7152 s53
  have s51 : leavesOK ctxLitU 238200000000 2 ((leaves.drop 14302).take 98) 479100000000 3 = true :=
    take_step (n := 2) (t := 98) (b := 14304) rfl rfl ArealUCore.ArealUK.chunk_7151 s52
  have s50 : leavesOK ctxLitU 476325000000 3 ((leaves.drop 14300).take 100) 479100000000 3 = true :=
    take_step (n := 2) (t := 100) (b := 14302) rfl rfl ArealUCore.ArealUK.chunk_7150 s51
  have s49 : leavesOK ctxLitU 476275000000 3 ((leaves.drop 14298).take 102) 479100000000 3 = true :=
    take_step (n := 2) (t := 102) (b := 14300) rfl rfl ArealUCore.ArealUK.chunk_7149 s50
  have s48 : leavesOK ctxLitU 476225000000 3 ((leaves.drop 14296).take 104) 479100000000 3 = true :=
    take_step (n := 2) (t := 104) (b := 14298) rfl rfl ArealUCore.ArealUK.chunk_7148 s49
  have s47 : leavesOK ctxLitU 476175000000 3 ((leaves.drop 14294).take 106) 479100000000 3 = true :=
    take_step (n := 2) (t := 106) (b := 14296) rfl rfl ArealUCore.ArealUK.chunk_7147 s48
  have s46 : leavesOK ctxLitU 476125000000 3 ((leaves.drop 14292).take 108) 479100000000 3 = true :=
    take_step (n := 2) (t := 108) (b := 14294) rfl rfl ArealUCore.ArealUK.chunk_7146 s47
  have s45 : leavesOK ctxLitU 476075000000 3 ((leaves.drop 14290).take 110) 479100000000 3 = true :=
    take_step (n := 2) (t := 110) (b := 14292) rfl rfl ArealUCore.ArealUK.chunk_7145 s46
  have s44 : leavesOK ctxLitU 476025000000 3 ((leaves.drop 14288).take 112) 479100000000 3 = true :=
    take_step (n := 2) (t := 112) (b := 14290) rfl rfl ArealUCore.ArealUK.chunk_7144 s45
  have s43 : leavesOK ctxLitU 475975000000 3 ((leaves.drop 14286).take 114) 479100000000 3 = true :=
    take_step (n := 2) (t := 114) (b := 14288) rfl rfl ArealUCore.ArealUK.chunk_7143 s44
  have s42 : leavesOK ctxLitU 475925000000 3 ((leaves.drop 14284).take 116) 479100000000 3 = true :=
    take_step (n := 2) (t := 116) (b := 14286) rfl rfl ArealUCore.ArealUK.chunk_7142 s43
  have s41 : leavesOK ctxLitU 475875000000 3 ((leaves.drop 14282).take 118) 479100000000 3 = true :=
    take_step (n := 2) (t := 118) (b := 14284) rfl rfl ArealUCore.ArealUK.chunk_7141 s42
  have s40 : leavesOK ctxLitU 475825000000 3 ((leaves.drop 14280).take 120) 479100000000 3 = true :=
    take_step (n := 2) (t := 120) (b := 14282) rfl rfl ArealUCore.ArealUK.chunk_7140 s41
  have s39 : leavesOK ctxLitU 475775000000 3 ((leaves.drop 14278).take 122) 479100000000 3 = true :=
    take_step (n := 2) (t := 122) (b := 14280) rfl rfl ArealUCore.ArealUK.chunk_7139 s40
  have s38 : leavesOK ctxLitU 475725000000 3 ((leaves.drop 14276).take 124) 479100000000 3 = true :=
    take_step (n := 2) (t := 124) (b := 14278) rfl rfl ArealUCore.ArealUK.chunk_7138 s39
  have s37 : leavesOK ctxLitU 475675000000 3 ((leaves.drop 14274).take 126) 479100000000 3 = true :=
    take_step (n := 2) (t := 126) (b := 14276) rfl rfl ArealUCore.ArealUK.chunk_7137 s38
  have s36 : leavesOK ctxLitU 237800000000 2 ((leaves.drop 14272).take 128) 479100000000 3 = true :=
    take_step (n := 2) (t := 128) (b := 14274) rfl rfl ArealUCore.ArealUK.chunk_7136 s37
  have s35 : leavesOK ctxLitU 475525000000 3 ((leaves.drop 14270).take 130) 479100000000 3 = true :=
    take_step (n := 2) (t := 130) (b := 14272) rfl rfl ArealUCore.ArealUK.chunk_7135 s36
  have s34 : leavesOK ctxLitU 475475000000 3 ((leaves.drop 14268).take 132) 479100000000 3 = true :=
    take_step (n := 2) (t := 132) (b := 14270) rfl rfl ArealUCore.ArealUK.chunk_7134 s35
  have s33 : leavesOK ctxLitU 475425000000 3 ((leaves.drop 14266).take 134) 479100000000 3 = true :=
    take_step (n := 2) (t := 134) (b := 14268) rfl rfl ArealUCore.ArealUK.chunk_7133 s34
  have s32 : leavesOK ctxLitU 475375000000 3 ((leaves.drop 14264).take 136) 479100000000 3 = true :=
    take_step (n := 2) (t := 136) (b := 14266) rfl rfl ArealUCore.ArealUK.chunk_7132 s33
  have s31 : leavesOK ctxLitU 475325000000 3 ((leaves.drop 14262).take 138) 479100000000 3 = true :=
    take_step (n := 2) (t := 138) (b := 14264) rfl rfl ArealUCore.ArealUK.chunk_7131 s32
  have s30 : leavesOK ctxLitU 475275000000 3 ((leaves.drop 14260).take 140) 479100000000 3 = true :=
    take_step (n := 2) (t := 140) (b := 14262) rfl rfl ArealUCore.ArealUK.chunk_7130 s31
  have s29 : leavesOK ctxLitU 475225000000 3 ((leaves.drop 14258).take 142) 479100000000 3 = true :=
    take_step (n := 2) (t := 142) (b := 14260) rfl rfl ArealUCore.ArealUK.chunk_7129 s30
  have s28 : leavesOK ctxLitU 475175000000 3 ((leaves.drop 14256).take 144) 479100000000 3 = true :=
    take_step (n := 2) (t := 144) (b := 14258) rfl rfl ArealUCore.ArealUK.chunk_7128 s29
  have s27 : leavesOK ctxLitU 475125000000 3 ((leaves.drop 14254).take 146) 479100000000 3 = true :=
    take_step (n := 2) (t := 146) (b := 14256) rfl rfl ArealUCore.ArealUK.chunk_7127 s28
  have s26 : leavesOK ctxLitU 475075000000 3 ((leaves.drop 14252).take 148) 479100000000 3 = true :=
    take_step (n := 2) (t := 148) (b := 14254) rfl rfl ArealUCore.ArealUK.chunk_7126 s27
  have s25 : leavesOK ctxLitU 475025000000 3 ((leaves.drop 14250).take 150) 479100000000 3 = true :=
    take_step (n := 2) (t := 150) (b := 14252) rfl rfl ArealUCore.ArealUK.chunk_7125 s26
  have s24 : leavesOK ctxLitU 474975000000 3 ((leaves.drop 14248).take 152) 479100000000 3 = true :=
    take_step (n := 2) (t := 152) (b := 14250) rfl rfl ArealUCore.ArealUK.chunk_7124 s25
  have s23 : leavesOK ctxLitU 474925000000 3 ((leaves.drop 14246).take 154) 479100000000 3 = true :=
    take_step (n := 2) (t := 154) (b := 14248) rfl rfl ArealUCore.ArealUK.chunk_7123 s24
  have s22 : leavesOK ctxLitU 474875000000 3 ((leaves.drop 14244).take 156) 479100000000 3 = true :=
    take_step (n := 2) (t := 156) (b := 14246) rfl rfl ArealUCore.ArealUK.chunk_7122 s23
  have s21 : leavesOK ctxLitU 237400000000 2 ((leaves.drop 14242).take 158) 479100000000 3 = true :=
    take_step (n := 2) (t := 158) (b := 14244) rfl rfl ArealUCore.ArealUK.chunk_7121 s22
  have s20 : leavesOK ctxLitU 237350000000 2 ((leaves.drop 14240).take 160) 479100000000 3 = true :=
    take_step (n := 2) (t := 160) (b := 14242) rfl rfl ArealUCore.ArealUK.chunk_7120 s21
  have s19 : leavesOK ctxLitU 474650000000 3 ((leaves.drop 14238).take 162) 479100000000 3 = true :=
    take_step (n := 2) (t := 162) (b := 14240) rfl rfl ArealUCore.ArealUK.chunk_7119 s20
  have s18 : leavesOK ctxLitU 474600000000 3 ((leaves.drop 14236).take 164) 479100000000 3 = true :=
    take_step (n := 2) (t := 164) (b := 14238) rfl rfl ArealUCore.ArealUK.chunk_7118 s19
  have s17 : leavesOK ctxLitU 474550000000 3 ((leaves.drop 14234).take 166) 479100000000 3 = true :=
    take_step (n := 2) (t := 166) (b := 14236) rfl rfl ArealUCore.ArealUK.chunk_7117 s18
  have s16 : leavesOK ctxLitU 474500000000 3 ((leaves.drop 14232).take 168) 479100000000 3 = true :=
    take_step (n := 2) (t := 168) (b := 14234) rfl rfl ArealUCore.ArealUK.chunk_7116 s17
  have s15 : leavesOK ctxLitU 474450000000 3 ((leaves.drop 14230).take 170) 479100000000 3 = true :=
    take_step (n := 2) (t := 170) (b := 14232) rfl rfl ArealUCore.ArealUK.chunk_7115 s16
  have s14 : leavesOK ctxLitU 474400000000 3 ((leaves.drop 14228).take 172) 479100000000 3 = true :=
    take_step (n := 2) (t := 172) (b := 14230) rfl rfl ArealUCore.ArealUK.chunk_7114 s15
  have s13 : leavesOK ctxLitU 474350000000 3 ((leaves.drop 14226).take 174) 479100000000 3 = true :=
    take_step (n := 2) (t := 174) (b := 14228) rfl rfl ArealUCore.ArealUK.chunk_7113 s14
  have s12 : leavesOK ctxLitU 474300000000 3 ((leaves.drop 14224).take 176) 479100000000 3 = true :=
    take_step (n := 2) (t := 176) (b := 14226) rfl rfl ArealUCore.ArealUK.chunk_7112 s13
  have s11 : leavesOK ctxLitU 474250000000 3 ((leaves.drop 14222).take 178) 479100000000 3 = true :=
    take_step (n := 2) (t := 178) (b := 14224) rfl rfl ArealUCore.ArealUK.chunk_7111 s12
  have s10 : leavesOK ctxLitU 474200000000 3 ((leaves.drop 14220).take 180) 479100000000 3 = true :=
    take_step (n := 2) (t := 180) (b := 14222) rfl rfl ArealUCore.ArealUK.chunk_7110 s11
  have s9 : leavesOK ctxLitU 474150000000 3 ((leaves.drop 14218).take 182) 479100000000 3 = true :=
    take_step (n := 2) (t := 182) (b := 14220) rfl rfl ArealUCore.ArealUK.chunk_7109 s10
  have s8 : leavesOK ctxLitU 474100000000 3 ((leaves.drop 14216).take 184) 479100000000 3 = true :=
    take_step (n := 2) (t := 184) (b := 14218) rfl rfl ArealUCore.ArealUK.chunk_7108 s9
  have s7 : leavesOK ctxLitU 237000000000 2 ((leaves.drop 14214).take 186) 479100000000 3 = true :=
    take_step (n := 2) (t := 186) (b := 14216) rfl rfl ArealUCore.ArealUK.chunk_7107 s8
  have s6 : leavesOK ctxLitU 473925000000 3 ((leaves.drop 14212).take 188) 479100000000 3 = true :=
    take_step (n := 2) (t := 188) (b := 14214) rfl rfl ArealUCore.ArealUK.chunk_7106 s7
  have s5 : leavesOK ctxLitU 473875000000 3 ((leaves.drop 14210).take 190) 479100000000 3 = true :=
    take_step (n := 2) (t := 190) (b := 14212) rfl rfl ArealUCore.ArealUK.chunk_7105 s6
  have s4 : leavesOK ctxLitU 473825000000 3 ((leaves.drop 14208).take 192) 479100000000 3 = true :=
    take_step (n := 2) (t := 192) (b := 14210) rfl rfl ArealUCore.ArealUK.chunk_7104 s5
  have s3 : leavesOK ctxLitU 473775000000 3 ((leaves.drop 14206).take 194) 479100000000 3 = true :=
    take_step (n := 2) (t := 194) (b := 14208) rfl rfl ArealUCore.ArealUK.chunk_7103 s4
  have s2 : leavesOK ctxLitU 473725000000 3 ((leaves.drop 14204).take 196) 479100000000 3 = true :=
    take_step (n := 2) (t := 196) (b := 14206) rfl rfl ArealUCore.ArealUK.chunk_7102 s3
  have s1 : leavesOK ctxLitU 473675000000 3 ((leaves.drop 14202).take 198) 479100000000 3 = true :=
    take_step (n := 2) (t := 198) (b := 14204) rfl rfl ArealUCore.ArealUK.chunk_7101 s2
  have s0 : leavesOK ctxLitU 473625000000 3 ((leaves.drop 14200).take 200) 479100000000 3 = true :=
    take_step (n := 2) (t := 200) (b := 14202) rfl rfl ArealUCore.ArealUK.chunk_7100 s1
  exact s0

end Areal.UCert

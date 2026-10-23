import ArealUK.Chunk13200
import ArealUK.Chunk13201
import ArealUK.Chunk13202
import ArealUK.Chunk13203
import ArealUK.Chunk13204
import ArealUK.Chunk13205
import ArealUK.Chunk13206
import ArealUK.Chunk13207
import ArealUK.Chunk13208
import ArealUK.Chunk13209
import ArealUK.Chunk13210
import ArealUK.Chunk13211
import ArealUK.Chunk13212
import ArealUK.Chunk13213
import ArealUK.Chunk13214
import ArealUK.Chunk13215
import ArealUK.Chunk13216
import ArealUK.Chunk13217
import ArealUK.Chunk13218
import ArealUK.Chunk13219
import ArealUK.Chunk13220
import ArealUK.Chunk13221
import ArealUK.Chunk13222
import ArealUK.Chunk13223
import ArealUK.Chunk13224
import ArealUK.Chunk13225
import ArealUK.Chunk13226
import ArealUK.Chunk13227
import ArealUK.Chunk13228
import ArealUK.Chunk13229
import ArealUK.Chunk13230
import ArealUK.Chunk13231
import ArealUK.Chunk13232
import ArealUK.Chunk13233
import ArealUK.Chunk13234
import ArealUK.Chunk13235
import ArealUK.Chunk13236
import ArealUK.Chunk13237
import ArealUK.Chunk13238
import ArealUK.Chunk13239
import ArealUK.Chunk13240
import ArealUK.Chunk13241
import ArealUK.Chunk13242
import ArealUK.Chunk13243
import ArealUK.Chunk13244
import ArealUK.Chunk13245
import ArealUK.Chunk13246
import ArealUK.Chunk13247
import ArealUK.Chunk13248
import ArealUK.Chunk13249
import ArealUK.Chunk13250
import ArealUK.Chunk13251
import ArealUK.Chunk13252
import ArealUK.Chunk13253
import ArealUK.Chunk13254
import ArealUK.Chunk13255
import ArealUK.Chunk13256
import ArealUK.Chunk13257
import ArealUK.Chunk13258
import ArealUK.Chunk13259
import ArealUK.Chunk13260
import ArealUK.Chunk13261
import ArealUK.Chunk13262
import ArealUK.Chunk13263
import ArealUK.Chunk13264
import ArealUK.Chunk13265
import ArealUK.Chunk13266
import ArealUK.Chunk13267
import ArealUK.Chunk13268
import ArealUK.Chunk13269
import ArealUK.Chunk13270
import ArealUK.Chunk13271
import ArealUK.Chunk13272
import ArealUK.Chunk13273
import ArealUK.Chunk13274
import ArealUK.Chunk13275
import ArealUK.Chunk13276
import ArealUK.Chunk13277
import ArealUK.Chunk13278
import ArealUK.Chunk13279
import ArealUK.Chunk13280
import ArealUK.Chunk13281
import ArealUK.Chunk13282
import ArealUK.Chunk13283
import ArealUK.Chunk13284
import ArealUK.Chunk13285
import ArealUK.Chunk13286
import ArealUK.Chunk13287
import ArealUK.Chunk13288
import ArealUK.Chunk13289
import ArealUK.Chunk13290
import ArealUK.Chunk13291
import ArealUK.Chunk13292
import ArealUK.Chunk13293
import ArealUK.Chunk13294
import ArealUK.Chunk13295
import ArealUK.Chunk13296
import ArealUK.Chunk13297
import ArealUK.Chunk13298
import ArealUK.Chunk13299
import Areal.UCert.LeavesKGen

/-! Group 132 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_132 : leavesOK ctxLitU 134437500000 0 ((leaves.drop 26400).take 200) 542475000000 2 = true := by
  have s99 := ArealUCore.ArealUK.chunk_13299
  have s98 : leavesOK ctxLitU 542375000000 2 ((leaves.drop 26596).take 4) 542475000000 2 = true :=
    take_step (n := 2) (t := 4) (b := 26598) rfl rfl ArealUCore.ArealUK.chunk_13298 s99
  have s97 : leavesOK ctxLitU 542325000000 2 ((leaves.drop 26594).take 6) 542475000000 2 = true :=
    take_step (n := 2) (t := 6) (b := 26596) rfl rfl ArealUCore.ArealUK.chunk_13297 s98
  have s96 : leavesOK ctxLitU 271125000000 1 ((leaves.drop 26592).take 8) 542475000000 2 = true :=
    take_step (n := 2) (t := 8) (b := 26594) rfl rfl ArealUCore.ArealUK.chunk_13296 s97
  have s95 : leavesOK ctxLitU 542175000000 2 ((leaves.drop 26590).take 10) 542475000000 2 = true :=
    take_step (n := 2) (t := 10) (b := 26592) rfl rfl ArealUCore.ArealUK.chunk_13295 s96
  have s94 : leavesOK ctxLitU 542125000000 2 ((leaves.drop 26588).take 12) 542475000000 2 = true :=
    take_step (n := 2) (t := 12) (b := 26590) rfl rfl ArealUCore.ArealUK.chunk_13294 s95
  have s93 : leavesOK ctxLitU 542075000000 2 ((leaves.drop 26586).take 14) 542475000000 2 = true :=
    take_step (n := 2) (t := 14) (b := 26588) rfl rfl ArealUCore.ArealUK.chunk_13293 s94
  have s92 : leavesOK ctxLitU 542025000000 2 ((leaves.drop 26584).take 16) 542475000000 2 = true :=
    take_step (n := 2) (t := 16) (b := 26586) rfl rfl ArealUCore.ArealUK.chunk_13292 s93
  have s91 : leavesOK ctxLitU 270987500000 1 ((leaves.drop 26582).take 18) 542475000000 2 = true :=
    take_step (n := 2) (t := 18) (b := 26584) rfl rfl ArealUCore.ArealUK.chunk_13291 s92
  have s90 : leavesOK ctxLitU 541950000000 2 ((leaves.drop 26580).take 20) 542475000000 2 = true :=
    take_step (n := 2) (t := 20) (b := 26582) rfl rfl ArealUCore.ArealUK.chunk_13290 s91
  have s89 : leavesOK ctxLitU 541925000000 2 ((leaves.drop 26578).take 22) 542475000000 2 = true :=
    take_step (n := 2) (t := 22) (b := 26580) rfl rfl ArealUCore.ArealUK.chunk_13289 s90
  have s88 : leavesOK ctxLitU 135468750000 0 ((leaves.drop 26576).take 24) 542475000000 2 = true :=
    take_step (n := 2) (t := 24) (b := 26578) rfl rfl ArealUCore.ArealUK.chunk_13288 s89
  have s87 : leavesOK ctxLitU 135456250000 0 ((leaves.drop 26574).take 26) 542475000000 2 = true :=
    take_step (n := 2) (t := 26) (b := 26576) rfl rfl ArealUCore.ArealUK.chunk_13287 s88
  have s86 : leavesOK ctxLitU 135443750000 0 ((leaves.drop 26572).take 28) 542475000000 2 = true :=
    take_step (n := 2) (t := 28) (b := 26574) rfl rfl ArealUCore.ArealUK.chunk_13286 s87
  have s85 : leavesOK ctxLitU 270868750000 1 ((leaves.drop 26570).take 30) 542475000000 2 = true :=
    take_step (n := 2) (t := 30) (b := 26572) rfl rfl ArealUCore.ArealUK.chunk_13285 s86
  have s84 : leavesOK ctxLitU 270856250000 1 ((leaves.drop 26568).take 32) 542475000000 2 = true :=
    take_step (n := 2) (t := 32) (b := 26570) rfl rfl ArealUCore.ArealUK.chunk_13284 s85
  have s83 : leavesOK ctxLitU 270837500000 1 ((leaves.drop 26566).take 34) 542475000000 2 = true :=
    take_step (n := 2) (t := 34) (b := 26568) rfl rfl ArealUCore.ArealUK.chunk_13283 s84
  have s82 : leavesOK ctxLitU 270812500000 1 ((leaves.drop 26564).take 36) 542475000000 2 = true :=
    take_step (n := 2) (t := 36) (b := 26566) rfl rfl ArealUCore.ArealUK.chunk_13282 s83
  have s81 : leavesOK ctxLitU 270787500000 1 ((leaves.drop 26562).take 38) 542475000000 2 = true :=
    take_step (n := 2) (t := 38) (b := 26564) rfl rfl ArealUCore.ArealUK.chunk_13281 s82
  have s80 : leavesOK ctxLitU 270762500000 1 ((leaves.drop 26560).take 40) 542475000000 2 = true :=
    take_step (n := 2) (t := 40) (b := 26562) rfl rfl ArealUCore.ArealUK.chunk_13280 s81
  have s79 : leavesOK ctxLitU 270743750000 1 ((leaves.drop 26558).take 42) 542475000000 2 = true :=
    take_step (n := 2) (t := 42) (b := 26560) rfl rfl ArealUCore.ArealUK.chunk_13279 s80
  have s78 : leavesOK ctxLitU 135362500000 0 ((leaves.drop 26556).take 44) 542475000000 2 = true :=
    take_step (n := 2) (t := 44) (b := 26558) rfl rfl ArealUCore.ArealUK.chunk_13278 s79
  have s77 : leavesOK ctxLitU 135350000000 0 ((leaves.drop 26554).take 46) 542475000000 2 = true :=
    take_step (n := 2) (t := 46) (b := 26556) rfl rfl ArealUCore.ArealUK.chunk_13277 s78
  have s76 : leavesOK ctxLitU 270675000000 1 ((leaves.drop 26552).take 48) 542475000000 2 = true :=
    take_step (n := 2) (t := 48) (b := 26554) rfl rfl ArealUCore.ArealUK.chunk_13276 s77
  have s75 : leavesOK ctxLitU 270650000000 1 ((leaves.drop 26550).take 50) 542475000000 2 = true :=
    take_step (n := 2) (t := 50) (b := 26552) rfl rfl ArealUCore.ArealUK.chunk_13275 s76
  have s74 : leavesOK ctxLitU 541250000000 2 ((leaves.drop 26548).take 52) 542475000000 2 = true :=
    take_step (n := 2) (t := 52) (b := 26550) rfl rfl ArealUCore.ArealUK.chunk_13274 s75
  have s73 : leavesOK ctxLitU 541200000000 2 ((leaves.drop 26546).take 54) 542475000000 2 = true :=
    take_step (n := 2) (t := 54) (b := 26548) rfl rfl ArealUCore.ArealUK.chunk_13273 s74
  have s72 : leavesOK ctxLitU 541162500000 2 ((leaves.drop 26544).take 56) 542475000000 2 = true :=
    take_step (n := 2) (t := 56) (b := 26546) rfl rfl ArealUCore.ArealUK.chunk_13272 s73
  have s71 : leavesOK ctxLitU 270562500000 1 ((leaves.drop 26542).take 58) 542475000000 2 = true :=
    take_step (n := 2) (t := 58) (b := 26544) rfl rfl ArealUCore.ArealUK.chunk_13271 s72
  have s70 : leavesOK ctxLitU 135268750000 0 ((leaves.drop 26540).take 60) 542475000000 2 = true :=
    take_step (n := 2) (t := 60) (b := 26542) rfl rfl ArealUCore.ArealUK.chunk_13270 s71
  have s69 : leavesOK ctxLitU 135256250000 0 ((leaves.drop 26538).take 62) 542475000000 2 = true :=
    take_step (n := 2) (t := 62) (b := 26540) rfl rfl ArealUCore.ArealUK.chunk_13269 s70
  have s68 : leavesOK ctxLitU 135243750000 0 ((leaves.drop 26536).take 64) 542475000000 2 = true :=
    take_step (n := 2) (t := 64) (b := 26538) rfl rfl ArealUCore.ArealUK.chunk_13268 s69
  have s67 : leavesOK ctxLitU 270468750000 1 ((leaves.drop 26534).take 66) 542475000000 2 = true :=
    take_step (n := 2) (t := 66) (b := 26536) rfl rfl ArealUCore.ArealUK.chunk_13267 s68
  have s66 : leavesOK ctxLitU 270456250000 1 ((leaves.drop 26532).take 68) 542475000000 2 = true :=
    take_step (n := 2) (t := 68) (b := 26534) rfl rfl ArealUCore.ArealUK.chunk_13266 s67
  have s65 : leavesOK ctxLitU 270437500000 1 ((leaves.drop 26530).take 70) 542475000000 2 = true :=
    take_step (n := 2) (t := 70) (b := 26532) rfl rfl ArealUCore.ArealUK.chunk_13265 s66
  have s64 : leavesOK ctxLitU 270412500000 1 ((leaves.drop 26528).take 72) 542475000000 2 = true :=
    take_step (n := 2) (t := 72) (b := 26530) rfl rfl ArealUCore.ArealUK.chunk_13264 s65
  have s63 : leavesOK ctxLitU 270387500000 1 ((leaves.drop 26526).take 74) 542475000000 2 = true :=
    take_step (n := 2) (t := 74) (b := 26528) rfl rfl ArealUCore.ArealUK.chunk_13263 s64
  have s62 : leavesOK ctxLitU 270362500000 1 ((leaves.drop 26524).take 76) 542475000000 2 = true :=
    take_step (n := 2) (t := 76) (b := 26526) rfl rfl ArealUCore.ArealUK.chunk_13262 s63
  have s61 : leavesOK ctxLitU 135168750000 0 ((leaves.drop 26522).take 78) 542475000000 2 = true :=
    take_step (n := 2) (t := 78) (b := 26524) rfl rfl ArealUCore.ArealUK.chunk_13261 s62
  have s60 : leavesOK ctxLitU 135156250000 0 ((leaves.drop 26520).take 80) 542475000000 2 = true :=
    take_step (n := 2) (t := 80) (b := 26522) rfl rfl ArealUCore.ArealUK.chunk_13260 s61
  have s59 : leavesOK ctxLitU 135143750000 0 ((leaves.drop 26518).take 82) 542475000000 2 = true :=
    take_step (n := 2) (t := 82) (b := 26520) rfl rfl ArealUCore.ArealUK.chunk_13259 s60
  have s58 : leavesOK ctxLitU 135131250000 0 ((leaves.drop 26516).take 84) 542475000000 2 = true :=
    take_step (n := 2) (t := 84) (b := 26518) rfl rfl ArealUCore.ArealUK.chunk_13258 s59
  have s57 : leavesOK ctxLitU 270237500000 1 ((leaves.drop 26514).take 86) 542475000000 2 = true :=
    take_step (n := 2) (t := 86) (b := 26516) rfl rfl ArealUCore.ArealUK.chunk_13257 s58
  have s56 : leavesOK ctxLitU 270212500000 1 ((leaves.drop 26512).take 88) 542475000000 2 = true :=
    take_step (n := 2) (t := 88) (b := 26514) rfl rfl ArealUCore.ArealUK.chunk_13256 s57
  have s55 : leavesOK ctxLitU 270187500000 1 ((leaves.drop 26510).take 90) 542475000000 2 = true :=
    take_step (n := 2) (t := 90) (b := 26512) rfl rfl ArealUCore.ArealUK.chunk_13255 s56
  have s54 : leavesOK ctxLitU 270162500000 1 ((leaves.drop 26508).take 92) 542475000000 2 = true :=
    take_step (n := 2) (t := 92) (b := 26510) rfl rfl ArealUCore.ArealUK.chunk_13254 s55
  have s53 : leavesOK ctxLitU 135068750000 0 ((leaves.drop 26506).take 94) 542475000000 2 = true :=
    take_step (n := 2) (t := 94) (b := 26508) rfl rfl ArealUCore.ArealUK.chunk_13253 s54
  have s52 : leavesOK ctxLitU 135056250000 0 ((leaves.drop 26504).take 96) 542475000000 2 = true :=
    take_step (n := 2) (t := 96) (b := 26506) rfl rfl ArealUCore.ArealUK.chunk_13252 s53
  have s51 : leavesOK ctxLitU 135043750000 0 ((leaves.drop 26502).take 98) 542475000000 2 = true :=
    take_step (n := 2) (t := 98) (b := 26504) rfl rfl ArealUCore.ArealUK.chunk_13251 s52
  have s50 : leavesOK ctxLitU 270068750000 1 ((leaves.drop 26500).take 100) 542475000000 2 = true :=
    take_step (n := 2) (t := 100) (b := 26502) rfl rfl ArealUCore.ArealUK.chunk_13250 s51
  have s49 : leavesOK ctxLitU 270056250000 1 ((leaves.drop 26498).take 102) 542475000000 2 = true :=
    take_step (n := 2) (t := 102) (b := 26500) rfl rfl ArealUCore.ArealUK.chunk_13249 s50
  have s48 : leavesOK ctxLitU 270037500000 1 ((leaves.drop 26496).take 104) 542475000000 2 = true :=
    take_step (n := 2) (t := 104) (b := 26498) rfl rfl ArealUCore.ArealUK.chunk_13248 s49
  have s47 : leavesOK ctxLitU 270012500000 1 ((leaves.drop 26494).take 106) 542475000000 2 = true :=
    take_step (n := 2) (t := 106) (b := 26496) rfl rfl ArealUCore.ArealUK.chunk_13247 s48
  have s46 : leavesOK ctxLitU 539975000000 2 ((leaves.drop 26492).take 108) 542475000000 2 = true :=
    take_step (n := 2) (t := 108) (b := 26494) rfl rfl ArealUCore.ArealUK.chunk_13246 s47
  have s45 : leavesOK ctxLitU 539925000000 2 ((leaves.drop 26490).take 110) 542475000000 2 = true :=
    take_step (n := 2) (t := 110) (b := 26492) rfl rfl ArealUCore.ArealUK.chunk_13245 s46
  have s44 : leavesOK ctxLitU 539875000000 2 ((leaves.drop 26488).take 112) 542475000000 2 = true :=
    take_step (n := 2) (t := 112) (b := 26490) rfl rfl ArealUCore.ArealUK.chunk_13244 s45
  have s43 : leavesOK ctxLitU 539825000000 2 ((leaves.drop 26486).take 114) 542475000000 2 = true :=
    take_step (n := 2) (t := 114) (b := 26488) rfl rfl ArealUCore.ArealUK.chunk_13243 s44
  have s42 : leavesOK ctxLitU 539775000000 2 ((leaves.drop 26484).take 116) 542475000000 2 = true :=
    take_step (n := 2) (t := 116) (b := 26486) rfl rfl ArealUCore.ArealUK.chunk_13242 s43
  have s41 : leavesOK ctxLitU 539725000000 2 ((leaves.drop 26482).take 118) 542475000000 2 = true :=
    take_step (n := 2) (t := 118) (b := 26484) rfl rfl ArealUCore.ArealUK.chunk_13241 s42
  have s40 : leavesOK ctxLitU 539675000000 2 ((leaves.drop 26480).take 120) 542475000000 2 = true :=
    take_step (n := 2) (t := 120) (b := 26482) rfl rfl ArealUCore.ArealUK.chunk_13240 s41
  have s39 : leavesOK ctxLitU 539625000000 2 ((leaves.drop 26478).take 122) 542475000000 2 = true :=
    take_step (n := 2) (t := 122) (b := 26480) rfl rfl ArealUCore.ArealUK.chunk_13239 s40
  have s38 : leavesOK ctxLitU 269787500000 1 ((leaves.drop 26476).take 124) 542475000000 2 = true :=
    take_step (n := 2) (t := 124) (b := 26478) rfl rfl ArealUCore.ArealUK.chunk_13238 s39
  have s37 : leavesOK ctxLitU 539550000000 2 ((leaves.drop 26474).take 126) 542475000000 2 = true :=
    take_step (n := 2) (t := 126) (b := 26476) rfl rfl ArealUCore.ArealUK.chunk_13237 s38
  have s36 : leavesOK ctxLitU 269750000000 1 ((leaves.drop 26472).take 128) 542475000000 2 = true :=
    take_step (n := 2) (t := 128) (b := 26474) rfl rfl ArealUCore.ArealUK.chunk_13236 s37
  have s35 : leavesOK ctxLitU 134862500000 0 ((leaves.drop 26470).take 130) 542475000000 2 = true :=
    take_step (n := 2) (t := 130) (b := 26472) rfl rfl ArealUCore.ArealUK.chunk_13235 s36
  have s34 : leavesOK ctxLitU 134850000000 0 ((leaves.drop 26468).take 132) 542475000000 2 = true :=
    take_step (n := 2) (t := 132) (b := 26470) rfl rfl ArealUCore.ArealUK.chunk_13234 s35
  have s33 : leavesOK ctxLitU 134837500000 0 ((leaves.drop 26466).take 134) 542475000000 2 = true :=
    take_step (n := 2) (t := 134) (b := 26468) rfl rfl ArealUCore.ArealUK.chunk_13233 s34
  have s32 : leavesOK ctxLitU 134825000000 0 ((leaves.drop 26464).take 136) 542475000000 2 = true :=
    take_step (n := 2) (t := 136) (b := 26466) rfl rfl ArealUCore.ArealUK.chunk_13232 s33
  have s31 : leavesOK ctxLitU 269625000000 1 ((leaves.drop 26462).take 138) 542475000000 2 = true :=
    take_step (n := 2) (t := 138) (b := 26464) rfl rfl ArealUCore.ArealUK.chunk_13231 s32
  have s30 : leavesOK ctxLitU 269600000000 1 ((leaves.drop 26460).take 140) 542475000000 2 = true :=
    take_step (n := 2) (t := 140) (b := 26462) rfl rfl ArealUCore.ArealUK.chunk_13230 s31
  have s29 : leavesOK ctxLitU 269575000000 1 ((leaves.drop 26458).take 142) 542475000000 2 = true :=
    take_step (n := 2) (t := 142) (b := 26460) rfl rfl ArealUCore.ArealUK.chunk_13229 s30
  have s28 : leavesOK ctxLitU 269550000000 1 ((leaves.drop 26456).take 144) 542475000000 2 = true :=
    take_step (n := 2) (t := 144) (b := 26458) rfl rfl ArealUCore.ArealUK.chunk_13228 s29
  have s27 : leavesOK ctxLitU 269537500000 1 ((leaves.drop 26454).take 146) 542475000000 2 = true :=
    take_step (n := 2) (t := 146) (b := 26456) rfl rfl ArealUCore.ArealUK.chunk_13227 s28
  have s26 : leavesOK ctxLitU 269525000000 1 ((leaves.drop 26452).take 148) 542475000000 2 = true :=
    take_step (n := 2) (t := 148) (b := 26454) rfl rfl ArealUCore.ArealUK.chunk_13226 s27
  have s25 : leavesOK ctxLitU 134750000000 0 ((leaves.drop 26450).take 150) 542475000000 2 = true :=
    take_step (n := 2) (t := 150) (b := 26452) rfl rfl ArealUCore.ArealUK.chunk_13225 s26
  have s24 : leavesOK ctxLitU 134737500000 0 ((leaves.drop 26448).take 152) 542475000000 2 = true :=
    take_step (n := 2) (t := 152) (b := 26450) rfl rfl ArealUCore.ArealUK.chunk_13224 s25
  have s23 : leavesOK ctxLitU 134725000000 0 ((leaves.drop 26446).take 154) 542475000000 2 = true :=
    take_step (n := 2) (t := 154) (b := 26448) rfl rfl ArealUCore.ArealUK.chunk_13223 s24
  have s22 : leavesOK ctxLitU 269425000000 1 ((leaves.drop 26444).take 156) 542475000000 2 = true :=
    take_step (n := 2) (t := 156) (b := 26446) rfl rfl ArealUCore.ArealUK.chunk_13222 s23
  have s21 : leavesOK ctxLitU 269400000000 1 ((leaves.drop 26442).take 158) 542475000000 2 = true :=
    take_step (n := 2) (t := 158) (b := 26444) rfl rfl ArealUCore.ArealUK.chunk_13221 s22
  have s20 : leavesOK ctxLitU 538750000000 2 ((leaves.drop 26440).take 160) 542475000000 2 = true :=
    take_step (n := 2) (t := 160) (b := 26442) rfl rfl ArealUCore.ArealUK.chunk_13220 s21
  have s19 : leavesOK ctxLitU 538700000000 2 ((leaves.drop 26438).take 162) 542475000000 2 = true :=
    take_step (n := 2) (t := 162) (b := 26440) rfl rfl ArealUCore.ArealUK.chunk_13219 s20
  have s18 : leavesOK ctxLitU 269325000000 1 ((leaves.drop 26436).take 164) 542475000000 2 = true :=
    take_step (n := 2) (t := 164) (b := 26438) rfl rfl ArealUCore.ArealUK.chunk_13218 s19
  have s17 : leavesOK ctxLitU 269300000000 1 ((leaves.drop 26434).take 166) 542475000000 2 = true :=
    take_step (n := 2) (t := 166) (b := 26436) rfl rfl ArealUCore.ArealUK.chunk_13217 s18
  have s16 : leavesOK ctxLitU 134637500000 0 ((leaves.drop 26432).take 168) 542475000000 2 = true :=
    take_step (n := 2) (t := 168) (b := 26434) rfl rfl ArealUCore.ArealUK.chunk_13216 s17
  have s15 : leavesOK ctxLitU 134625000000 0 ((leaves.drop 26430).take 170) 542475000000 2 = true :=
    take_step (n := 2) (t := 170) (b := 26432) rfl rfl ArealUCore.ArealUK.chunk_13215 s16
  have s14 : leavesOK ctxLitU 269225000000 1 ((leaves.drop 26428).take 172) 542475000000 2 = true :=
    take_step (n := 2) (t := 172) (b := 26430) rfl rfl ArealUCore.ArealUK.chunk_13214 s15
  have s13 : leavesOK ctxLitU 269200000000 1 ((leaves.drop 26426).take 174) 542475000000 2 = true :=
    take_step (n := 2) (t := 174) (b := 26428) rfl rfl ArealUCore.ArealUK.chunk_13213 s14
  have s12 : leavesOK ctxLitU 269175000000 1 ((leaves.drop 26424).take 176) 542475000000 2 = true :=
    take_step (n := 2) (t := 176) (b := 26426) rfl rfl ArealUCore.ArealUK.chunk_13212 s13
  have s11 : leavesOK ctxLitU 269150000000 1 ((leaves.drop 26422).take 178) 542475000000 2 = true :=
    take_step (n := 2) (t := 178) (b := 26424) rfl rfl ArealUCore.ArealUK.chunk_13211 s12
  have s10 : leavesOK ctxLitU 134562500000 0 ((leaves.drop 26420).take 180) 542475000000 2 = true :=
    take_step (n := 2) (t := 180) (b := 26422) rfl rfl ArealUCore.ArealUK.chunk_13210 s11
  have s9 : leavesOK ctxLitU 134550000000 0 ((leaves.drop 26418).take 182) 542475000000 2 = true :=
    take_step (n := 2) (t := 182) (b := 26420) rfl rfl ArealUCore.ArealUK.chunk_13209 s10
  have s8 : leavesOK ctxLitU 134537500000 0 ((leaves.drop 26416).take 184) 542475000000 2 = true :=
    take_step (n := 2) (t := 184) (b := 26418) rfl rfl ArealUCore.ArealUK.chunk_13208 s9
  have s7 : leavesOK ctxLitU 134525000000 0 ((leaves.drop 26414).take 186) 542475000000 2 = true :=
    take_step (n := 2) (t := 186) (b := 26416) rfl rfl ArealUCore.ArealUK.chunk_13207 s8
  have s6 : leavesOK ctxLitU 269025000000 1 ((leaves.drop 26412).take 188) 542475000000 2 = true :=
    take_step (n := 2) (t := 188) (b := 26414) rfl rfl ArealUCore.ArealUK.chunk_13206 s7
  have s5 : leavesOK ctxLitU 269000000000 1 ((leaves.drop 26410).take 190) 542475000000 2 = true :=
    take_step (n := 2) (t := 190) (b := 26412) rfl rfl ArealUCore.ArealUK.chunk_13205 s6
  have s4 : leavesOK ctxLitU 268975000000 1 ((leaves.drop 26408).take 192) 542475000000 2 = true :=
    take_step (n := 2) (t := 192) (b := 26410) rfl rfl ArealUCore.ArealUK.chunk_13204 s5
  have s3 : leavesOK ctxLitU 268950000000 1 ((leaves.drop 26406).take 194) 542475000000 2 = true :=
    take_step (n := 2) (t := 194) (b := 26408) rfl rfl ArealUCore.ArealUK.chunk_13203 s4
  have s2 : leavesOK ctxLitU 134462500000 0 ((leaves.drop 26404).take 196) 542475000000 2 = true :=
    take_step (n := 2) (t := 196) (b := 26406) rfl rfl ArealUCore.ArealUK.chunk_13202 s3
  have s1 : leavesOK ctxLitU 134450000000 0 ((leaves.drop 26402).take 198) 542475000000 2 = true :=
    take_step (n := 2) (t := 198) (b := 26404) rfl rfl ArealUCore.ArealUK.chunk_13201 s2
  have s0 : leavesOK ctxLitU 134437500000 0 ((leaves.drop 26400).take 200) 542475000000 2 = true :=
    take_step (n := 2) (t := 200) (b := 26402) rfl rfl ArealUCore.ArealUK.chunk_13200 s1
  exact s0

end Areal.UCert

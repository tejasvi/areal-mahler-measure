import ArealUK.Chunk5200
import ArealUK.Chunk5201
import ArealUK.Chunk5202
import ArealUK.Chunk5203
import ArealUK.Chunk5204
import ArealUK.Chunk5205
import ArealUK.Chunk5206
import ArealUK.Chunk5207
import ArealUK.Chunk5208
import ArealUK.Chunk5209
import ArealUK.Chunk5210
import ArealUK.Chunk5211
import ArealUK.Chunk5212
import ArealUK.Chunk5213
import ArealUK.Chunk5214
import ArealUK.Chunk5215
import ArealUK.Chunk5216
import ArealUK.Chunk5217
import ArealUK.Chunk5218
import ArealUK.Chunk5219
import ArealUK.Chunk5220
import ArealUK.Chunk5221
import ArealUK.Chunk5222
import ArealUK.Chunk5223
import ArealUK.Chunk5224
import ArealUK.Chunk5225
import ArealUK.Chunk5226
import ArealUK.Chunk5227
import ArealUK.Chunk5228
import ArealUK.Chunk5229
import ArealUK.Chunk5230
import ArealUK.Chunk5231
import ArealUK.Chunk5232
import ArealUK.Chunk5233
import ArealUK.Chunk5234
import ArealUK.Chunk5235
import ArealUK.Chunk5236
import ArealUK.Chunk5237
import ArealUK.Chunk5238
import ArealUK.Chunk5239
import ArealUK.Chunk5240
import ArealUK.Chunk5241
import ArealUK.Chunk5242
import ArealUK.Chunk5243
import ArealUK.Chunk5244
import ArealUK.Chunk5245
import ArealUK.Chunk5246
import ArealUK.Chunk5247
import ArealUK.Chunk5248
import ArealUK.Chunk5249
import ArealUK.Chunk5250
import ArealUK.Chunk5251
import ArealUK.Chunk5252
import ArealUK.Chunk5253
import ArealUK.Chunk5254
import ArealUK.Chunk5255
import ArealUK.Chunk5256
import ArealUK.Chunk5257
import ArealUK.Chunk5258
import ArealUK.Chunk5259
import ArealUK.Chunk5260
import ArealUK.Chunk5261
import ArealUK.Chunk5262
import ArealUK.Chunk5263
import ArealUK.Chunk5264
import ArealUK.Chunk5265
import ArealUK.Chunk5266
import ArealUK.Chunk5267
import ArealUK.Chunk5268
import ArealUK.Chunk5269
import ArealUK.Chunk5270
import ArealUK.Chunk5271
import ArealUK.Chunk5272
import ArealUK.Chunk5273
import ArealUK.Chunk5274
import ArealUK.Chunk5275
import ArealUK.Chunk5276
import ArealUK.Chunk5277
import ArealUK.Chunk5278
import ArealUK.Chunk5279
import ArealUK.Chunk5280
import ArealUK.Chunk5281
import ArealUK.Chunk5282
import ArealUK.Chunk5283
import ArealUK.Chunk5284
import ArealUK.Chunk5285
import ArealUK.Chunk5286
import ArealUK.Chunk5287
import ArealUK.Chunk5288
import ArealUK.Chunk5289
import ArealUK.Chunk5290
import ArealUK.Chunk5291
import ArealUK.Chunk5292
import ArealUK.Chunk5293
import ArealUK.Chunk5294
import ArealUK.Chunk5295
import ArealUK.Chunk5296
import ArealUK.Chunk5297
import ArealUK.Chunk5298
import ArealUK.Chunk5299
import Areal.UCert.LeavesKGen

/-! Group 52 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_52 : leavesOK ctxLitU 138156250000 2 ((leaves.drop 10400).take 200) 279962500000 3 = true := by
  have s99 := ArealUCore.ArealUK.chunk_5299
  have s98 : leavesOK ctxLitU 139962500000 2 ((leaves.drop 10596).take 4) 279962500000 3 = true :=
    take_step (n := 2) (t := 4) (b := 10598) rfl rfl ArealUCore.ArealUK.chunk_5298 s99
  have s97 : leavesOK ctxLitU 34981250000 0 ((leaves.drop 10594).take 6) 279962500000 3 = true :=
    take_step (n := 2) (t := 6) (b := 10596) rfl rfl ArealUCore.ArealUK.chunk_5297 s98
  have s96 : leavesOK ctxLitU 34968750000 0 ((leaves.drop 10592).take 8) 279962500000 3 = true :=
    take_step (n := 2) (t := 8) (b := 10594) rfl rfl ArealUCore.ArealUK.chunk_5296 s97
  have s95 : leavesOK ctxLitU 34956250000 0 ((leaves.drop 10590).take 10) 279962500000 3 = true :=
    take_step (n := 2) (t := 10) (b := 10592) rfl rfl ArealUCore.ArealUK.chunk_5295 s96
  have s94 : leavesOK ctxLitU 143179820938634 12 ((leaves.drop 10588).take 12) 279962500000 3 = true :=
    take_step (n := 2) (t := 12) (b := 10590) rfl rfl ArealUCore.ArealUK.chunk_5294 s95
  have s93 : leavesOK ctxLitU 34943750000 0 ((leaves.drop 10586).take 14) 279962500000 3 = true :=
    take_step (n := 2) (t := 14) (b := 10588) rfl rfl ArealUCore.ArealUK.chunk_5293 s94
  have s92 : leavesOK ctxLitU 34931250000 0 ((leaves.drop 10584).take 16) 279962500000 3 = true :=
    take_step (n := 2) (t := 16) (b := 10586) rfl rfl ArealUCore.ArealUK.chunk_5292 s93
  have s91 : leavesOK ctxLitU 69843750000 1 ((leaves.drop 10582).take 18) 279962500000 3 = true :=
    take_step (n := 2) (t := 18) (b := 10584) rfl rfl ArealUCore.ArealUK.chunk_5291 s92
  have s90 : leavesOK ctxLitU 139675000000 2 ((leaves.drop 10580).take 20) 279962500000 3 = true :=
    take_step (n := 2) (t := 20) (b := 10582) rfl rfl ArealUCore.ArealUK.chunk_5290 s91
  have s89 : leavesOK ctxLitU 279337500000 3 ((leaves.drop 10578).take 22) 279962500000 3 = true :=
    take_step (n := 2) (t := 22) (b := 10580) rfl rfl ArealUCore.ArealUK.chunk_5289 s90
  have s88 : leavesOK ctxLitU 279325000000 3 ((leaves.drop 10576).take 24) 279962500000 3 = true :=
    take_step (n := 2) (t := 24) (b := 10578) rfl rfl ArealUCore.ArealUK.chunk_5288 s89
  have s87 : leavesOK ctxLitU 139650000000 2 ((leaves.drop 10574).take 26) 279962500000 3 = true :=
    take_step (n := 2) (t := 26) (b := 10576) rfl rfl ArealUCore.ArealUK.chunk_5287 s88
  have s86 : leavesOK ctxLitU 139631250000 2 ((leaves.drop 10572).take 28) 279962500000 3 = true :=
    take_step (n := 2) (t := 28) (b := 10574) rfl rfl ArealUCore.ArealUK.chunk_5286 s87
  have s85 : leavesOK ctxLitU 139618750000 2 ((leaves.drop 10570).take 30) 279962500000 3 = true :=
    take_step (n := 2) (t := 30) (b := 10572) rfl rfl ArealUCore.ArealUK.chunk_5285 s86
  have s84 : leavesOK ctxLitU 139606250000 2 ((leaves.drop 10568).take 32) 279962500000 3 = true :=
    take_step (n := 2) (t := 32) (b := 10570) rfl rfl ArealUCore.ArealUK.chunk_5284 s85
  have s83 : leavesOK ctxLitU 139593750000 2 ((leaves.drop 10566).take 34) 279962500000 3 = true :=
    take_step (n := 2) (t := 34) (b := 10568) rfl rfl ArealUCore.ArealUK.chunk_5283 s84
  have s82 : leavesOK ctxLitU 139581250000 2 ((leaves.drop 10564).take 36) 279962500000 3 = true :=
    take_step (n := 2) (t := 36) (b := 10566) rfl rfl ArealUCore.ArealUK.chunk_5282 s83
  have s81 : leavesOK ctxLitU 139568750000 2 ((leaves.drop 10562).take 38) 279962500000 3 = true :=
    take_step (n := 2) (t := 38) (b := 10564) rfl rfl ArealUCore.ArealUK.chunk_5281 s82
  have s80 : leavesOK ctxLitU 69775000000 1 ((leaves.drop 10560).take 40) 279962500000 3 = true :=
    take_step (n := 2) (t := 40) (b := 10562) rfl rfl ArealUCore.ArealUK.chunk_5280 s81
  have s79 : leavesOK ctxLitU 69762500000 1 ((leaves.drop 10558).take 42) 279962500000 3 = true :=
    take_step (n := 2) (t := 42) (b := 10560) rfl rfl ArealUCore.ArealUK.chunk_5279 s80
  have s78 : leavesOK ctxLitU 139506250000 2 ((leaves.drop 10556).take 44) 279962500000 3 = true :=
    take_step (n := 2) (t := 44) (b := 10558) rfl rfl ArealUCore.ArealUK.chunk_5278 s79
  have s77 : leavesOK ctxLitU 278987500000 3 ((leaves.drop 10554).take 46) 279962500000 3 = true :=
    take_step (n := 2) (t := 46) (b := 10556) rfl rfl ArealUCore.ArealUK.chunk_5277 s78
  have s76 : leavesOK ctxLitU 278962500000 3 ((leaves.drop 10552).take 48) 279962500000 3 = true :=
    take_step (n := 2) (t := 48) (b := 10554) rfl rfl ArealUCore.ArealUK.chunk_5276 s77
  have s75 : leavesOK ctxLitU 278937500000 3 ((leaves.drop 10550).take 50) 279962500000 3 = true :=
    take_step (n := 2) (t := 50) (b := 10552) rfl rfl ArealUCore.ArealUK.chunk_5275 s76
  have s74 : leavesOK ctxLitU 278912500000 3 ((leaves.drop 10548).take 52) 279962500000 3 = true :=
    take_step (n := 2) (t := 52) (b := 10550) rfl rfl ArealUCore.ArealUK.chunk_5274 s75
  have s73 : leavesOK ctxLitU 278887500000 3 ((leaves.drop 10546).take 54) 279962500000 3 = true :=
    take_step (n := 2) (t := 54) (b := 10548) rfl rfl ArealUCore.ArealUK.chunk_5273 s74
  have s72 : leavesOK ctxLitU 139425000000 2 ((leaves.drop 10544).take 56) 279962500000 3 = true :=
    take_step (n := 2) (t := 56) (b := 10546) rfl rfl ArealUCore.ArealUK.chunk_5272 s73
  have s71 : leavesOK ctxLitU 139400000000 2 ((leaves.drop 10542).take 58) 279962500000 3 = true :=
    take_step (n := 2) (t := 58) (b := 10544) rfl rfl ArealUCore.ArealUK.chunk_5271 s72
  have s70 : leavesOK ctxLitU 278750000000 3 ((leaves.drop 10540).take 60) 279962500000 3 = true :=
    take_step (n := 2) (t := 60) (b := 10542) rfl rfl ArealUCore.ArealUK.chunk_5270 s71
  have s69 : leavesOK ctxLitU 278700000000 3 ((leaves.drop 10538).take 62) 279962500000 3 = true :=
    take_step (n := 2) (t := 62) (b := 10540) rfl rfl ArealUCore.ArealUK.chunk_5269 s70
  have s68 : leavesOK ctxLitU 557350000000 4 ((leaves.drop 10536).take 64) 279962500000 3 = true :=
    take_step (n := 2) (t := 64) (b := 10538) rfl rfl ArealUCore.ArealUK.chunk_5268 s69
  have s67 : leavesOK ctxLitU 557300000000 4 ((leaves.drop 10534).take 66) 279962500000 3 = true :=
    take_step (n := 2) (t := 66) (b := 10536) rfl rfl ArealUCore.ArealUK.chunk_5267 s68
  have s66 : leavesOK ctxLitU 278600000000 3 ((leaves.drop 10532).take 68) 279962500000 3 = true :=
    take_step (n := 2) (t := 68) (b := 10534) rfl rfl ArealUCore.ArealUK.chunk_5266 s67
  have s65 : leavesOK ctxLitU 278550000000 3 ((leaves.drop 10530).take 70) 279962500000 3 = true :=
    take_step (n := 2) (t := 70) (b := 10532) rfl rfl ArealUCore.ArealUK.chunk_5265 s66
  have s64 : leavesOK ctxLitU 278500000000 3 ((leaves.drop 10528).take 72) 279962500000 3 = true :=
    take_step (n := 2) (t := 72) (b := 10530) rfl rfl ArealUCore.ArealUK.chunk_5264 s65
  have s63 : leavesOK ctxLitU 278450000000 3 ((leaves.drop 10526).take 74) 279962500000 3 = true :=
    take_step (n := 2) (t := 74) (b := 10528) rfl rfl ArealUCore.ArealUK.chunk_5263 s64
  have s62 : leavesOK ctxLitU 278400000000 3 ((leaves.drop 10524).take 76) 279962500000 3 = true :=
    take_step (n := 2) (t := 76) (b := 10526) rfl rfl ArealUCore.ArealUK.chunk_5262 s63
  have s61 : leavesOK ctxLitU 278350000000 3 ((leaves.drop 10522).take 78) 279962500000 3 = true :=
    take_step (n := 2) (t := 78) (b := 10524) rfl rfl ArealUCore.ArealUK.chunk_5261 s62
  have s60 : leavesOK ctxLitU 278300000000 3 ((leaves.drop 10520).take 80) 279962500000 3 = true :=
    take_step (n := 2) (t := 80) (b := 10522) rfl rfl ArealUCore.ArealUK.chunk_5260 s61
  have s59 : leavesOK ctxLitU 278250000000 3 ((leaves.drop 10518).take 82) 279962500000 3 = true :=
    take_step (n := 2) (t := 82) (b := 10520) rfl rfl ArealUCore.ArealUK.chunk_5259 s60
  have s58 : leavesOK ctxLitU 556425000000 4 ((leaves.drop 10516).take 84) 279962500000 3 = true :=
    take_step (n := 2) (t := 84) (b := 10518) rfl rfl ArealUCore.ArealUK.chunk_5258 s59
  have s57 : leavesOK ctxLitU 556375000000 4 ((leaves.drop 10514).take 86) 279962500000 3 = true :=
    take_step (n := 2) (t := 86) (b := 10516) rfl rfl ArealUCore.ArealUK.chunk_5257 s58
  have s56 : leavesOK ctxLitU 556325000000 4 ((leaves.drop 10512).take 88) 279962500000 3 = true :=
    take_step (n := 2) (t := 88) (b := 10514) rfl rfl ArealUCore.ArealUK.chunk_5256 s57
  have s55 : leavesOK ctxLitU 556275000000 4 ((leaves.drop 10510).take 90) 279962500000 3 = true :=
    take_step (n := 2) (t := 90) (b := 10512) rfl rfl ArealUCore.ArealUK.chunk_5255 s56
  have s54 : leavesOK ctxLitU 556225000000 4 ((leaves.drop 10508).take 92) 279962500000 3 = true :=
    take_step (n := 2) (t := 92) (b := 10510) rfl rfl ArealUCore.ArealUK.chunk_5254 s55
  have s53 : leavesOK ctxLitU 556175000000 4 ((leaves.drop 10506).take 94) 279962500000 3 = true :=
    take_step (n := 2) (t := 94) (b := 10508) rfl rfl ArealUCore.ArealUK.chunk_5253 s54
  have s52 : leavesOK ctxLitU 556125000000 4 ((leaves.drop 10504).take 96) 279962500000 3 = true :=
    take_step (n := 2) (t := 96) (b := 10506) rfl rfl ArealUCore.ArealUK.chunk_5252 s53
  have s51 : leavesOK ctxLitU 556075000000 4 ((leaves.drop 10502).take 98) 279962500000 3 = true :=
    take_step (n := 2) (t := 98) (b := 10504) rfl rfl ArealUCore.ArealUK.chunk_5251 s52
  have s50 : leavesOK ctxLitU 556025000000 4 ((leaves.drop 10500).take 100) 279962500000 3 = true :=
    take_step (n := 2) (t := 100) (b := 10502) rfl rfl ArealUCore.ArealUK.chunk_5250 s51
  have s49 : leavesOK ctxLitU 555975000000 4 ((leaves.drop 10498).take 102) 279962500000 3 = true :=
    take_step (n := 2) (t := 102) (b := 10500) rfl rfl ArealUCore.ArealUK.chunk_5249 s50
  have s48 : leavesOK ctxLitU 555925000000 4 ((leaves.drop 10496).take 104) 279962500000 3 = true :=
    take_step (n := 2) (t := 104) (b := 10498) rfl rfl ArealUCore.ArealUK.chunk_5248 s49
  have s47 : leavesOK ctxLitU 555875000000 4 ((leaves.drop 10494).take 106) 279962500000 3 = true :=
    take_step (n := 2) (t := 106) (b := 10496) rfl rfl ArealUCore.ArealUK.chunk_5247 s48
  have s46 : leavesOK ctxLitU 277900000000 3 ((leaves.drop 10492).take 108) 279962500000 3 = true :=
    take_step (n := 2) (t := 108) (b := 10494) rfl rfl ArealUCore.ArealUK.chunk_5246 s47
  have s45 : leavesOK ctxLitU 277850000000 3 ((leaves.drop 10490).take 110) 279962500000 3 = true :=
    take_step (n := 2) (t := 110) (b := 10492) rfl rfl ArealUCore.ArealUK.chunk_5245 s46
  have s44 : leavesOK ctxLitU 277800000000 3 ((leaves.drop 10488).take 112) 279962500000 3 = true :=
    take_step (n := 2) (t := 112) (b := 10490) rfl rfl ArealUCore.ArealUK.chunk_5244 s45
  have s43 : leavesOK ctxLitU 277750000000 3 ((leaves.drop 10486).take 114) 279962500000 3 = true :=
    take_step (n := 2) (t := 114) (b := 10488) rfl rfl ArealUCore.ArealUK.chunk_5243 s44
  have s42 : leavesOK ctxLitU 277700000000 3 ((leaves.drop 10484).take 116) 279962500000 3 = true :=
    take_step (n := 2) (t := 116) (b := 10486) rfl rfl ArealUCore.ArealUK.chunk_5242 s43
  have s41 : leavesOK ctxLitU 277650000000 3 ((leaves.drop 10482).take 118) 279962500000 3 = true :=
    take_step (n := 2) (t := 118) (b := 10484) rfl rfl ArealUCore.ArealUK.chunk_5241 s42
  have s40 : leavesOK ctxLitU 277600000000 3 ((leaves.drop 10480).take 120) 279962500000 3 = true :=
    take_step (n := 2) (t := 120) (b := 10482) rfl rfl ArealUCore.ArealUK.chunk_5240 s41
  have s39 : leavesOK ctxLitU 277550000000 3 ((leaves.drop 10478).take 122) 279962500000 3 = true :=
    take_step (n := 2) (t := 122) (b := 10480) rfl rfl ArealUCore.ArealUK.chunk_5239 s40
  have s38 : leavesOK ctxLitU 277500000000 3 ((leaves.drop 10476).take 124) 279962500000 3 = true :=
    take_step (n := 2) (t := 124) (b := 10478) rfl rfl ArealUCore.ArealUK.chunk_5238 s39
  have s37 : leavesOK ctxLitU 277450000000 3 ((leaves.drop 10474).take 126) 279962500000 3 = true :=
    take_step (n := 2) (t := 126) (b := 10476) rfl rfl ArealUCore.ArealUK.chunk_5237 s38
  have s36 : leavesOK ctxLitU 277400000000 3 ((leaves.drop 10472).take 128) 279962500000 3 = true :=
    take_step (n := 2) (t := 128) (b := 10474) rfl rfl ArealUCore.ArealUK.chunk_5236 s37
  have s35 : leavesOK ctxLitU 277350000000 3 ((leaves.drop 10470).take 130) 279962500000 3 = true :=
    take_step (n := 2) (t := 130) (b := 10472) rfl rfl ArealUCore.ArealUK.chunk_5235 s36
  have s34 : leavesOK ctxLitU 277300000000 3 ((leaves.drop 10468).take 132) 279962500000 3 = true :=
    take_step (n := 2) (t := 132) (b := 10470) rfl rfl ArealUCore.ArealUK.chunk_5234 s35
  have s33 : leavesOK ctxLitU 277250000000 3 ((leaves.drop 10466).take 134) 279962500000 3 = true :=
    take_step (n := 2) (t := 134) (b := 10468) rfl rfl ArealUCore.ArealUK.chunk_5233 s34
  have s32 : leavesOK ctxLitU 277200000000 3 ((leaves.drop 10464).take 136) 279962500000 3 = true :=
    take_step (n := 2) (t := 136) (b := 10466) rfl rfl ArealUCore.ArealUK.chunk_5232 s33
  have s31 : leavesOK ctxLitU 277150000000 3 ((leaves.drop 10462).take 138) 279962500000 3 = true :=
    take_step (n := 2) (t := 138) (b := 10464) rfl rfl ArealUCore.ArealUK.chunk_5231 s32
  have s30 : leavesOK ctxLitU 277100000000 3 ((leaves.drop 10460).take 140) 279962500000 3 = true :=
    take_step (n := 2) (t := 140) (b := 10462) rfl rfl ArealUCore.ArealUK.chunk_5230 s31
  have s29 : leavesOK ctxLitU 277050000000 3 ((leaves.drop 10458).take 142) 279962500000 3 = true :=
    take_step (n := 2) (t := 142) (b := 10460) rfl rfl ArealUCore.ArealUK.chunk_5229 s30
  have s28 : leavesOK ctxLitU 277000000000 3 ((leaves.drop 10456).take 144) 279962500000 3 = true :=
    take_step (n := 2) (t := 144) (b := 10458) rfl rfl ArealUCore.ArealUK.chunk_5228 s29
  have s27 : leavesOK ctxLitU 276950000000 3 ((leaves.drop 10454).take 146) 279962500000 3 = true :=
    take_step (n := 2) (t := 146) (b := 10456) rfl rfl ArealUCore.ArealUK.chunk_5227 s28
  have s26 : leavesOK ctxLitU 553825000000 4 ((leaves.drop 10452).take 148) 279962500000 3 = true :=
    take_step (n := 2) (t := 148) (b := 10454) rfl rfl ArealUCore.ArealUK.chunk_5226 s27
  have s25 : leavesOK ctxLitU 553775000000 4 ((leaves.drop 10450).take 150) 279962500000 3 = true :=
    take_step (n := 2) (t := 150) (b := 10452) rfl rfl ArealUCore.ArealUK.chunk_5225 s26
  have s24 : leavesOK ctxLitU 553725000000 4 ((leaves.drop 10448).take 152) 279962500000 3 = true :=
    take_step (n := 2) (t := 152) (b := 10450) rfl rfl ArealUCore.ArealUK.chunk_5224 s25
  have s23 : leavesOK ctxLitU 553675000000 4 ((leaves.drop 10446).take 154) 279962500000 3 = true :=
    take_step (n := 2) (t := 154) (b := 10448) rfl rfl ArealUCore.ArealUK.chunk_5223 s24
  have s22 : leavesOK ctxLitU 553625000000 4 ((leaves.drop 10444).take 156) 279962500000 3 = true :=
    take_step (n := 2) (t := 156) (b := 10446) rfl rfl ArealUCore.ArealUK.chunk_5222 s23
  have s21 : leavesOK ctxLitU 276787500000 3 ((leaves.drop 10442).take 158) 279962500000 3 = true :=
    take_step (n := 2) (t := 158) (b := 10444) rfl rfl ArealUCore.ArealUK.chunk_5221 s22
  have s20 : leavesOK ctxLitU 276762500000 3 ((leaves.drop 10440).take 160) 279962500000 3 = true :=
    take_step (n := 2) (t := 160) (b := 10442) rfl rfl ArealUCore.ArealUK.chunk_5220 s21
  have s19 : leavesOK ctxLitU 276737500000 3 ((leaves.drop 10438).take 162) 279962500000 3 = true :=
    take_step (n := 2) (t := 162) (b := 10440) rfl rfl ArealUCore.ArealUK.chunk_5219 s20
  have s18 : leavesOK ctxLitU 276712500000 3 ((leaves.drop 10436).take 164) 279962500000 3 = true :=
    take_step (n := 2) (t := 164) (b := 10438) rfl rfl ArealUCore.ArealUK.chunk_5218 s19
  have s17 : leavesOK ctxLitU 276687500000 3 ((leaves.drop 10434).take 166) 279962500000 3 = true :=
    take_step (n := 2) (t := 166) (b := 10436) rfl rfl ArealUCore.ArealUK.chunk_5217 s18
  have s16 : leavesOK ctxLitU 276662500000 3 ((leaves.drop 10432).take 168) 279962500000 3 = true :=
    take_step (n := 2) (t := 168) (b := 10434) rfl rfl ArealUCore.ArealUK.chunk_5216 s17
  have s15 : leavesOK ctxLitU 276637500000 3 ((leaves.drop 10430).take 170) 279962500000 3 = true :=
    take_step (n := 2) (t := 170) (b := 10432) rfl rfl ArealUCore.ArealUK.chunk_5215 s16
  have s14 : leavesOK ctxLitU 276612500000 3 ((leaves.drop 10428).take 172) 279962500000 3 = true :=
    take_step (n := 2) (t := 172) (b := 10430) rfl rfl ArealUCore.ArealUK.chunk_5214 s15
  have s13 : leavesOK ctxLitU 138293750000 2 ((leaves.drop 10426).take 174) 279962500000 3 = true :=
    take_step (n := 2) (t := 174) (b := 10428) rfl rfl ArealUCore.ArealUK.chunk_5213 s14
  have s12 : leavesOK ctxLitU 138281250000 2 ((leaves.drop 10424).take 176) 279962500000 3 = true :=
    take_step (n := 2) (t := 176) (b := 10426) rfl rfl ArealUCore.ArealUK.chunk_5212 s13
  have s11 : leavesOK ctxLitU 276550000000 3 ((leaves.drop 10422).take 178) 279962500000 3 = true :=
    take_step (n := 2) (t := 178) (b := 10424) rfl rfl ArealUCore.ArealUK.chunk_5211 s12
  have s10 : leavesOK ctxLitU 138262500000 2 ((leaves.drop 10420).take 180) 279962500000 3 = true :=
    take_step (n := 2) (t := 180) (b := 10422) rfl rfl ArealUCore.ArealUK.chunk_5210 s11
  have s9 : leavesOK ctxLitU 138243750000 2 ((leaves.drop 10418).take 182) 279962500000 3 = true :=
    take_step (n := 2) (t := 182) (b := 10420) rfl rfl ArealUCore.ArealUK.chunk_5209 s10
  have s8 : leavesOK ctxLitU 276468750000 3 ((leaves.drop 10416).take 184) 279962500000 3 = true :=
    take_step (n := 2) (t := 184) (b := 10418) rfl rfl ArealUCore.ArealUK.chunk_5208 s9
  have s7 : leavesOK ctxLitU 138225000000 2 ((leaves.drop 10414).take 186) 279962500000 3 = true :=
    take_step (n := 2) (t := 186) (b := 10416) rfl rfl ArealUCore.ArealUK.chunk_5207 s8
  have s6 : leavesOK ctxLitU 283047424746362 13 ((leaves.drop 10412).take 188) 279962500000 3 = true :=
    take_step (n := 2) (t := 188) (b := 10414) rfl rfl ArealUCore.ArealUK.chunk_5206 s7
  have s5 : leavesOK ctxLitU 141516800000000 12 ((leaves.drop 10410).take 190) 279962500000 3 = true :=
    take_step (n := 2) (t := 190) (b := 10412) rfl rfl ArealUCore.ArealUK.chunk_5205 s6
  have s4 : leavesOK ctxLitU 276387500000 3 ((leaves.drop 10408).take 192) 279962500000 3 = true :=
    take_step (n := 2) (t := 192) (b := 10410) rfl rfl ArealUCore.ArealUK.chunk_5204 s5
  have s3 : leavesOK ctxLitU 276375000000 3 ((leaves.drop 10406).take 194) 279962500000 3 = true :=
    take_step (n := 2) (t := 194) (b := 10408) rfl rfl ArealUCore.ArealUK.chunk_5203 s4
  have s2 : leavesOK ctxLitU 552737500000 4 ((leaves.drop 10404).take 196) 279962500000 3 = true :=
    take_step (n := 2) (t := 196) (b := 10406) rfl rfl ArealUCore.ArealUK.chunk_5202 s3
  have s1 : leavesOK ctxLitU 138175000000 2 ((leaves.drop 10402).take 198) 279962500000 3 = true :=
    take_step (n := 2) (t := 198) (b := 10404) rfl rfl ArealUCore.ArealUK.chunk_5201 s2
  have s0 : leavesOK ctxLitU 138156250000 2 ((leaves.drop 10400).take 200) 279962500000 3 = true :=
    take_step (n := 2) (t := 200) (b := 10402) rfl rfl ArealUCore.ArealUK.chunk_5200 s1
  exact s0

end Areal.UCert

import ArealUK.Chunk14200
import ArealUK.Chunk14201
import ArealUK.Chunk14202
import ArealUK.Chunk14203
import ArealUK.Chunk14204
import ArealUK.Chunk14205
import ArealUK.Chunk14206
import ArealUK.Chunk14207
import ArealUK.Chunk14208
import ArealUK.Chunk14209
import ArealUK.Chunk14210
import ArealUK.Chunk14211
import ArealUK.Chunk14212
import ArealUK.Chunk14213
import ArealUK.Chunk14214
import ArealUK.Chunk14215
import ArealUK.Chunk14216
import ArealUK.Chunk14217
import ArealUK.Chunk14218
import ArealUK.Chunk14219
import ArealUK.Chunk14220
import ArealUK.Chunk14221
import ArealUK.Chunk14222
import ArealUK.Chunk14223
import ArealUK.Chunk14224
import ArealUK.Chunk14225
import ArealUK.Chunk14226
import ArealUK.Chunk14227
import ArealUK.Chunk14228
import ArealUK.Chunk14229
import ArealUK.Chunk14230
import ArealUK.Chunk14231
import ArealUK.Chunk14232
import ArealUK.Chunk14233
import ArealUK.Chunk14234
import ArealUK.Chunk14235
import ArealUK.Chunk14236
import ArealUK.Chunk14237
import ArealUK.Chunk14238
import ArealUK.Chunk14239
import ArealUK.Chunk14240
import ArealUK.Chunk14241
import ArealUK.Chunk14242
import ArealUK.Chunk14243
import ArealUK.Chunk14244
import ArealUK.Chunk14245
import ArealUK.Chunk14246
import ArealUK.Chunk14247
import ArealUK.Chunk14248
import ArealUK.Chunk14249
import ArealUK.Chunk14250
import ArealUK.Chunk14251
import ArealUK.Chunk14252
import ArealUK.Chunk14253
import ArealUK.Chunk14254
import ArealUK.Chunk14255
import ArealUK.Chunk14256
import ArealUK.Chunk14257
import ArealUK.Chunk14258
import ArealUK.Chunk14259
import ArealUK.Chunk14260
import ArealUK.Chunk14261
import ArealUK.Chunk14262
import ArealUK.Chunk14263
import ArealUK.Chunk14264
import ArealUK.Chunk14265
import ArealUK.Chunk14266
import ArealUK.Chunk14267
import ArealUK.Chunk14268
import ArealUK.Chunk14269
import ArealUK.Chunk14270
import ArealUK.Chunk14271
import ArealUK.Chunk14272
import ArealUK.Chunk14273
import ArealUK.Chunk14274
import ArealUK.Chunk14275
import ArealUK.Chunk14276
import ArealUK.Chunk14277
import ArealUK.Chunk14278
import ArealUK.Chunk14279
import ArealUK.Chunk14280
import ArealUK.Chunk14281
import ArealUK.Chunk14282
import ArealUK.Chunk14283
import ArealUK.Chunk14284
import ArealUK.Chunk14285
import ArealUK.Chunk14286
import ArealUK.Chunk14287
import ArealUK.Chunk14288
import ArealUK.Chunk14289
import ArealUK.Chunk14290
import ArealUK.Chunk14291
import ArealUK.Chunk14292
import ArealUK.Chunk14293
import ArealUK.Chunk14294
import ArealUK.Chunk14295
import ArealUK.Chunk14296
import ArealUK.Chunk14297
import ArealUK.Chunk14298
import ArealUK.Chunk14299
import Areal.UCert.LeavesKGen

/-! Group 142 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_142 : leavesOK ctxLitU 584850000000 2 ((leaves.drop 28400).take 200) 294750000000 1 = true := by
  have s99 := ArealUCore.ArealUK.chunk_14299
  have s98 : leavesOK ctxLitU 294725000000 1 ((leaves.drop 28596).take 4) 294750000000 1 = true :=
    take_step (n := 2) (t := 4) (b := 28598) rfl rfl ArealUCore.ArealUK.chunk_14298 s99
  have s97 : leavesOK ctxLitU 147350000000 0 ((leaves.drop 28594).take 6) 294750000000 1 = true :=
    take_step (n := 2) (t := 6) (b := 28596) rfl rfl ArealUCore.ArealUK.chunk_14297 s98
  have s96 : leavesOK ctxLitU 294675000000 1 ((leaves.drop 28592).take 8) 294750000000 1 = true :=
    take_step (n := 2) (t := 8) (b := 28594) rfl rfl ArealUCore.ArealUK.chunk_14296 s97
  have s95 : leavesOK ctxLitU 294650000000 1 ((leaves.drop 28590).take 10) 294750000000 1 = true :=
    take_step (n := 2) (t := 10) (b := 28592) rfl rfl ArealUCore.ArealUK.chunk_14295 s96
  have s94 : leavesOK ctxLitU 589250000000 2 ((leaves.drop 28588).take 12) 294750000000 1 = true :=
    take_step (n := 2) (t := 12) (b := 28590) rfl rfl ArealUCore.ArealUK.chunk_14294 s95
  have s93 : leavesOK ctxLitU 589200000000 2 ((leaves.drop 28586).take 14) 294750000000 1 = true :=
    take_step (n := 2) (t := 14) (b := 28588) rfl rfl ArealUCore.ArealUK.chunk_14293 s94
  have s92 : leavesOK ctxLitU 294575000000 1 ((leaves.drop 28584).take 16) 294750000000 1 = true :=
    take_step (n := 2) (t := 16) (b := 28586) rfl rfl ArealUCore.ArealUK.chunk_14292 s93
  have s91 : leavesOK ctxLitU 294550000000 1 ((leaves.drop 28582).take 18) 294750000000 1 = true :=
    take_step (n := 2) (t := 18) (b := 28584) rfl rfl ArealUCore.ArealUK.chunk_14291 s92
  have s90 : leavesOK ctxLitU 147262500000 0 ((leaves.drop 28580).take 20) 294750000000 1 = true :=
    take_step (n := 2) (t := 20) (b := 28582) rfl rfl ArealUCore.ArealUK.chunk_14290 s91
  have s89 : leavesOK ctxLitU 147250000000 0 ((leaves.drop 28578).take 22) 294750000000 1 = true :=
    take_step (n := 2) (t := 22) (b := 28580) rfl rfl ArealUCore.ArealUK.chunk_14289 s90
  have s88 : leavesOK ctxLitU 147237500000 0 ((leaves.drop 28576).take 24) 294750000000 1 = true :=
    take_step (n := 2) (t := 24) (b := 28578) rfl rfl ArealUCore.ArealUK.chunk_14288 s89
  have s87 : leavesOK ctxLitU 294462500000 1 ((leaves.drop 28574).take 26) 294750000000 1 = true :=
    take_step (n := 2) (t := 26) (b := 28576) rfl rfl ArealUCore.ArealUK.chunk_14287 s88
  have s86 : leavesOK ctxLitU 294450000000 1 ((leaves.drop 28572).take 28) 294750000000 1 = true :=
    take_step (n := 2) (t := 28) (b := 28574) rfl rfl ArealUCore.ArealUK.chunk_14286 s87
  have s85 : leavesOK ctxLitU 294425000000 1 ((leaves.drop 28570).take 30) 294750000000 1 = true :=
    take_step (n := 2) (t := 30) (b := 28572) rfl rfl ArealUCore.ArealUK.chunk_14285 s86
  have s84 : leavesOK ctxLitU 294400000000 1 ((leaves.drop 28568).take 32) 294750000000 1 = true :=
    take_step (n := 2) (t := 32) (b := 28570) rfl rfl ArealUCore.ArealUK.chunk_14284 s85
  have s83 : leavesOK ctxLitU 294375000000 1 ((leaves.drop 28566).take 34) 294750000000 1 = true :=
    take_step (n := 2) (t := 34) (b := 28568) rfl rfl ArealUCore.ArealUK.chunk_14283 s84
  have s82 : leavesOK ctxLitU 294350000000 1 ((leaves.drop 28564).take 36) 294750000000 1 = true :=
    take_step (n := 2) (t := 36) (b := 28566) rfl rfl ArealUCore.ArealUK.chunk_14282 s83
  have s81 : leavesOK ctxLitU 294337500000 1 ((leaves.drop 28562).take 38) 294750000000 1 = true :=
    take_step (n := 2) (t := 38) (b := 28564) rfl rfl ArealUCore.ArealUK.chunk_14281 s82
  have s80 : leavesOK ctxLitU 294325000000 1 ((leaves.drop 28560).take 40) 294750000000 1 = true :=
    take_step (n := 2) (t := 40) (b := 28562) rfl rfl ArealUCore.ArealUK.chunk_14280 s81
  have s79 : leavesOK ctxLitU 147150000000 0 ((leaves.drop 28558).take 42) 294750000000 1 = true :=
    take_step (n := 2) (t := 42) (b := 28560) rfl rfl ArealUCore.ArealUK.chunk_14279 s80
  have s78 : leavesOK ctxLitU 147137500000 0 ((leaves.drop 28556).take 44) 294750000000 1 = true :=
    take_step (n := 2) (t := 44) (b := 28558) rfl rfl ArealUCore.ArealUK.chunk_14278 s79
  have s77 : leavesOK ctxLitU 147125000000 0 ((leaves.drop 28554).take 46) 294750000000 1 = true :=
    take_step (n := 2) (t := 46) (b := 28556) rfl rfl ArealUCore.ArealUK.chunk_14277 s78
  have s76 : leavesOK ctxLitU 294225000000 1 ((leaves.drop 28552).take 48) 294750000000 1 = true :=
    take_step (n := 2) (t := 48) (b := 28554) rfl rfl ArealUCore.ArealUK.chunk_14276 s77
  have s75 : leavesOK ctxLitU 294200000000 1 ((leaves.drop 28550).take 50) 294750000000 1 = true :=
    take_step (n := 2) (t := 50) (b := 28552) rfl rfl ArealUCore.ArealUK.chunk_14275 s76
  have s74 : leavesOK ctxLitU 588350000000 2 ((leaves.drop 28548).take 52) 294750000000 1 = true :=
    take_step (n := 2) (t := 52) (b := 28550) rfl rfl ArealUCore.ArealUK.chunk_14274 s75
  have s73 : leavesOK ctxLitU 588300000000 2 ((leaves.drop 28546).take 54) 294750000000 1 = true :=
    take_step (n := 2) (t := 54) (b := 28548) rfl rfl ArealUCore.ArealUK.chunk_14273 s74
  have s72 : leavesOK ctxLitU 294125000000 1 ((leaves.drop 28544).take 56) 294750000000 1 = true :=
    take_step (n := 2) (t := 56) (b := 28546) rfl rfl ArealUCore.ArealUK.chunk_14272 s73
  have s71 : leavesOK ctxLitU 294100000000 1 ((leaves.drop 28542).take 58) 294750000000 1 = true :=
    take_step (n := 2) (t := 58) (b := 28544) rfl rfl ArealUCore.ArealUK.chunk_14271 s72
  have s70 : leavesOK ctxLitU 147037500000 0 ((leaves.drop 28540).take 60) 294750000000 1 = true :=
    take_step (n := 2) (t := 60) (b := 28542) rfl rfl ArealUCore.ArealUK.chunk_14270 s71
  have s69 : leavesOK ctxLitU 147025000000 0 ((leaves.drop 28538).take 62) 294750000000 1 = true :=
    take_step (n := 2) (t := 62) (b := 28540) rfl rfl ArealUCore.ArealUK.chunk_14269 s70
  have s68 : leavesOK ctxLitU 294025000000 1 ((leaves.drop 28536).take 64) 294750000000 1 = true :=
    take_step (n := 2) (t := 64) (b := 28538) rfl rfl ArealUCore.ArealUK.chunk_14268 s69
  have s67 : leavesOK ctxLitU 294000000000 1 ((leaves.drop 28534).take 66) 294750000000 1 = true :=
    take_step (n := 2) (t := 66) (b := 28536) rfl rfl ArealUCore.ArealUK.chunk_14267 s68
  have s66 : leavesOK ctxLitU 293975000000 1 ((leaves.drop 28532).take 68) 294750000000 1 = true :=
    take_step (n := 2) (t := 68) (b := 28534) rfl rfl ArealUCore.ArealUK.chunk_14266 s67
  have s65 : leavesOK ctxLitU 293950000000 1 ((leaves.drop 28530).take 70) 294750000000 1 = true :=
    take_step (n := 2) (t := 70) (b := 28532) rfl rfl ArealUCore.ArealUK.chunk_14265 s66
  have s64 : leavesOK ctxLitU 146962500000 0 ((leaves.drop 28528).take 72) 294750000000 1 = true :=
    take_step (n := 2) (t := 72) (b := 28530) rfl rfl ArealUCore.ArealUK.chunk_14264 s65
  have s63 : leavesOK ctxLitU 146950000000 0 ((leaves.drop 28526).take 74) 294750000000 1 = true :=
    take_step (n := 2) (t := 74) (b := 28528) rfl rfl ArealUCore.ArealUK.chunk_14263 s64
  have s62 : leavesOK ctxLitU 293875000000 1 ((leaves.drop 28524).take 76) 294750000000 1 = true :=
    take_step (n := 2) (t := 76) (b := 28526) rfl rfl ArealUCore.ArealUK.chunk_14262 s63
  have s61 : leavesOK ctxLitU 293850000000 1 ((leaves.drop 28522).take 78) 294750000000 1 = true :=
    take_step (n := 2) (t := 78) (b := 28524) rfl rfl ArealUCore.ArealUK.chunk_14261 s62
  have s60 : leavesOK ctxLitU 587650000000 2 ((leaves.drop 28520).take 80) 294750000000 1 = true :=
    take_step (n := 2) (t := 80) (b := 28522) rfl rfl ArealUCore.ArealUK.chunk_14260 s61
  have s59 : leavesOK ctxLitU 587600000000 2 ((leaves.drop 28518).take 82) 294750000000 1 = true :=
    take_step (n := 2) (t := 82) (b := 28520) rfl rfl ArealUCore.ArealUK.chunk_14259 s60
  have s58 : leavesOK ctxLitU 587550000000 2 ((leaves.drop 28516).take 84) 294750000000 1 = true :=
    take_step (n := 2) (t := 84) (b := 28518) rfl rfl ArealUCore.ArealUK.chunk_14258 s59
  have s57 : leavesOK ctxLitU 587500000000 2 ((leaves.drop 28514).take 86) 294750000000 1 = true :=
    take_step (n := 2) (t := 86) (b := 28516) rfl rfl ArealUCore.ArealUK.chunk_14257 s58
  have s56 : leavesOK ctxLitU 293725000000 1 ((leaves.drop 28512).take 88) 294750000000 1 = true :=
    take_step (n := 2) (t := 88) (b := 28514) rfl rfl ArealUCore.ArealUK.chunk_14256 s57
  have s55 : leavesOK ctxLitU 293700000000 1 ((leaves.drop 28510).take 90) 294750000000 1 = true :=
    take_step (n := 2) (t := 90) (b := 28512) rfl rfl ArealUCore.ArealUK.chunk_14255 s56
  have s54 : leavesOK ctxLitU 146837500000 0 ((leaves.drop 28508).take 92) 294750000000 1 = true :=
    take_step (n := 2) (t := 92) (b := 28510) rfl rfl ArealUCore.ArealUK.chunk_14254 s55
  have s53 : leavesOK ctxLitU 293662500000 1 ((leaves.drop 28506).take 94) 294750000000 1 = true :=
    take_step (n := 2) (t := 94) (b := 28508) rfl rfl ArealUCore.ArealUK.chunk_14253 s54
  have s52 : leavesOK ctxLitU 293650000000 1 ((leaves.drop 28504).take 96) 294750000000 1 = true :=
    take_step (n := 2) (t := 96) (b := 28506) rfl rfl ArealUCore.ArealUK.chunk_14252 s53
  have s51 : leavesOK ctxLitU 293625000000 1 ((leaves.drop 28502).take 98) 294750000000 1 = true :=
    take_step (n := 2) (t := 98) (b := 28504) rfl rfl ArealUCore.ArealUK.chunk_14251 s52
  have s50 : leavesOK ctxLitU 293600000000 1 ((leaves.drop 28500).take 100) 294750000000 1 = true :=
    take_step (n := 2) (t := 100) (b := 28502) rfl rfl ArealUCore.ArealUK.chunk_14250 s51
  have s49 : leavesOK ctxLitU 293575000000 1 ((leaves.drop 28498).take 102) 294750000000 1 = true :=
    take_step (n := 2) (t := 102) (b := 28500) rfl rfl ArealUCore.ArealUK.chunk_14249 s50
  have s48 : leavesOK ctxLitU 293550000000 1 ((leaves.drop 28496).take 104) 294750000000 1 = true :=
    take_step (n := 2) (t := 104) (b := 28498) rfl rfl ArealUCore.ArealUK.chunk_14248 s49
  have s47 : leavesOK ctxLitU 293537500000 1 ((leaves.drop 28494).take 106) 294750000000 1 = true :=
    take_step (n := 2) (t := 106) (b := 28496) rfl rfl ArealUCore.ArealUK.chunk_14247 s48
  have s46 : leavesOK ctxLitU 293525000000 1 ((leaves.drop 28492).take 108) 294750000000 1 = true :=
    take_step (n := 2) (t := 108) (b := 28494) rfl rfl ArealUCore.ArealUK.chunk_14246 s47
  have s45 : leavesOK ctxLitU 146750000000 0 ((leaves.drop 28490).take 110) 294750000000 1 = true :=
    take_step (n := 2) (t := 110) (b := 28492) rfl rfl ArealUCore.ArealUK.chunk_14245 s46
  have s44 : leavesOK ctxLitU 146737500000 0 ((leaves.drop 28488).take 112) 294750000000 1 = true :=
    take_step (n := 2) (t := 112) (b := 28490) rfl rfl ArealUCore.ArealUK.chunk_14244 s45
  have s43 : leavesOK ctxLitU 146725000000 0 ((leaves.drop 28486).take 114) 294750000000 1 = true :=
    take_step (n := 2) (t := 114) (b := 28488) rfl rfl ArealUCore.ArealUK.chunk_14243 s44
  have s42 : leavesOK ctxLitU 293425000000 1 ((leaves.drop 28484).take 116) 294750000000 1 = true :=
    take_step (n := 2) (t := 116) (b := 28486) rfl rfl ArealUCore.ArealUK.chunk_14242 s43
  have s41 : leavesOK ctxLitU 293400000000 1 ((leaves.drop 28482).take 118) 294750000000 1 = true :=
    take_step (n := 2) (t := 118) (b := 28484) rfl rfl ArealUCore.ArealUK.chunk_14241 s42
  have s40 : leavesOK ctxLitU 586750000000 2 ((leaves.drop 28480).take 120) 294750000000 1 = true :=
    take_step (n := 2) (t := 120) (b := 28482) rfl rfl ArealUCore.ArealUK.chunk_14240 s41
  have s39 : leavesOK ctxLitU 586700000000 2 ((leaves.drop 28478).take 122) 294750000000 1 = true :=
    take_step (n := 2) (t := 122) (b := 28480) rfl rfl ArealUCore.ArealUK.chunk_14239 s40
  have s38 : leavesOK ctxLitU 586650000000 2 ((leaves.drop 28476).take 124) 294750000000 1 = true :=
    take_step (n := 2) (t := 124) (b := 28478) rfl rfl ArealUCore.ArealUK.chunk_14238 s39
  have s37 : leavesOK ctxLitU 586575000000 2 ((leaves.drop 28474).take 126) 294750000000 1 = true :=
    take_step (n := 2) (t := 126) (b := 28476) rfl rfl ArealUCore.ArealUK.chunk_14237 s38
  have s36 : leavesOK ctxLitU 586525000000 2 ((leaves.drop 28472).take 128) 294750000000 1 = true :=
    take_step (n := 2) (t := 128) (b := 28474) rfl rfl ArealUCore.ArealUK.chunk_14236 s37
  have s35 : leavesOK ctxLitU 586475000000 2 ((leaves.drop 28470).take 130) 294750000000 1 = true :=
    take_step (n := 2) (t := 130) (b := 28472) rfl rfl ArealUCore.ArealUK.chunk_14235 s36
  have s34 : leavesOK ctxLitU 586425000000 2 ((leaves.drop 28468).take 132) 294750000000 1 = true :=
    take_step (n := 2) (t := 132) (b := 28470) rfl rfl ArealUCore.ArealUK.chunk_14234 s35
  have s33 : leavesOK ctxLitU 293187500000 1 ((leaves.drop 28466).take 134) 294750000000 1 = true :=
    take_step (n := 2) (t := 134) (b := 28468) rfl rfl ArealUCore.ArealUK.chunk_14233 s34
  have s32 : leavesOK ctxLitU 293162500000 1 ((leaves.drop 28464).take 136) 294750000000 1 = true :=
    take_step (n := 2) (t := 136) (b := 28466) rfl rfl ArealUCore.ArealUK.chunk_14232 s33
  have s31 : leavesOK ctxLitU 293143750000 1 ((leaves.drop 28462).take 138) 294750000000 1 = true :=
    take_step (n := 2) (t := 138) (b := 28464) rfl rfl ArealUCore.ArealUK.chunk_14231 s32
  have s30 : leavesOK ctxLitU 293131250000 1 ((leaves.drop 28460).take 140) 294750000000 1 = true :=
    take_step (n := 2) (t := 140) (b := 28462) rfl rfl ArealUCore.ArealUK.chunk_14230 s31
  have s29 : leavesOK ctxLitU 146556250000 0 ((leaves.drop 28458).take 142) 294750000000 1 = true :=
    take_step (n := 2) (t := 142) (b := 28460) rfl rfl ArealUCore.ArealUK.chunk_14229 s30
  have s28 : leavesOK ctxLitU 146543750000 0 ((leaves.drop 28456).take 144) 294750000000 1 = true :=
    take_step (n := 2) (t := 144) (b := 28458) rfl rfl ArealUCore.ArealUK.chunk_14228 s29
  have s27 : leavesOK ctxLitU 146531250000 0 ((leaves.drop 28454).take 146) 294750000000 1 = true :=
    take_step (n := 2) (t := 146) (b := 28456) rfl rfl ArealUCore.ArealUK.chunk_14227 s28
  have s26 : leavesOK ctxLitU 293037500000 1 ((leaves.drop 28452).take 148) 294750000000 1 = true :=
    take_step (n := 2) (t := 148) (b := 28454) rfl rfl ArealUCore.ArealUK.chunk_14226 s27
  have s25 : leavesOK ctxLitU 293012500000 1 ((leaves.drop 28450).take 150) 294750000000 1 = true :=
    take_step (n := 2) (t := 150) (b := 28452) rfl rfl ArealUCore.ArealUK.chunk_14225 s26
  have s24 : leavesOK ctxLitU 292987500000 1 ((leaves.drop 28448).take 152) 294750000000 1 = true :=
    take_step (n := 2) (t := 152) (b := 28450) rfl rfl ArealUCore.ArealUK.chunk_14224 s25
  have s23 : leavesOK ctxLitU 292962500000 1 ((leaves.drop 28446).take 154) 294750000000 1 = true :=
    take_step (n := 2) (t := 154) (b := 28448) rfl rfl ArealUCore.ArealUK.chunk_14223 s24
  have s22 : leavesOK ctxLitU 146468750000 0 ((leaves.drop 28444).take 156) 294750000000 1 = true :=
    take_step (n := 2) (t := 156) (b := 28446) rfl rfl ArealUCore.ArealUK.chunk_14222 s23
  have s21 : leavesOK ctxLitU 146456250000 0 ((leaves.drop 28442).take 158) 294750000000 1 = true :=
    take_step (n := 2) (t := 158) (b := 28444) rfl rfl ArealUCore.ArealUK.chunk_14221 s22
  have s20 : leavesOK ctxLitU 146443750000 0 ((leaves.drop 28440).take 160) 294750000000 1 = true :=
    take_step (n := 2) (t := 160) (b := 28442) rfl rfl ArealUCore.ArealUK.chunk_14220 s21
  have s19 : leavesOK ctxLitU 146431250000 0 ((leaves.drop 28438).take 162) 294750000000 1 = true :=
    take_step (n := 2) (t := 162) (b := 28440) rfl rfl ArealUCore.ArealUK.chunk_14219 s20
  have s18 : leavesOK ctxLitU 292850000000 1 ((leaves.drop 28436).take 164) 294750000000 1 = true :=
    take_step (n := 2) (t := 164) (b := 28438) rfl rfl ArealUCore.ArealUK.chunk_14218 s19
  have s17 : leavesOK ctxLitU 292825000000 1 ((leaves.drop 28434).take 166) 294750000000 1 = true :=
    take_step (n := 2) (t := 166) (b := 28436) rfl rfl ArealUCore.ArealUK.chunk_14217 s18
  have s16 : leavesOK ctxLitU 292800000000 1 ((leaves.drop 28432).take 168) 294750000000 1 = true :=
    take_step (n := 2) (t := 168) (b := 28434) rfl rfl ArealUCore.ArealUK.chunk_14216 s17
  have s15 : leavesOK ctxLitU 292775000000 1 ((leaves.drop 28430).take 170) 294750000000 1 = true :=
    take_step (n := 2) (t := 170) (b := 28432) rfl rfl ArealUCore.ArealUK.chunk_14215 s16
  have s14 : leavesOK ctxLitU 292750000000 1 ((leaves.drop 28428).take 172) 294750000000 1 = true :=
    take_step (n := 2) (t := 172) (b := 28430) rfl rfl ArealUCore.ArealUK.chunk_14214 s15
  have s13 : leavesOK ctxLitU 292737500000 1 ((leaves.drop 28426).take 174) 294750000000 1 = true :=
    take_step (n := 2) (t := 174) (b := 28428) rfl rfl ArealUCore.ArealUK.chunk_14213 s14
  have s12 : leavesOK ctxLitU 292725000000 1 ((leaves.drop 28424).take 176) 294750000000 1 = true :=
    take_step (n := 2) (t := 176) (b := 28426) rfl rfl ArealUCore.ArealUK.chunk_14212 s13
  have s11 : leavesOK ctxLitU 146350000000 0 ((leaves.drop 28422).take 178) 294750000000 1 = true :=
    take_step (n := 2) (t := 178) (b := 28424) rfl rfl ArealUCore.ArealUK.chunk_14211 s12
  have s10 : leavesOK ctxLitU 146337500000 0 ((leaves.drop 28420).take 180) 294750000000 1 = true :=
    take_step (n := 2) (t := 180) (b := 28422) rfl rfl ArealUCore.ArealUK.chunk_14210 s11
  have s9 : leavesOK ctxLitU 146325000000 0 ((leaves.drop 28418).take 182) 294750000000 1 = true :=
    take_step (n := 2) (t := 182) (b := 28420) rfl rfl ArealUCore.ArealUK.chunk_14209 s10
  have s8 : leavesOK ctxLitU 292625000000 1 ((leaves.drop 28416).take 184) 294750000000 1 = true :=
    take_step (n := 2) (t := 184) (b := 28418) rfl rfl ArealUCore.ArealUK.chunk_14208 s9
  have s7 : leavesOK ctxLitU 292600000000 1 ((leaves.drop 28414).take 186) 294750000000 1 = true :=
    take_step (n := 2) (t := 186) (b := 28416) rfl rfl ArealUCore.ArealUK.chunk_14207 s8
  have s6 : leavesOK ctxLitU 585150000000 2 ((leaves.drop 28412).take 188) 294750000000 1 = true :=
    take_step (n := 2) (t := 188) (b := 28414) rfl rfl ArealUCore.ArealUK.chunk_14206 s7
  have s5 : leavesOK ctxLitU 585100000000 2 ((leaves.drop 28410).take 190) 294750000000 1 = true :=
    take_step (n := 2) (t := 190) (b := 28412) rfl rfl ArealUCore.ArealUK.chunk_14205 s6
  have s4 : leavesOK ctxLitU 585050000000 2 ((leaves.drop 28408).take 192) 294750000000 1 = true :=
    take_step (n := 2) (t := 192) (b := 28410) rfl rfl ArealUCore.ArealUK.chunk_14204 s5
  have s3 : leavesOK ctxLitU 585000000000 2 ((leaves.drop 28406).take 194) 294750000000 1 = true :=
    take_step (n := 2) (t := 194) (b := 28408) rfl rfl ArealUCore.ArealUK.chunk_14203 s4
  have s2 : leavesOK ctxLitU 584950000000 2 ((leaves.drop 28404).take 196) 294750000000 1 = true :=
    take_step (n := 2) (t := 196) (b := 28406) rfl rfl ArealUCore.ArealUK.chunk_14202 s3
  have s1 : leavesOK ctxLitU 584900000000 2 ((leaves.drop 28402).take 198) 294750000000 1 = true :=
    take_step (n := 2) (t := 198) (b := 28404) rfl rfl ArealUCore.ArealUK.chunk_14201 s2
  have s0 : leavesOK ctxLitU 584850000000 2 ((leaves.drop 28400).take 200) 294750000000 1 = true :=
    take_step (n := 2) (t := 200) (b := 28402) rfl rfl ArealUCore.ArealUK.chunk_14200 s1
  exact s0

end Areal.UCert

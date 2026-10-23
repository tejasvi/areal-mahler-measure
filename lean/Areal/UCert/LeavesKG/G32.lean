import ArealUK.Chunk3200
import ArealUK.Chunk3201
import ArealUK.Chunk3202
import ArealUK.Chunk3203
import ArealUK.Chunk3204
import ArealUK.Chunk3205
import ArealUK.Chunk3206
import ArealUK.Chunk3207
import ArealUK.Chunk3208
import ArealUK.Chunk3209
import ArealUK.Chunk3210
import ArealUK.Chunk3211
import ArealUK.Chunk3212
import ArealUK.Chunk3213
import ArealUK.Chunk3214
import ArealUK.Chunk3215
import ArealUK.Chunk3216
import ArealUK.Chunk3217
import ArealUK.Chunk3218
import ArealUK.Chunk3219
import ArealUK.Chunk3220
import ArealUK.Chunk3221
import ArealUK.Chunk3222
import ArealUK.Chunk3223
import ArealUK.Chunk3224
import ArealUK.Chunk3225
import ArealUK.Chunk3226
import ArealUK.Chunk3227
import ArealUK.Chunk3228
import ArealUK.Chunk3229
import ArealUK.Chunk3230
import ArealUK.Chunk3231
import ArealUK.Chunk3232
import ArealUK.Chunk3233
import ArealUK.Chunk3234
import ArealUK.Chunk3235
import ArealUK.Chunk3236
import ArealUK.Chunk3237
import ArealUK.Chunk3238
import ArealUK.Chunk3239
import ArealUK.Chunk3240
import ArealUK.Chunk3241
import ArealUK.Chunk3242
import ArealUK.Chunk3243
import ArealUK.Chunk3244
import ArealUK.Chunk3245
import ArealUK.Chunk3246
import ArealUK.Chunk3247
import ArealUK.Chunk3248
import ArealUK.Chunk3249
import ArealUK.Chunk3250
import ArealUK.Chunk3251
import ArealUK.Chunk3252
import ArealUK.Chunk3253
import ArealUK.Chunk3254
import ArealUK.Chunk3255
import ArealUK.Chunk3256
import ArealUK.Chunk3257
import ArealUK.Chunk3258
import ArealUK.Chunk3259
import ArealUK.Chunk3260
import ArealUK.Chunk3261
import ArealUK.Chunk3262
import ArealUK.Chunk3263
import ArealUK.Chunk3264
import ArealUK.Chunk3265
import ArealUK.Chunk3266
import ArealUK.Chunk3267
import ArealUK.Chunk3268
import ArealUK.Chunk3269
import ArealUK.Chunk3270
import ArealUK.Chunk3271
import ArealUK.Chunk3272
import ArealUK.Chunk3273
import ArealUK.Chunk3274
import ArealUK.Chunk3275
import ArealUK.Chunk3276
import ArealUK.Chunk3277
import ArealUK.Chunk3278
import ArealUK.Chunk3279
import ArealUK.Chunk3280
import ArealUK.Chunk3281
import ArealUK.Chunk3282
import ArealUK.Chunk3283
import ArealUK.Chunk3284
import ArealUK.Chunk3285
import ArealUK.Chunk3286
import ArealUK.Chunk3287
import ArealUK.Chunk3288
import ArealUK.Chunk3289
import ArealUK.Chunk3290
import ArealUK.Chunk3291
import ArealUK.Chunk3292
import ArealUK.Chunk3293
import ArealUK.Chunk3294
import ArealUK.Chunk3295
import ArealUK.Chunk3296
import ArealUK.Chunk3297
import ArealUK.Chunk3298
import ArealUK.Chunk3299
import Areal.UCert.LeavesKGen

/-! Group 32 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_32 : leavesOK ctxLitU 300250000000 4 ((leaves.drop 6400).take 200) 306325000000 4 = true := by
  have s99 := ArealUCore.ArealUK.chunk_3299
  have s98 : leavesOK ctxLitU 306225000000 4 ((leaves.drop 6596).take 4) 306325000000 4 = true :=
    take_step (n := 2) (t := 4) (b := 6598) rfl rfl ArealUCore.ArealUK.chunk_3298 s99
  have s97 : leavesOK ctxLitU 306175000000 4 ((leaves.drop 6594).take 6) 306325000000 4 = true :=
    take_step (n := 2) (t := 6) (b := 6596) rfl rfl ArealUCore.ArealUK.chunk_3297 s98
  have s96 : leavesOK ctxLitU 306125000000 4 ((leaves.drop 6592).take 8) 306325000000 4 = true :=
    take_step (n := 2) (t := 8) (b := 6594) rfl rfl ArealUCore.ArealUK.chunk_3296 s97
  have s95 : leavesOK ctxLitU 306075000000 4 ((leaves.drop 6590).take 10) 306325000000 4 = true :=
    take_step (n := 2) (t := 10) (b := 6592) rfl rfl ArealUCore.ArealUK.chunk_3295 s96
  have s94 : leavesOK ctxLitU 306025000000 4 ((leaves.drop 6588).take 12) 306325000000 4 = true :=
    take_step (n := 2) (t := 12) (b := 6590) rfl rfl ArealUCore.ArealUK.chunk_3294 s95
  have s93 : leavesOK ctxLitU 305975000000 4 ((leaves.drop 6586).take 14) 306325000000 4 = true :=
    take_step (n := 2) (t := 14) (b := 6588) rfl rfl ArealUCore.ArealUK.chunk_3293 s94
  have s92 : leavesOK ctxLitU 305925000000 4 ((leaves.drop 6584).take 16) 306325000000 4 = true :=
    take_step (n := 2) (t := 16) (b := 6586) rfl rfl ArealUCore.ArealUK.chunk_3292 s93
  have s91 : leavesOK ctxLitU 305875000000 4 ((leaves.drop 6582).take 18) 306325000000 4 = true :=
    take_step (n := 2) (t := 18) (b := 6584) rfl rfl ArealUCore.ArealUK.chunk_3291 s92
  have s90 : leavesOK ctxLitU 305825000000 4 ((leaves.drop 6580).take 20) 306325000000 4 = true :=
    take_step (n := 2) (t := 20) (b := 6582) rfl rfl ArealUCore.ArealUK.chunk_3290 s91
  have s89 : leavesOK ctxLitU 305775000000 4 ((leaves.drop 6578).take 22) 306325000000 4 = true :=
    take_step (n := 2) (t := 22) (b := 6580) rfl rfl ArealUCore.ArealUK.chunk_3289 s90
  have s88 : leavesOK ctxLitU 305725000000 4 ((leaves.drop 6576).take 24) 306325000000 4 = true :=
    take_step (n := 2) (t := 24) (b := 6578) rfl rfl ArealUCore.ArealUK.chunk_3288 s89
  have s87 : leavesOK ctxLitU 305675000000 4 ((leaves.drop 6574).take 26) 306325000000 4 = true :=
    take_step (n := 2) (t := 26) (b := 6576) rfl rfl ArealUCore.ArealUK.chunk_3287 s88
  have s86 : leavesOK ctxLitU 305625000000 4 ((leaves.drop 6572).take 28) 306325000000 4 = true :=
    take_step (n := 2) (t := 28) (b := 6574) rfl rfl ArealUCore.ArealUK.chunk_3286 s87
  have s85 : leavesOK ctxLitU 305575000000 4 ((leaves.drop 6570).take 30) 306325000000 4 = true :=
    take_step (n := 2) (t := 30) (b := 6572) rfl rfl ArealUCore.ArealUK.chunk_3285 s86
  have s84 : leavesOK ctxLitU 305525000000 4 ((leaves.drop 6568).take 32) 306325000000 4 = true :=
    take_step (n := 2) (t := 32) (b := 6570) rfl rfl ArealUCore.ArealUK.chunk_3284 s85
  have s83 : leavesOK ctxLitU 305475000000 4 ((leaves.drop 6566).take 34) 306325000000 4 = true :=
    take_step (n := 2) (t := 34) (b := 6568) rfl rfl ArealUCore.ArealUK.chunk_3283 s84
  have s82 : leavesOK ctxLitU 305425000000 4 ((leaves.drop 6564).take 36) 306325000000 4 = true :=
    take_step (n := 2) (t := 36) (b := 6566) rfl rfl ArealUCore.ArealUK.chunk_3282 s83
  have s81 : leavesOK ctxLitU 305375000000 4 ((leaves.drop 6562).take 38) 306325000000 4 = true :=
    take_step (n := 2) (t := 38) (b := 6564) rfl rfl ArealUCore.ArealUK.chunk_3281 s82
  have s80 : leavesOK ctxLitU 305325000000 4 ((leaves.drop 6560).take 40) 306325000000 4 = true :=
    take_step (n := 2) (t := 40) (b := 6562) rfl rfl ArealUCore.ArealUK.chunk_3280 s81
  have s79 : leavesOK ctxLitU 305275000000 4 ((leaves.drop 6558).take 42) 306325000000 4 = true :=
    take_step (n := 2) (t := 42) (b := 6560) rfl rfl ArealUCore.ArealUK.chunk_3279 s80
  have s78 : leavesOK ctxLitU 305225000000 4 ((leaves.drop 6556).take 44) 306325000000 4 = true :=
    take_step (n := 2) (t := 44) (b := 6558) rfl rfl ArealUCore.ArealUK.chunk_3278 s79
  have s77 : leavesOK ctxLitU 305175000000 4 ((leaves.drop 6554).take 46) 306325000000 4 = true :=
    take_step (n := 2) (t := 46) (b := 6556) rfl rfl ArealUCore.ArealUK.chunk_3277 s78
  have s76 : leavesOK ctxLitU 305125000000 4 ((leaves.drop 6552).take 48) 306325000000 4 = true :=
    take_step (n := 2) (t := 48) (b := 6554) rfl rfl ArealUCore.ArealUK.chunk_3276 s77
  have s75 : leavesOK ctxLitU 305075000000 4 ((leaves.drop 6550).take 50) 306325000000 4 = true :=
    take_step (n := 2) (t := 50) (b := 6552) rfl rfl ArealUCore.ArealUK.chunk_3275 s76
  have s74 : leavesOK ctxLitU 305025000000 4 ((leaves.drop 6548).take 52) 306325000000 4 = true :=
    take_step (n := 2) (t := 52) (b := 6550) rfl rfl ArealUCore.ArealUK.chunk_3274 s75
  have s73 : leavesOK ctxLitU 304975000000 4 ((leaves.drop 6546).take 54) 306325000000 4 = true :=
    take_step (n := 2) (t := 54) (b := 6548) rfl rfl ArealUCore.ArealUK.chunk_3273 s74
  have s72 : leavesOK ctxLitU 304925000000 4 ((leaves.drop 6544).take 56) 306325000000 4 = true :=
    take_step (n := 2) (t := 56) (b := 6546) rfl rfl ArealUCore.ArealUK.chunk_3272 s73
  have s71 : leavesOK ctxLitU 304875000000 4 ((leaves.drop 6542).take 58) 306325000000 4 = true :=
    take_step (n := 2) (t := 58) (b := 6544) rfl rfl ArealUCore.ArealUK.chunk_3271 s72
  have s70 : leavesOK ctxLitU 304825000000 4 ((leaves.drop 6540).take 60) 306325000000 4 = true :=
    take_step (n := 2) (t := 60) (b := 6542) rfl rfl ArealUCore.ArealUK.chunk_3270 s71
  have s69 : leavesOK ctxLitU 304775000000 4 ((leaves.drop 6538).take 62) 306325000000 4 = true :=
    take_step (n := 2) (t := 62) (b := 6540) rfl rfl ArealUCore.ArealUK.chunk_3269 s70
  have s68 : leavesOK ctxLitU 304725000000 4 ((leaves.drop 6536).take 64) 306325000000 4 = true :=
    take_step (n := 2) (t := 64) (b := 6538) rfl rfl ArealUCore.ArealUK.chunk_3268 s69
  have s67 : leavesOK ctxLitU 304675000000 4 ((leaves.drop 6534).take 66) 306325000000 4 = true :=
    take_step (n := 2) (t := 66) (b := 6536) rfl rfl ArealUCore.ArealUK.chunk_3267 s68
  have s66 : leavesOK ctxLitU 304625000000 4 ((leaves.drop 6532).take 68) 306325000000 4 = true :=
    take_step (n := 2) (t := 68) (b := 6534) rfl rfl ArealUCore.ArealUK.chunk_3266 s67
  have s65 : leavesOK ctxLitU 304575000000 4 ((leaves.drop 6530).take 70) 306325000000 4 = true :=
    take_step (n := 2) (t := 70) (b := 6532) rfl rfl ArealUCore.ArealUK.chunk_3265 s66
  have s64 : leavesOK ctxLitU 304525000000 4 ((leaves.drop 6528).take 72) 306325000000 4 = true :=
    take_step (n := 2) (t := 72) (b := 6530) rfl rfl ArealUCore.ArealUK.chunk_3264 s65
  have s63 : leavesOK ctxLitU 304475000000 4 ((leaves.drop 6526).take 74) 306325000000 4 = true :=
    take_step (n := 2) (t := 74) (b := 6528) rfl rfl ArealUCore.ArealUK.chunk_3263 s64
  have s62 : leavesOK ctxLitU 304425000000 4 ((leaves.drop 6524).take 76) 306325000000 4 = true :=
    take_step (n := 2) (t := 76) (b := 6526) rfl rfl ArealUCore.ArealUK.chunk_3262 s63
  have s61 : leavesOK ctxLitU 304375000000 4 ((leaves.drop 6522).take 78) 306325000000 4 = true :=
    take_step (n := 2) (t := 78) (b := 6524) rfl rfl ArealUCore.ArealUK.chunk_3261 s62
  have s60 : leavesOK ctxLitU 304325000000 4 ((leaves.drop 6520).take 80) 306325000000 4 = true :=
    take_step (n := 2) (t := 80) (b := 6522) rfl rfl ArealUCore.ArealUK.chunk_3260 s61
  have s59 : leavesOK ctxLitU 304275000000 4 ((leaves.drop 6518).take 82) 306325000000 4 = true :=
    take_step (n := 2) (t := 82) (b := 6520) rfl rfl ArealUCore.ArealUK.chunk_3259 s60
  have s58 : leavesOK ctxLitU 304225000000 4 ((leaves.drop 6516).take 84) 306325000000 4 = true :=
    take_step (n := 2) (t := 84) (b := 6518) rfl rfl ArealUCore.ArealUK.chunk_3258 s59
  have s57 : leavesOK ctxLitU 304175000000 4 ((leaves.drop 6514).take 86) 306325000000 4 = true :=
    take_step (n := 2) (t := 86) (b := 6516) rfl rfl ArealUCore.ArealUK.chunk_3257 s58
  have s56 : leavesOK ctxLitU 304125000000 4 ((leaves.drop 6512).take 88) 306325000000 4 = true :=
    take_step (n := 2) (t := 88) (b := 6514) rfl rfl ArealUCore.ArealUK.chunk_3256 s57
  have s55 : leavesOK ctxLitU 304075000000 4 ((leaves.drop 6510).take 90) 306325000000 4 = true :=
    take_step (n := 2) (t := 90) (b := 6512) rfl rfl ArealUCore.ArealUK.chunk_3255 s56
  have s54 : leavesOK ctxLitU 304025000000 4 ((leaves.drop 6508).take 92) 306325000000 4 = true :=
    take_step (n := 2) (t := 92) (b := 6510) rfl rfl ArealUCore.ArealUK.chunk_3254 s55
  have s53 : leavesOK ctxLitU 303975000000 4 ((leaves.drop 6506).take 94) 306325000000 4 = true :=
    take_step (n := 2) (t := 94) (b := 6508) rfl rfl ArealUCore.ArealUK.chunk_3253 s54
  have s52 : leavesOK ctxLitU 303925000000 4 ((leaves.drop 6504).take 96) 306325000000 4 = true :=
    take_step (n := 2) (t := 96) (b := 6506) rfl rfl ArealUCore.ArealUK.chunk_3252 s53
  have s51 : leavesOK ctxLitU 303875000000 4 ((leaves.drop 6502).take 98) 306325000000 4 = true :=
    take_step (n := 2) (t := 98) (b := 6504) rfl rfl ArealUCore.ArealUK.chunk_3251 s52
  have s50 : leavesOK ctxLitU 303825000000 4 ((leaves.drop 6500).take 100) 306325000000 4 = true :=
    take_step (n := 2) (t := 100) (b := 6502) rfl rfl ArealUCore.ArealUK.chunk_3250 s51
  have s49 : leavesOK ctxLitU 303775000000 4 ((leaves.drop 6498).take 102) 306325000000 4 = true :=
    take_step (n := 2) (t := 102) (b := 6500) rfl rfl ArealUCore.ArealUK.chunk_3249 s50
  have s48 : leavesOK ctxLitU 303725000000 4 ((leaves.drop 6496).take 104) 306325000000 4 = true :=
    take_step (n := 2) (t := 104) (b := 6498) rfl rfl ArealUCore.ArealUK.chunk_3248 s49
  have s47 : leavesOK ctxLitU 303675000000 4 ((leaves.drop 6494).take 106) 306325000000 4 = true :=
    take_step (n := 2) (t := 106) (b := 6496) rfl rfl ArealUCore.ArealUK.chunk_3247 s48
  have s46 : leavesOK ctxLitU 303625000000 4 ((leaves.drop 6492).take 108) 306325000000 4 = true :=
    take_step (n := 2) (t := 108) (b := 6494) rfl rfl ArealUCore.ArealUK.chunk_3246 s47
  have s45 : leavesOK ctxLitU 303575000000 4 ((leaves.drop 6490).take 110) 306325000000 4 = true :=
    take_step (n := 2) (t := 110) (b := 6492) rfl rfl ArealUCore.ArealUK.chunk_3245 s46
  have s44 : leavesOK ctxLitU 303525000000 4 ((leaves.drop 6488).take 112) 306325000000 4 = true :=
    take_step (n := 2) (t := 112) (b := 6490) rfl rfl ArealUCore.ArealUK.chunk_3244 s45
  have s43 : leavesOK ctxLitU 303475000000 4 ((leaves.drop 6486).take 114) 306325000000 4 = true :=
    take_step (n := 2) (t := 114) (b := 6488) rfl rfl ArealUCore.ArealUK.chunk_3243 s44
  have s42 : leavesOK ctxLitU 303425000000 4 ((leaves.drop 6484).take 116) 306325000000 4 = true :=
    take_step (n := 2) (t := 116) (b := 6486) rfl rfl ArealUCore.ArealUK.chunk_3242 s43
  have s41 : leavesOK ctxLitU 303375000000 4 ((leaves.drop 6482).take 118) 306325000000 4 = true :=
    take_step (n := 2) (t := 118) (b := 6484) rfl rfl ArealUCore.ArealUK.chunk_3241 s42
  have s40 : leavesOK ctxLitU 303325000000 4 ((leaves.drop 6480).take 120) 306325000000 4 = true :=
    take_step (n := 2) (t := 120) (b := 6482) rfl rfl ArealUCore.ArealUK.chunk_3240 s41
  have s39 : leavesOK ctxLitU 303275000000 4 ((leaves.drop 6478).take 122) 306325000000 4 = true :=
    take_step (n := 2) (t := 122) (b := 6480) rfl rfl ArealUCore.ArealUK.chunk_3239 s40
  have s38 : leavesOK ctxLitU 303225000000 4 ((leaves.drop 6476).take 124) 306325000000 4 = true :=
    take_step (n := 2) (t := 124) (b := 6478) rfl rfl ArealUCore.ArealUK.chunk_3238 s39
  have s37 : leavesOK ctxLitU 303175000000 4 ((leaves.drop 6474).take 126) 306325000000 4 = true :=
    take_step (n := 2) (t := 126) (b := 6476) rfl rfl ArealUCore.ArealUK.chunk_3237 s38
  have s36 : leavesOK ctxLitU 303125000000 4 ((leaves.drop 6472).take 128) 306325000000 4 = true :=
    take_step (n := 2) (t := 128) (b := 6474) rfl rfl ArealUCore.ArealUK.chunk_3236 s37
  have s35 : leavesOK ctxLitU 303075000000 4 ((leaves.drop 6470).take 130) 306325000000 4 = true :=
    take_step (n := 2) (t := 130) (b := 6472) rfl rfl ArealUCore.ArealUK.chunk_3235 s36
  have s34 : leavesOK ctxLitU 303025000000 4 ((leaves.drop 6468).take 132) 306325000000 4 = true :=
    take_step (n := 2) (t := 132) (b := 6470) rfl rfl ArealUCore.ArealUK.chunk_3234 s35
  have s33 : leavesOK ctxLitU 302975000000 4 ((leaves.drop 6466).take 134) 306325000000 4 = true :=
    take_step (n := 2) (t := 134) (b := 6468) rfl rfl ArealUCore.ArealUK.chunk_3233 s34
  have s32 : leavesOK ctxLitU 302925000000 4 ((leaves.drop 6464).take 136) 306325000000 4 = true :=
    take_step (n := 2) (t := 136) (b := 6466) rfl rfl ArealUCore.ArealUK.chunk_3232 s33
  have s31 : leavesOK ctxLitU 302875000000 4 ((leaves.drop 6462).take 138) 306325000000 4 = true :=
    take_step (n := 2) (t := 138) (b := 6464) rfl rfl ArealUCore.ArealUK.chunk_3231 s32
  have s30 : leavesOK ctxLitU 302825000000 4 ((leaves.drop 6460).take 140) 306325000000 4 = true :=
    take_step (n := 2) (t := 140) (b := 6462) rfl rfl ArealUCore.ArealUK.chunk_3230 s31
  have s29 : leavesOK ctxLitU 151387500000 3 ((leaves.drop 6458).take 142) 306325000000 4 = true :=
    take_step (n := 2) (t := 142) (b := 6460) rfl rfl ArealUCore.ArealUK.chunk_3229 s30
  have s28 : leavesOK ctxLitU 151362500000 3 ((leaves.drop 6456).take 144) 306325000000 4 = true :=
    take_step (n := 2) (t := 144) (b := 6458) rfl rfl ArealUCore.ArealUK.chunk_3228 s29
  have s27 : leavesOK ctxLitU 151337500000 3 ((leaves.drop 6454).take 146) 306325000000 4 = true :=
    take_step (n := 2) (t := 146) (b := 6456) rfl rfl ArealUCore.ArealUK.chunk_3227 s28
  have s26 : leavesOK ctxLitU 151312500000 3 ((leaves.drop 6452).take 148) 306325000000 4 = true :=
    take_step (n := 2) (t := 148) (b := 6454) rfl rfl ArealUCore.ArealUK.chunk_3226 s27
  have s25 : leavesOK ctxLitU 151287500000 3 ((leaves.drop 6450).take 150) 306325000000 4 = true :=
    take_step (n := 2) (t := 150) (b := 6452) rfl rfl ArealUCore.ArealUK.chunk_3225 s26
  have s24 : leavesOK ctxLitU 151262500000 3 ((leaves.drop 6448).take 152) 306325000000 4 = true :=
    take_step (n := 2) (t := 152) (b := 6450) rfl rfl ArealUCore.ArealUK.chunk_3224 s25
  have s23 : leavesOK ctxLitU 151237500000 3 ((leaves.drop 6446).take 154) 306325000000 4 = true :=
    take_step (n := 2) (t := 154) (b := 6448) rfl rfl ArealUCore.ArealUK.chunk_3223 s24
  have s22 : leavesOK ctxLitU 151212500000 3 ((leaves.drop 6444).take 156) 306325000000 4 = true :=
    take_step (n := 2) (t := 156) (b := 6446) rfl rfl ArealUCore.ArealUK.chunk_3222 s23
  have s21 : leavesOK ctxLitU 75593750000 2 ((leaves.drop 6442).take 158) 306325000000 4 = true :=
    take_step (n := 2) (t := 158) (b := 6444) rfl rfl ArealUCore.ArealUK.chunk_3221 s22
  have s20 : leavesOK ctxLitU 75581250000 2 ((leaves.drop 6440).take 160) 306325000000 4 = true :=
    take_step (n := 2) (t := 160) (b := 6442) rfl rfl ArealUCore.ArealUK.chunk_3220 s21
  have s19 : leavesOK ctxLitU 75568750000 2 ((leaves.drop 6438).take 162) 306325000000 4 = true :=
    take_step (n := 2) (t := 162) (b := 6440) rfl rfl ArealUCore.ArealUK.chunk_3219 s20
  have s18 : leavesOK ctxLitU 37775000000 1 ((leaves.drop 6436).take 164) 306325000000 4 = true :=
    take_step (n := 2) (t := 164) (b := 6438) rfl rfl ArealUCore.ArealUK.chunk_3218 s19
  have s17 : leavesOK ctxLitU 151081250000 3 ((leaves.drop 6434).take 166) 306325000000 4 = true :=
    take_step (n := 2) (t := 166) (b := 6436) rfl rfl ArealUCore.ArealUK.chunk_3217 s18
  have s16 : leavesOK ctxLitU 151068750000 3 ((leaves.drop 6432).take 168) 306325000000 4 = true :=
    take_step (n := 2) (t := 168) (b := 6434) rfl rfl ArealUCore.ArealUK.chunk_3216 s17
  have s15 : leavesOK ctxLitU 151056250000 3 ((leaves.drop 6430).take 170) 306325000000 4 = true :=
    take_step (n := 2) (t := 170) (b := 6432) rfl rfl ArealUCore.ArealUK.chunk_3215 s16
  have s14 : leavesOK ctxLitU 75518750000 2 ((leaves.drop 6428).take 172) 306325000000 4 = true :=
    take_step (n := 2) (t := 172) (b := 6430) rfl rfl ArealUCore.ArealUK.chunk_3214 s15
  have s13 : leavesOK ctxLitU 37750000000 1 ((leaves.drop 6426).take 174) 306325000000 4 = true :=
    take_step (n := 2) (t := 174) (b := 6428) rfl rfl ArealUCore.ArealUK.chunk_3213 s14
  have s12 : leavesOK ctxLitU 18862500000 0 ((leaves.drop 6424).take 176) 306325000000 4 = true :=
    take_step (n := 2) (t := 176) (b := 6426) rfl rfl ArealUCore.ArealUK.chunk_3212 s13
  have s11 : leavesOK ctxLitU 18850000000 0 ((leaves.drop 6422).take 178) 306325000000 4 = true :=
    take_step (n := 2) (t := 178) (b := 6424) rfl rfl ArealUCore.ArealUK.chunk_3211 s12
  have s10 : leavesOK ctxLitU 18837500000 0 ((leaves.drop 6420).take 180) 306325000000 4 = true :=
    take_step (n := 2) (t := 180) (b := 6422) rfl rfl ArealUCore.ArealUK.chunk_3210 s11
  have s9 : leavesOK ctxLitU 77119468831675 12 ((leaves.drop 6418).take 182) 306325000000 4 = true :=
    take_step (n := 2) (t := 182) (b := 6420) rfl rfl ArealUCore.ArealUK.chunk_3209 s10
  have s8 : leavesOK ctxLitU 77107200000000 12 ((leaves.drop 6416).take 184) 306325000000 4 = true :=
    take_step (n := 2) (t := 184) (b := 6418) rfl rfl ArealUCore.ArealUK.chunk_3208 s9
  have s7 : leavesOK ctxLitU 18812500000 0 ((leaves.drop 6414).take 186) 306325000000 4 = true :=
    take_step (n := 2) (t := 186) (b := 6416) rfl rfl ArealUCore.ArealUK.chunk_3207 s8
  have s6 : leavesOK ctxLitU 18800000000 0 ((leaves.drop 6412).take 188) 306325000000 4 = true :=
    take_step (n := 2) (t := 188) (b := 6414) rfl rfl ArealUCore.ArealUK.chunk_3206 s7
  have s5 : leavesOK ctxLitU 18787500000 0 ((leaves.drop 6410).take 190) 306325000000 4 = true :=
    take_step (n := 2) (t := 190) (b := 6412) rfl rfl ArealUCore.ArealUK.chunk_3205 s6
  have s4 : leavesOK ctxLitU 37556250000 1 ((leaves.drop 6408).take 192) 306325000000 4 = true :=
    take_step (n := 2) (t := 192) (b := 6410) rfl rfl ArealUCore.ArealUK.chunk_3204 s5
  have s3 : leavesOK ctxLitU 150187500000 3 ((leaves.drop 6406).take 194) 306325000000 4 = true :=
    take_step (n := 2) (t := 194) (b := 6408) rfl rfl ArealUCore.ArealUK.chunk_3203 s4
  have s2 : leavesOK ctxLitU 150162500000 3 ((leaves.drop 6404).take 196) 306325000000 4 = true :=
    take_step (n := 2) (t := 196) (b := 6406) rfl rfl ArealUCore.ArealUK.chunk_3202 s3
  have s1 : leavesOK ctxLitU 150137500000 3 ((leaves.drop 6402).take 198) 306325000000 4 = true :=
    take_step (n := 2) (t := 198) (b := 6404) rfl rfl ArealUCore.ArealUK.chunk_3201 s2
  have s0 : leavesOK ctxLitU 300250000000 4 ((leaves.drop 6400).take 200) 306325000000 4 = true :=
    take_step (n := 2) (t := 200) (b := 6402) rfl rfl ArealUCore.ArealUK.chunk_3200 s1
  exact s0

end Areal.UCert

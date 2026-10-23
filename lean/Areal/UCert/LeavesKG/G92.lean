import ArealUK.Chunk9200
import ArealUK.Chunk9201
import ArealUK.Chunk9202
import ArealUK.Chunk9203
import ArealUK.Chunk9204
import ArealUK.Chunk9205
import ArealUK.Chunk9206
import ArealUK.Chunk9207
import ArealUK.Chunk9208
import ArealUK.Chunk9209
import ArealUK.Chunk9210
import ArealUK.Chunk9211
import ArealUK.Chunk9212
import ArealUK.Chunk9213
import ArealUK.Chunk9214
import ArealUK.Chunk9215
import ArealUK.Chunk9216
import ArealUK.Chunk9217
import ArealUK.Chunk9218
import ArealUK.Chunk9219
import ArealUK.Chunk9220
import ArealUK.Chunk9221
import ArealUK.Chunk9222
import ArealUK.Chunk9223
import ArealUK.Chunk9224
import ArealUK.Chunk9225
import ArealUK.Chunk9226
import ArealUK.Chunk9227
import ArealUK.Chunk9228
import ArealUK.Chunk9229
import ArealUK.Chunk9230
import ArealUK.Chunk9231
import ArealUK.Chunk9232
import ArealUK.Chunk9233
import ArealUK.Chunk9234
import ArealUK.Chunk9235
import ArealUK.Chunk9236
import ArealUK.Chunk9237
import ArealUK.Chunk9238
import ArealUK.Chunk9239
import ArealUK.Chunk9240
import ArealUK.Chunk9241
import ArealUK.Chunk9242
import ArealUK.Chunk9243
import ArealUK.Chunk9244
import ArealUK.Chunk9245
import ArealUK.Chunk9246
import ArealUK.Chunk9247
import ArealUK.Chunk9248
import ArealUK.Chunk9249
import ArealUK.Chunk9250
import ArealUK.Chunk9251
import ArealUK.Chunk9252
import ArealUK.Chunk9253
import ArealUK.Chunk9254
import ArealUK.Chunk9255
import ArealUK.Chunk9256
import ArealUK.Chunk9257
import ArealUK.Chunk9258
import ArealUK.Chunk9259
import ArealUK.Chunk9260
import ArealUK.Chunk9261
import ArealUK.Chunk9262
import ArealUK.Chunk9263
import ArealUK.Chunk9264
import ArealUK.Chunk9265
import ArealUK.Chunk9266
import ArealUK.Chunk9267
import ArealUK.Chunk9268
import ArealUK.Chunk9269
import ArealUK.Chunk9270
import ArealUK.Chunk9271
import ArealUK.Chunk9272
import ArealUK.Chunk9273
import ArealUK.Chunk9274
import ArealUK.Chunk9275
import ArealUK.Chunk9276
import ArealUK.Chunk9277
import ArealUK.Chunk9278
import ArealUK.Chunk9279
import ArealUK.Chunk9280
import ArealUK.Chunk9281
import ArealUK.Chunk9282
import ArealUK.Chunk9283
import ArealUK.Chunk9284
import ArealUK.Chunk9285
import ArealUK.Chunk9286
import ArealUK.Chunk9287
import ArealUK.Chunk9288
import ArealUK.Chunk9289
import ArealUK.Chunk9290
import ArealUK.Chunk9291
import ArealUK.Chunk9292
import ArealUK.Chunk9293
import ArealUK.Chunk9294
import ArealUK.Chunk9295
import ArealUK.Chunk9296
import ArealUK.Chunk9297
import ArealUK.Chunk9298
import ArealUK.Chunk9299
import Areal.UCert.LeavesKGen

/-! Group 92 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_92 : leavesOK ctxLitU 314875000000 2 ((leaves.drop 18400).take 200) 319875000000 2 = true := by
  have s99 := ArealUCore.ArealUK.chunk_9299
  have s98 : leavesOK ctxLitU 319775000000 2 ((leaves.drop 18596).take 4) 319875000000 2 = true :=
    take_step (n := 2) (t := 4) (b := 18598) rfl rfl ArealUCore.ArealUK.chunk_9298 s99
  have s97 : leavesOK ctxLitU 319725000000 2 ((leaves.drop 18594).take 6) 319875000000 2 = true :=
    take_step (n := 2) (t := 6) (b := 18596) rfl rfl ArealUCore.ArealUK.chunk_9297 s98
  have s96 : leavesOK ctxLitU 319675000000 2 ((leaves.drop 18592).take 8) 319875000000 2 = true :=
    take_step (n := 2) (t := 8) (b := 18594) rfl rfl ArealUCore.ArealUK.chunk_9296 s97
  have s95 : leavesOK ctxLitU 319625000000 2 ((leaves.drop 18590).take 10) 319875000000 2 = true :=
    take_step (n := 2) (t := 10) (b := 18592) rfl rfl ArealUCore.ArealUK.chunk_9295 s96
  have s94 : leavesOK ctxLitU 319575000000 2 ((leaves.drop 18588).take 12) 319875000000 2 = true :=
    take_step (n := 2) (t := 12) (b := 18590) rfl rfl ArealUCore.ArealUK.chunk_9294 s95
  have s93 : leavesOK ctxLitU 319525000000 2 ((leaves.drop 18586).take 14) 319875000000 2 = true :=
    take_step (n := 2) (t := 14) (b := 18588) rfl rfl ArealUCore.ArealUK.chunk_9293 s94
  have s92 : leavesOK ctxLitU 319475000000 2 ((leaves.drop 18584).take 16) 319875000000 2 = true :=
    take_step (n := 2) (t := 16) (b := 18586) rfl rfl ArealUCore.ArealUK.chunk_9292 s93
  have s91 : leavesOK ctxLitU 319425000000 2 ((leaves.drop 18582).take 18) 319875000000 2 = true :=
    take_step (n := 2) (t := 18) (b := 18584) rfl rfl ArealUCore.ArealUK.chunk_9291 s92
  have s90 : leavesOK ctxLitU 319375000000 2 ((leaves.drop 18580).take 20) 319875000000 2 = true :=
    take_step (n := 2) (t := 20) (b := 18582) rfl rfl ArealUCore.ArealUK.chunk_9290 s91
  have s89 : leavesOK ctxLitU 319325000000 2 ((leaves.drop 18578).take 22) 319875000000 2 = true :=
    take_step (n := 2) (t := 22) (b := 18580) rfl rfl ArealUCore.ArealUK.chunk_9289 s90
  have s88 : leavesOK ctxLitU 319275000000 2 ((leaves.drop 18576).take 24) 319875000000 2 = true :=
    take_step (n := 2) (t := 24) (b := 18578) rfl rfl ArealUCore.ArealUK.chunk_9288 s89
  have s87 : leavesOK ctxLitU 319225000000 2 ((leaves.drop 18574).take 26) 319875000000 2 = true :=
    take_step (n := 2) (t := 26) (b := 18576) rfl rfl ArealUCore.ArealUK.chunk_9287 s88
  have s86 : leavesOK ctxLitU 319175000000 2 ((leaves.drop 18572).take 28) 319875000000 2 = true :=
    take_step (n := 2) (t := 28) (b := 18574) rfl rfl ArealUCore.ArealUK.chunk_9286 s87
  have s85 : leavesOK ctxLitU 319125000000 2 ((leaves.drop 18570).take 30) 319875000000 2 = true :=
    take_step (n := 2) (t := 30) (b := 18572) rfl rfl ArealUCore.ArealUK.chunk_9285 s86
  have s84 : leavesOK ctxLitU 319075000000 2 ((leaves.drop 18568).take 32) 319875000000 2 = true :=
    take_step (n := 2) (t := 32) (b := 18570) rfl rfl ArealUCore.ArealUK.chunk_9284 s85
  have s83 : leavesOK ctxLitU 319025000000 2 ((leaves.drop 18566).take 34) 319875000000 2 = true :=
    take_step (n := 2) (t := 34) (b := 18568) rfl rfl ArealUCore.ArealUK.chunk_9283 s84
  have s82 : leavesOK ctxLitU 318975000000 2 ((leaves.drop 18564).take 36) 319875000000 2 = true :=
    take_step (n := 2) (t := 36) (b := 18566) rfl rfl ArealUCore.ArealUK.chunk_9282 s83
  have s81 : leavesOK ctxLitU 318925000000 2 ((leaves.drop 18562).take 38) 319875000000 2 = true :=
    take_step (n := 2) (t := 38) (b := 18564) rfl rfl ArealUCore.ArealUK.chunk_9281 s82
  have s80 : leavesOK ctxLitU 318875000000 2 ((leaves.drop 18560).take 40) 319875000000 2 = true :=
    take_step (n := 2) (t := 40) (b := 18562) rfl rfl ArealUCore.ArealUK.chunk_9280 s81
  have s79 : leavesOK ctxLitU 318825000000 2 ((leaves.drop 18558).take 42) 319875000000 2 = true :=
    take_step (n := 2) (t := 42) (b := 18560) rfl rfl ArealUCore.ArealUK.chunk_9279 s80
  have s78 : leavesOK ctxLitU 318775000000 2 ((leaves.drop 18556).take 44) 319875000000 2 = true :=
    take_step (n := 2) (t := 44) (b := 18558) rfl rfl ArealUCore.ArealUK.chunk_9278 s79
  have s77 : leavesOK ctxLitU 318725000000 2 ((leaves.drop 18554).take 46) 319875000000 2 = true :=
    take_step (n := 2) (t := 46) (b := 18556) rfl rfl ArealUCore.ArealUK.chunk_9277 s78
  have s76 : leavesOK ctxLitU 318675000000 2 ((leaves.drop 18552).take 48) 319875000000 2 = true :=
    take_step (n := 2) (t := 48) (b := 18554) rfl rfl ArealUCore.ArealUK.chunk_9276 s77
  have s75 : leavesOK ctxLitU 318625000000 2 ((leaves.drop 18550).take 50) 319875000000 2 = true :=
    take_step (n := 2) (t := 50) (b := 18552) rfl rfl ArealUCore.ArealUK.chunk_9275 s76
  have s74 : leavesOK ctxLitU 318575000000 2 ((leaves.drop 18548).take 52) 319875000000 2 = true :=
    take_step (n := 2) (t := 52) (b := 18550) rfl rfl ArealUCore.ArealUK.chunk_9274 s75
  have s73 : leavesOK ctxLitU 318525000000 2 ((leaves.drop 18546).take 54) 319875000000 2 = true :=
    take_step (n := 2) (t := 54) (b := 18548) rfl rfl ArealUCore.ArealUK.chunk_9273 s74
  have s72 : leavesOK ctxLitU 318475000000 2 ((leaves.drop 18544).take 56) 319875000000 2 = true :=
    take_step (n := 2) (t := 56) (b := 18546) rfl rfl ArealUCore.ArealUK.chunk_9272 s73
  have s71 : leavesOK ctxLitU 318425000000 2 ((leaves.drop 18542).take 58) 319875000000 2 = true :=
    take_step (n := 2) (t := 58) (b := 18544) rfl rfl ArealUCore.ArealUK.chunk_9271 s72
  have s70 : leavesOK ctxLitU 318375000000 2 ((leaves.drop 18540).take 60) 319875000000 2 = true :=
    take_step (n := 2) (t := 60) (b := 18542) rfl rfl ArealUCore.ArealUK.chunk_9270 s71
  have s69 : leavesOK ctxLitU 318325000000 2 ((leaves.drop 18538).take 62) 319875000000 2 = true :=
    take_step (n := 2) (t := 62) (b := 18540) rfl rfl ArealUCore.ArealUK.chunk_9269 s70
  have s68 : leavesOK ctxLitU 318275000000 2 ((leaves.drop 18536).take 64) 319875000000 2 = true :=
    take_step (n := 2) (t := 64) (b := 18538) rfl rfl ArealUCore.ArealUK.chunk_9268 s69
  have s67 : leavesOK ctxLitU 318225000000 2 ((leaves.drop 18534).take 66) 319875000000 2 = true :=
    take_step (n := 2) (t := 66) (b := 18536) rfl rfl ArealUCore.ArealUK.chunk_9267 s68
  have s66 : leavesOK ctxLitU 318175000000 2 ((leaves.drop 18532).take 68) 319875000000 2 = true :=
    take_step (n := 2) (t := 68) (b := 18534) rfl rfl ArealUCore.ArealUK.chunk_9266 s67
  have s65 : leavesOK ctxLitU 318125000000 2 ((leaves.drop 18530).take 70) 319875000000 2 = true :=
    take_step (n := 2) (t := 70) (b := 18532) rfl rfl ArealUCore.ArealUK.chunk_9265 s66
  have s64 : leavesOK ctxLitU 318075000000 2 ((leaves.drop 18528).take 72) 319875000000 2 = true :=
    take_step (n := 2) (t := 72) (b := 18530) rfl rfl ArealUCore.ArealUK.chunk_9264 s65
  have s63 : leavesOK ctxLitU 318025000000 2 ((leaves.drop 18526).take 74) 319875000000 2 = true :=
    take_step (n := 2) (t := 74) (b := 18528) rfl rfl ArealUCore.ArealUK.chunk_9263 s64
  have s62 : leavesOK ctxLitU 317975000000 2 ((leaves.drop 18524).take 76) 319875000000 2 = true :=
    take_step (n := 2) (t := 76) (b := 18526) rfl rfl ArealUCore.ArealUK.chunk_9262 s63
  have s61 : leavesOK ctxLitU 317925000000 2 ((leaves.drop 18522).take 78) 319875000000 2 = true :=
    take_step (n := 2) (t := 78) (b := 18524) rfl rfl ArealUCore.ArealUK.chunk_9261 s62
  have s60 : leavesOK ctxLitU 317875000000 2 ((leaves.drop 18520).take 80) 319875000000 2 = true :=
    take_step (n := 2) (t := 80) (b := 18522) rfl rfl ArealUCore.ArealUK.chunk_9260 s61
  have s59 : leavesOK ctxLitU 317825000000 2 ((leaves.drop 18518).take 82) 319875000000 2 = true :=
    take_step (n := 2) (t := 82) (b := 18520) rfl rfl ArealUCore.ArealUK.chunk_9259 s60
  have s58 : leavesOK ctxLitU 317775000000 2 ((leaves.drop 18516).take 84) 319875000000 2 = true :=
    take_step (n := 2) (t := 84) (b := 18518) rfl rfl ArealUCore.ArealUK.chunk_9258 s59
  have s57 : leavesOK ctxLitU 317725000000 2 ((leaves.drop 18514).take 86) 319875000000 2 = true :=
    take_step (n := 2) (t := 86) (b := 18516) rfl rfl ArealUCore.ArealUK.chunk_9257 s58
  have s56 : leavesOK ctxLitU 317675000000 2 ((leaves.drop 18512).take 88) 319875000000 2 = true :=
    take_step (n := 2) (t := 88) (b := 18514) rfl rfl ArealUCore.ArealUK.chunk_9256 s57
  have s55 : leavesOK ctxLitU 317625000000 2 ((leaves.drop 18510).take 90) 319875000000 2 = true :=
    take_step (n := 2) (t := 90) (b := 18512) rfl rfl ArealUCore.ArealUK.chunk_9255 s56
  have s54 : leavesOK ctxLitU 317575000000 2 ((leaves.drop 18508).take 92) 319875000000 2 = true :=
    take_step (n := 2) (t := 92) (b := 18510) rfl rfl ArealUCore.ArealUK.chunk_9254 s55
  have s53 : leavesOK ctxLitU 317525000000 2 ((leaves.drop 18506).take 94) 319875000000 2 = true :=
    take_step (n := 2) (t := 94) (b := 18508) rfl rfl ArealUCore.ArealUK.chunk_9253 s54
  have s52 : leavesOK ctxLitU 317475000000 2 ((leaves.drop 18504).take 96) 319875000000 2 = true :=
    take_step (n := 2) (t := 96) (b := 18506) rfl rfl ArealUCore.ArealUK.chunk_9252 s53
  have s51 : leavesOK ctxLitU 317425000000 2 ((leaves.drop 18502).take 98) 319875000000 2 = true :=
    take_step (n := 2) (t := 98) (b := 18504) rfl rfl ArealUCore.ArealUK.chunk_9251 s52
  have s50 : leavesOK ctxLitU 317375000000 2 ((leaves.drop 18500).take 100) 319875000000 2 = true :=
    take_step (n := 2) (t := 100) (b := 18502) rfl rfl ArealUCore.ArealUK.chunk_9250 s51
  have s49 : leavesOK ctxLitU 317325000000 2 ((leaves.drop 18498).take 102) 319875000000 2 = true :=
    take_step (n := 2) (t := 102) (b := 18500) rfl rfl ArealUCore.ArealUK.chunk_9249 s50
  have s48 : leavesOK ctxLitU 317275000000 2 ((leaves.drop 18496).take 104) 319875000000 2 = true :=
    take_step (n := 2) (t := 104) (b := 18498) rfl rfl ArealUCore.ArealUK.chunk_9248 s49
  have s47 : leavesOK ctxLitU 317225000000 2 ((leaves.drop 18494).take 106) 319875000000 2 = true :=
    take_step (n := 2) (t := 106) (b := 18496) rfl rfl ArealUCore.ArealUK.chunk_9247 s48
  have s46 : leavesOK ctxLitU 317175000000 2 ((leaves.drop 18492).take 108) 319875000000 2 = true :=
    take_step (n := 2) (t := 108) (b := 18494) rfl rfl ArealUCore.ArealUK.chunk_9246 s47
  have s45 : leavesOK ctxLitU 317125000000 2 ((leaves.drop 18490).take 110) 319875000000 2 = true :=
    take_step (n := 2) (t := 110) (b := 18492) rfl rfl ArealUCore.ArealUK.chunk_9245 s46
  have s44 : leavesOK ctxLitU 317075000000 2 ((leaves.drop 18488).take 112) 319875000000 2 = true :=
    take_step (n := 2) (t := 112) (b := 18490) rfl rfl ArealUCore.ArealUK.chunk_9244 s45
  have s43 : leavesOK ctxLitU 317025000000 2 ((leaves.drop 18486).take 114) 319875000000 2 = true :=
    take_step (n := 2) (t := 114) (b := 18488) rfl rfl ArealUCore.ArealUK.chunk_9243 s44
  have s42 : leavesOK ctxLitU 316975000000 2 ((leaves.drop 18484).take 116) 319875000000 2 = true :=
    take_step (n := 2) (t := 116) (b := 18486) rfl rfl ArealUCore.ArealUK.chunk_9242 s43
  have s41 : leavesOK ctxLitU 316925000000 2 ((leaves.drop 18482).take 118) 319875000000 2 = true :=
    take_step (n := 2) (t := 118) (b := 18484) rfl rfl ArealUCore.ArealUK.chunk_9241 s42
  have s40 : leavesOK ctxLitU 316875000000 2 ((leaves.drop 18480).take 120) 319875000000 2 = true :=
    take_step (n := 2) (t := 120) (b := 18482) rfl rfl ArealUCore.ArealUK.chunk_9240 s41
  have s39 : leavesOK ctxLitU 316825000000 2 ((leaves.drop 18478).take 122) 319875000000 2 = true :=
    take_step (n := 2) (t := 122) (b := 18480) rfl rfl ArealUCore.ArealUK.chunk_9239 s40
  have s38 : leavesOK ctxLitU 316775000000 2 ((leaves.drop 18476).take 124) 319875000000 2 = true :=
    take_step (n := 2) (t := 124) (b := 18478) rfl rfl ArealUCore.ArealUK.chunk_9238 s39
  have s37 : leavesOK ctxLitU 316725000000 2 ((leaves.drop 18474).take 126) 319875000000 2 = true :=
    take_step (n := 2) (t := 126) (b := 18476) rfl rfl ArealUCore.ArealUK.chunk_9237 s38
  have s36 : leavesOK ctxLitU 316675000000 2 ((leaves.drop 18472).take 128) 319875000000 2 = true :=
    take_step (n := 2) (t := 128) (b := 18474) rfl rfl ArealUCore.ArealUK.chunk_9236 s37
  have s35 : leavesOK ctxLitU 316625000000 2 ((leaves.drop 18470).take 130) 319875000000 2 = true :=
    take_step (n := 2) (t := 130) (b := 18472) rfl rfl ArealUCore.ArealUK.chunk_9235 s36
  have s34 : leavesOK ctxLitU 316575000000 2 ((leaves.drop 18468).take 132) 319875000000 2 = true :=
    take_step (n := 2) (t := 132) (b := 18470) rfl rfl ArealUCore.ArealUK.chunk_9234 s35
  have s33 : leavesOK ctxLitU 316525000000 2 ((leaves.drop 18466).take 134) 319875000000 2 = true :=
    take_step (n := 2) (t := 134) (b := 18468) rfl rfl ArealUCore.ArealUK.chunk_9233 s34
  have s32 : leavesOK ctxLitU 316475000000 2 ((leaves.drop 18464).take 136) 319875000000 2 = true :=
    take_step (n := 2) (t := 136) (b := 18466) rfl rfl ArealUCore.ArealUK.chunk_9232 s33
  have s31 : leavesOK ctxLitU 316425000000 2 ((leaves.drop 18462).take 138) 319875000000 2 = true :=
    take_step (n := 2) (t := 138) (b := 18464) rfl rfl ArealUCore.ArealUK.chunk_9231 s32
  have s30 : leavesOK ctxLitU 316375000000 2 ((leaves.drop 18460).take 140) 319875000000 2 = true :=
    take_step (n := 2) (t := 140) (b := 18462) rfl rfl ArealUCore.ArealUK.chunk_9230 s31
  have s29 : leavesOK ctxLitU 316325000000 2 ((leaves.drop 18458).take 142) 319875000000 2 = true :=
    take_step (n := 2) (t := 142) (b := 18460) rfl rfl ArealUCore.ArealUK.chunk_9229 s30
  have s28 : leavesOK ctxLitU 316275000000 2 ((leaves.drop 18456).take 144) 319875000000 2 = true :=
    take_step (n := 2) (t := 144) (b := 18458) rfl rfl ArealUCore.ArealUK.chunk_9228 s29
  have s27 : leavesOK ctxLitU 316225000000 2 ((leaves.drop 18454).take 146) 319875000000 2 = true :=
    take_step (n := 2) (t := 146) (b := 18456) rfl rfl ArealUCore.ArealUK.chunk_9227 s28
  have s26 : leavesOK ctxLitU 316175000000 2 ((leaves.drop 18452).take 148) 319875000000 2 = true :=
    take_step (n := 2) (t := 148) (b := 18454) rfl rfl ArealUCore.ArealUK.chunk_9226 s27
  have s25 : leavesOK ctxLitU 316125000000 2 ((leaves.drop 18450).take 150) 319875000000 2 = true :=
    take_step (n := 2) (t := 150) (b := 18452) rfl rfl ArealUCore.ArealUK.chunk_9225 s26
  have s24 : leavesOK ctxLitU 316075000000 2 ((leaves.drop 18448).take 152) 319875000000 2 = true :=
    take_step (n := 2) (t := 152) (b := 18450) rfl rfl ArealUCore.ArealUK.chunk_9224 s25
  have s23 : leavesOK ctxLitU 316025000000 2 ((leaves.drop 18446).take 154) 319875000000 2 = true :=
    take_step (n := 2) (t := 154) (b := 18448) rfl rfl ArealUCore.ArealUK.chunk_9223 s24
  have s22 : leavesOK ctxLitU 315975000000 2 ((leaves.drop 18444).take 156) 319875000000 2 = true :=
    take_step (n := 2) (t := 156) (b := 18446) rfl rfl ArealUCore.ArealUK.chunk_9222 s23
  have s21 : leavesOK ctxLitU 315925000000 2 ((leaves.drop 18442).take 158) 319875000000 2 = true :=
    take_step (n := 2) (t := 158) (b := 18444) rfl rfl ArealUCore.ArealUK.chunk_9221 s22
  have s20 : leavesOK ctxLitU 315875000000 2 ((leaves.drop 18440).take 160) 319875000000 2 = true :=
    take_step (n := 2) (t := 160) (b := 18442) rfl rfl ArealUCore.ArealUK.chunk_9220 s21
  have s19 : leavesOK ctxLitU 315825000000 2 ((leaves.drop 18438).take 162) 319875000000 2 = true :=
    take_step (n := 2) (t := 162) (b := 18440) rfl rfl ArealUCore.ArealUK.chunk_9219 s20
  have s18 : leavesOK ctxLitU 315775000000 2 ((leaves.drop 18436).take 164) 319875000000 2 = true :=
    take_step (n := 2) (t := 164) (b := 18438) rfl rfl ArealUCore.ArealUK.chunk_9218 s19
  have s17 : leavesOK ctxLitU 315725000000 2 ((leaves.drop 18434).take 166) 319875000000 2 = true :=
    take_step (n := 2) (t := 166) (b := 18436) rfl rfl ArealUCore.ArealUK.chunk_9217 s18
  have s16 : leavesOK ctxLitU 315675000000 2 ((leaves.drop 18432).take 168) 319875000000 2 = true :=
    take_step (n := 2) (t := 168) (b := 18434) rfl rfl ArealUCore.ArealUK.chunk_9216 s17
  have s15 : leavesOK ctxLitU 315625000000 2 ((leaves.drop 18430).take 170) 319875000000 2 = true :=
    take_step (n := 2) (t := 170) (b := 18432) rfl rfl ArealUCore.ArealUK.chunk_9215 s16
  have s14 : leavesOK ctxLitU 315575000000 2 ((leaves.drop 18428).take 172) 319875000000 2 = true :=
    take_step (n := 2) (t := 172) (b := 18430) rfl rfl ArealUCore.ArealUK.chunk_9214 s15
  have s13 : leavesOK ctxLitU 315525000000 2 ((leaves.drop 18426).take 174) 319875000000 2 = true :=
    take_step (n := 2) (t := 174) (b := 18428) rfl rfl ArealUCore.ArealUK.chunk_9213 s14
  have s12 : leavesOK ctxLitU 315475000000 2 ((leaves.drop 18424).take 176) 319875000000 2 = true :=
    take_step (n := 2) (t := 176) (b := 18426) rfl rfl ArealUCore.ArealUK.chunk_9212 s13
  have s11 : leavesOK ctxLitU 315425000000 2 ((leaves.drop 18422).take 178) 319875000000 2 = true :=
    take_step (n := 2) (t := 178) (b := 18424) rfl rfl ArealUCore.ArealUK.chunk_9211 s12
  have s10 : leavesOK ctxLitU 315375000000 2 ((leaves.drop 18420).take 180) 319875000000 2 = true :=
    take_step (n := 2) (t := 180) (b := 18422) rfl rfl ArealUCore.ArealUK.chunk_9210 s11
  have s9 : leavesOK ctxLitU 315325000000 2 ((leaves.drop 18418).take 182) 319875000000 2 = true :=
    take_step (n := 2) (t := 182) (b := 18420) rfl rfl ArealUCore.ArealUK.chunk_9209 s10
  have s8 : leavesOK ctxLitU 315275000000 2 ((leaves.drop 18416).take 184) 319875000000 2 = true :=
    take_step (n := 2) (t := 184) (b := 18418) rfl rfl ArealUCore.ArealUK.chunk_9208 s9
  have s7 : leavesOK ctxLitU 315225000000 2 ((leaves.drop 18414).take 186) 319875000000 2 = true :=
    take_step (n := 2) (t := 186) (b := 18416) rfl rfl ArealUCore.ArealUK.chunk_9207 s8
  have s6 : leavesOK ctxLitU 315175000000 2 ((leaves.drop 18412).take 188) 319875000000 2 = true :=
    take_step (n := 2) (t := 188) (b := 18414) rfl rfl ArealUCore.ArealUK.chunk_9206 s7
  have s5 : leavesOK ctxLitU 315125000000 2 ((leaves.drop 18410).take 190) 319875000000 2 = true :=
    take_step (n := 2) (t := 190) (b := 18412) rfl rfl ArealUCore.ArealUK.chunk_9205 s6
  have s4 : leavesOK ctxLitU 315075000000 2 ((leaves.drop 18408).take 192) 319875000000 2 = true :=
    take_step (n := 2) (t := 192) (b := 18410) rfl rfl ArealUCore.ArealUK.chunk_9204 s5
  have s3 : leavesOK ctxLitU 315025000000 2 ((leaves.drop 18406).take 194) 319875000000 2 = true :=
    take_step (n := 2) (t := 194) (b := 18408) rfl rfl ArealUCore.ArealUK.chunk_9203 s4
  have s2 : leavesOK ctxLitU 314975000000 2 ((leaves.drop 18404).take 196) 319875000000 2 = true :=
    take_step (n := 2) (t := 196) (b := 18406) rfl rfl ArealUCore.ArealUK.chunk_9202 s3
  have s1 : leavesOK ctxLitU 314925000000 2 ((leaves.drop 18402).take 198) 319875000000 2 = true :=
    take_step (n := 2) (t := 198) (b := 18404) rfl rfl ArealUCore.ArealUK.chunk_9201 s2
  have s0 : leavesOK ctxLitU 314875000000 2 ((leaves.drop 18400).take 200) 319875000000 2 = true :=
    take_step (n := 2) (t := 200) (b := 18402) rfl rfl ArealUCore.ArealUK.chunk_9200 s1
  exact s0

end Areal.UCert

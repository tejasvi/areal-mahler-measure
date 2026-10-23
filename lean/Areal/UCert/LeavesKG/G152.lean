import ArealUK.Chunk15200
import ArealUK.Chunk15201
import ArealUK.Chunk15202
import ArealUK.Chunk15203
import ArealUK.Chunk15204
import ArealUK.Chunk15205
import ArealUK.Chunk15206
import ArealUK.Chunk15207
import ArealUK.Chunk15208
import ArealUK.Chunk15209
import ArealUK.Chunk15210
import ArealUK.Chunk15211
import ArealUK.Chunk15212
import ArealUK.Chunk15213
import ArealUK.Chunk15214
import ArealUK.Chunk15215
import ArealUK.Chunk15216
import ArealUK.Chunk15217
import ArealUK.Chunk15218
import ArealUK.Chunk15219
import ArealUK.Chunk15220
import ArealUK.Chunk15221
import ArealUK.Chunk15222
import ArealUK.Chunk15223
import ArealUK.Chunk15224
import ArealUK.Chunk15225
import ArealUK.Chunk15226
import ArealUK.Chunk15227
import ArealUK.Chunk15228
import ArealUK.Chunk15229
import ArealUK.Chunk15230
import ArealUK.Chunk15231
import ArealUK.Chunk15232
import ArealUK.Chunk15233
import ArealUK.Chunk15234
import ArealUK.Chunk15235
import ArealUK.Chunk15236
import ArealUK.Chunk15237
import ArealUK.Chunk15238
import ArealUK.Chunk15239
import ArealUK.Chunk15240
import ArealUK.Chunk15241
import ArealUK.Chunk15242
import ArealUK.Chunk15243
import ArealUK.Chunk15244
import ArealUK.Chunk15245
import ArealUK.Chunk15246
import ArealUK.Chunk15247
import ArealUK.Chunk15248
import ArealUK.Chunk15249
import ArealUK.Chunk15250
import ArealUK.Chunk15251
import ArealUK.Chunk15252
import ArealUK.Chunk15253
import ArealUK.Chunk15254
import ArealUK.Chunk15255
import ArealUK.Chunk15256
import ArealUK.Chunk15257
import ArealUK.Chunk15258
import ArealUK.Chunk15259
import ArealUK.Chunk15260
import ArealUK.Chunk15261
import ArealUK.Chunk15262
import ArealUK.Chunk15263
import ArealUK.Chunk15264
import ArealUK.Chunk15265
import ArealUK.Chunk15266
import ArealUK.Chunk15267
import ArealUK.Chunk15268
import ArealUK.Chunk15269
import ArealUK.Chunk15270
import ArealUK.Chunk15271
import ArealUK.Chunk15272
import ArealUK.Chunk15273
import ArealUK.Chunk15274
import ArealUK.Chunk15275
import ArealUK.Chunk15276
import ArealUK.Chunk15277
import ArealUK.Chunk15278
import ArealUK.Chunk15279
import ArealUK.Chunk15280
import ArealUK.Chunk15281
import ArealUK.Chunk15282
import ArealUK.Chunk15283
import ArealUK.Chunk15284
import ArealUK.Chunk15285
import ArealUK.Chunk15286
import ArealUK.Chunk15287
import ArealUK.Chunk15288
import ArealUK.Chunk15289
import ArealUK.Chunk15290
import ArealUK.Chunk15291
import ArealUK.Chunk15292
import ArealUK.Chunk15293
import ArealUK.Chunk15294
import ArealUK.Chunk15295
import ArealUK.Chunk15296
import ArealUK.Chunk15297
import ArealUK.Chunk15298
import ArealUK.Chunk15299
import Areal.UCert.LeavesKGen

/-! Group 152 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_152 : leavesOK ctxLitU 159218750000 0 ((leaves.drop 30400).take 200) 321387500000 1 = true := by
  have s99 := ArealUCore.ArealUK.chunk_15299
  have s98 : leavesOK ctxLitU 160668750000 0 ((leaves.drop 30596).take 4) 321387500000 1 = true :=
    take_step (n := 2) (t := 4) (b := 30598) rfl rfl ArealUCore.ArealUK.chunk_15298 s99
  have s97 : leavesOK ctxLitU 160656250000 0 ((leaves.drop 30594).take 6) 321387500000 1 = true :=
    take_step (n := 2) (t := 6) (b := 30596) rfl rfl ArealUCore.ArealUK.chunk_15297 s98
  have s96 : leavesOK ctxLitU 160643750000 0 ((leaves.drop 30592).take 8) 321387500000 1 = true :=
    take_step (n := 2) (t := 8) (b := 30594) rfl rfl ArealUCore.ArealUK.chunk_15296 s97
  have s95 : leavesOK ctxLitU 160631250000 0 ((leaves.drop 30590).take 10) 321387500000 1 = true :=
    take_step (n := 2) (t := 10) (b := 30592) rfl rfl ArealUCore.ArealUK.chunk_15295 s96
  have s94 : leavesOK ctxLitU 160618750000 0 ((leaves.drop 30588).take 12) 321387500000 1 = true :=
    take_step (n := 2) (t := 12) (b := 30590) rfl rfl ArealUCore.ArealUK.chunk_15294 s95
  have s93 : leavesOK ctxLitU 160606250000 0 ((leaves.drop 30586).take 14) 321387500000 1 = true :=
    take_step (n := 2) (t := 14) (b := 30588) rfl rfl ArealUCore.ArealUK.chunk_15293 s94
  have s92 : leavesOK ctxLitU 160587500000 0 ((leaves.drop 30584).take 16) 321387500000 1 = true :=
    take_step (n := 2) (t := 16) (b := 30586) rfl rfl ArealUCore.ArealUK.chunk_15292 s93
  have s91 : leavesOK ctxLitU 160568750000 0 ((leaves.drop 30582).take 18) 321387500000 1 = true :=
    take_step (n := 2) (t := 18) (b := 30584) rfl rfl ArealUCore.ArealUK.chunk_15291 s92
  have s90 : leavesOK ctxLitU 160556250000 0 ((leaves.drop 30580).take 20) 321387500000 1 = true :=
    take_step (n := 2) (t := 20) (b := 30582) rfl rfl ArealUCore.ArealUK.chunk_15290 s91
  have s89 : leavesOK ctxLitU 160537500000 0 ((leaves.drop 30578).take 22) 321387500000 1 = true :=
    take_step (n := 2) (t := 22) (b := 30580) rfl rfl ArealUCore.ArealUK.chunk_15289 s90
  have s88 : leavesOK ctxLitU 321025000000 1 ((leaves.drop 30576).take 24) 321387500000 1 = true :=
    take_step (n := 2) (t := 24) (b := 30578) rfl rfl ArealUCore.ArealUK.chunk_15288 s89
  have s87 : leavesOK ctxLitU 320987500000 1 ((leaves.drop 30574).take 26) 321387500000 1 = true :=
    take_step (n := 2) (t := 26) (b := 30576) rfl rfl ArealUCore.ArealUK.chunk_15287 s88
  have s86 : leavesOK ctxLitU 160475000000 0 ((leaves.drop 30572).take 28) 321387500000 1 = true :=
    take_step (n := 2) (t := 28) (b := 30574) rfl rfl ArealUCore.ArealUK.chunk_15286 s87
  have s85 : leavesOK ctxLitU 160462500000 0 ((leaves.drop 30570).take 30) 321387500000 1 = true :=
    take_step (n := 2) (t := 30) (b := 30572) rfl rfl ArealUCore.ArealUK.chunk_15285 s86
  have s84 : leavesOK ctxLitU 160450000000 0 ((leaves.drop 30568).take 32) 321387500000 1 = true :=
    take_step (n := 2) (t := 32) (b := 30570) rfl rfl ArealUCore.ArealUK.chunk_15284 s85
  have s83 : leavesOK ctxLitU 160437500000 0 ((leaves.drop 30566).take 34) 321387500000 1 = true :=
    take_step (n := 2) (t := 34) (b := 30568) rfl rfl ArealUCore.ArealUK.chunk_15283 s84
  have s82 : leavesOK ctxLitU 160425000000 0 ((leaves.drop 30564).take 36) 321387500000 1 = true :=
    take_step (n := 2) (t := 36) (b := 30566) rfl rfl ArealUCore.ArealUK.chunk_15282 s83
  have s81 : leavesOK ctxLitU 160412500000 0 ((leaves.drop 30562).take 38) 321387500000 1 = true :=
    take_step (n := 2) (t := 38) (b := 30564) rfl rfl ArealUCore.ArealUK.chunk_15281 s82
  have s80 : leavesOK ctxLitU 160400000000 0 ((leaves.drop 30560).take 40) 321387500000 1 = true :=
    take_step (n := 2) (t := 40) (b := 30562) rfl rfl ArealUCore.ArealUK.chunk_15280 s81
  have s79 : leavesOK ctxLitU 160387500000 0 ((leaves.drop 30558).take 42) 321387500000 1 = true :=
    take_step (n := 2) (t := 42) (b := 30560) rfl rfl ArealUCore.ArealUK.chunk_15279 s80
  have s78 : leavesOK ctxLitU 160375000000 0 ((leaves.drop 30556).take 44) 321387500000 1 = true :=
    take_step (n := 2) (t := 44) (b := 30558) rfl rfl ArealUCore.ArealUK.chunk_15278 s79
  have s77 : leavesOK ctxLitU 160362500000 0 ((leaves.drop 30554).take 46) 321387500000 1 = true :=
    take_step (n := 2) (t := 46) (b := 30556) rfl rfl ArealUCore.ArealUK.chunk_15277 s78
  have s76 : leavesOK ctxLitU 160350000000 0 ((leaves.drop 30552).take 48) 321387500000 1 = true :=
    take_step (n := 2) (t := 48) (b := 30554) rfl rfl ArealUCore.ArealUK.chunk_15276 s77
  have s75 : leavesOK ctxLitU 160337500000 0 ((leaves.drop 30550).take 50) 321387500000 1 = true :=
    take_step (n := 2) (t := 50) (b := 30552) rfl rfl ArealUCore.ArealUK.chunk_15275 s76
  have s74 : leavesOK ctxLitU 160325000000 0 ((leaves.drop 30548).take 52) 321387500000 1 = true :=
    take_step (n := 2) (t := 52) (b := 30550) rfl rfl ArealUCore.ArealUK.chunk_15274 s75
  have s73 : leavesOK ctxLitU 320625000000 1 ((leaves.drop 30546).take 54) 321387500000 1 = true :=
    take_step (n := 2) (t := 54) (b := 30548) rfl rfl ArealUCore.ArealUK.chunk_15273 s74
  have s72 : leavesOK ctxLitU 320600000000 1 ((leaves.drop 30544).take 56) 321387500000 1 = true :=
    take_step (n := 2) (t := 56) (b := 30546) rfl rfl ArealUCore.ArealUK.chunk_15272 s73
  have s71 : leavesOK ctxLitU 160275000000 0 ((leaves.drop 30542).take 58) 321387500000 1 = true :=
    take_step (n := 2) (t := 58) (b := 30544) rfl rfl ArealUCore.ArealUK.chunk_15271 s72
  have s70 : leavesOK ctxLitU 160262500000 0 ((leaves.drop 30540).take 60) 321387500000 1 = true :=
    take_step (n := 2) (t := 60) (b := 30542) rfl rfl ArealUCore.ArealUK.chunk_15270 s71
  have s69 : leavesOK ctxLitU 160250000000 0 ((leaves.drop 30538).take 62) 321387500000 1 = true :=
    take_step (n := 2) (t := 62) (b := 30540) rfl rfl ArealUCore.ArealUK.chunk_15269 s70
  have s68 : leavesOK ctxLitU 160237500000 0 ((leaves.drop 30536).take 64) 321387500000 1 = true :=
    take_step (n := 2) (t := 64) (b := 30538) rfl rfl ArealUCore.ArealUK.chunk_15268 s69
  have s67 : leavesOK ctxLitU 160225000000 0 ((leaves.drop 30534).take 66) 321387500000 1 = true :=
    take_step (n := 2) (t := 66) (b := 30536) rfl rfl ArealUCore.ArealUK.chunk_15267 s68
  have s66 : leavesOK ctxLitU 160200000000 0 ((leaves.drop 30532).take 68) 321387500000 1 = true :=
    take_step (n := 2) (t := 68) (b := 30534) rfl rfl ArealUCore.ArealUK.chunk_15266 s67
  have s65 : leavesOK ctxLitU 160175000000 0 ((leaves.drop 30530).take 70) 321387500000 1 = true :=
    take_step (n := 2) (t := 70) (b := 30532) rfl rfl ArealUCore.ArealUK.chunk_15265 s66
  have s64 : leavesOK ctxLitU 160162500000 0 ((leaves.drop 30528).take 72) 321387500000 1 = true :=
    take_step (n := 2) (t := 72) (b := 30530) rfl rfl ArealUCore.ArealUK.chunk_15264 s65
  have s63 : leavesOK ctxLitU 160150000000 0 ((leaves.drop 30526).take 74) 321387500000 1 = true :=
    take_step (n := 2) (t := 74) (b := 30528) rfl rfl ArealUCore.ArealUK.chunk_15263 s64
  have s62 : leavesOK ctxLitU 160137500000 0 ((leaves.drop 30524).take 76) 321387500000 1 = true :=
    take_step (n := 2) (t := 76) (b := 30526) rfl rfl ArealUCore.ArealUK.chunk_15262 s63
  have s61 : leavesOK ctxLitU 160125000000 0 ((leaves.drop 30522).take 78) 321387500000 1 = true :=
    take_step (n := 2) (t := 78) (b := 30524) rfl rfl ArealUCore.ArealUK.chunk_15261 s62
  have s60 : leavesOK ctxLitU 160100000000 0 ((leaves.drop 30520).take 80) 321387500000 1 = true :=
    take_step (n := 2) (t := 80) (b := 30522) rfl rfl ArealUCore.ArealUK.chunk_15260 s61
  have s59 : leavesOK ctxLitU 320175000000 1 ((leaves.drop 30518).take 82) 321387500000 1 = true :=
    take_step (n := 2) (t := 82) (b := 30520) rfl rfl ArealUCore.ArealUK.chunk_15259 s60
  have s58 : leavesOK ctxLitU 320150000000 1 ((leaves.drop 30516).take 84) 321387500000 1 = true :=
    take_step (n := 2) (t := 84) (b := 30518) rfl rfl ArealUCore.ArealUK.chunk_15258 s59
  have s57 : leavesOK ctxLitU 160062500000 0 ((leaves.drop 30514).take 86) 321387500000 1 = true :=
    take_step (n := 2) (t := 86) (b := 30516) rfl rfl ArealUCore.ArealUK.chunk_15257 s58
  have s56 : leavesOK ctxLitU 160050000000 0 ((leaves.drop 30512).take 88) 321387500000 1 = true :=
    take_step (n := 2) (t := 88) (b := 30514) rfl rfl ArealUCore.ArealUK.chunk_15256 s57
  have s55 : leavesOK ctxLitU 160037500000 0 ((leaves.drop 30510).take 90) 321387500000 1 = true :=
    take_step (n := 2) (t := 90) (b := 30512) rfl rfl ArealUCore.ArealUK.chunk_15255 s56
  have s54 : leavesOK ctxLitU 160025000000 0 ((leaves.drop 30508).take 92) 321387500000 1 = true :=
    take_step (n := 2) (t := 92) (b := 30510) rfl rfl ArealUCore.ArealUK.chunk_15254 s55
  have s53 : leavesOK ctxLitU 160000000000 0 ((leaves.drop 30506).take 94) 321387500000 1 = true :=
    take_step (n := 2) (t := 94) (b := 30508) rfl rfl ArealUCore.ArealUK.chunk_15253 s54
  have s52 : leavesOK ctxLitU 159975000000 0 ((leaves.drop 30504).take 96) 321387500000 1 = true :=
    take_step (n := 2) (t := 96) (b := 30506) rfl rfl ArealUCore.ArealUK.chunk_15252 s53
  have s51 : leavesOK ctxLitU 159962500000 0 ((leaves.drop 30502).take 98) 321387500000 1 = true :=
    take_step (n := 2) (t := 98) (b := 30504) rfl rfl ArealUCore.ArealUK.chunk_15251 s52
  have s50 : leavesOK ctxLitU 159950000000 0 ((leaves.drop 30500).take 100) 321387500000 1 = true :=
    take_step (n := 2) (t := 100) (b := 30502) rfl rfl ArealUCore.ArealUK.chunk_15250 s51
  have s49 : leavesOK ctxLitU 159937500000 0 ((leaves.drop 30498).take 102) 321387500000 1 = true :=
    take_step (n := 2) (t := 102) (b := 30500) rfl rfl ArealUCore.ArealUK.chunk_15249 s50
  have s48 : leavesOK ctxLitU 159925000000 0 ((leaves.drop 30496).take 104) 321387500000 1 = true :=
    take_step (n := 2) (t := 104) (b := 30498) rfl rfl ArealUCore.ArealUK.chunk_15248 s49
  have s47 : leavesOK ctxLitU 159900000000 0 ((leaves.drop 30494).take 106) 321387500000 1 = true :=
    take_step (n := 2) (t := 106) (b := 30496) rfl rfl ArealUCore.ArealUK.chunk_15247 s48
  have s46 : leavesOK ctxLitU 319775000000 1 ((leaves.drop 30492).take 108) 321387500000 1 = true :=
    take_step (n := 2) (t := 108) (b := 30494) rfl rfl ArealUCore.ArealUK.chunk_15246 s47
  have s45 : leavesOK ctxLitU 319750000000 1 ((leaves.drop 30490).take 110) 321387500000 1 = true :=
    take_step (n := 2) (t := 110) (b := 30492) rfl rfl ArealUCore.ArealUK.chunk_15245 s46
  have s44 : leavesOK ctxLitU 159862500000 0 ((leaves.drop 30488).take 112) 321387500000 1 = true :=
    take_step (n := 2) (t := 112) (b := 30490) rfl rfl ArealUCore.ArealUK.chunk_15244 s45
  have s43 : leavesOK ctxLitU 159850000000 0 ((leaves.drop 30486).take 114) 321387500000 1 = true :=
    take_step (n := 2) (t := 114) (b := 30488) rfl rfl ArealUCore.ArealUK.chunk_15243 s44
  have s42 : leavesOK ctxLitU 159837500000 0 ((leaves.drop 30484).take 116) 321387500000 1 = true :=
    take_step (n := 2) (t := 116) (b := 30486) rfl rfl ArealUCore.ArealUK.chunk_15242 s43
  have s41 : leavesOK ctxLitU 159825000000 0 ((leaves.drop 30482).take 118) 321387500000 1 = true :=
    take_step (n := 2) (t := 118) (b := 30484) rfl rfl ArealUCore.ArealUK.chunk_15241 s42
  have s40 : leavesOK ctxLitU 159812500000 0 ((leaves.drop 30480).take 120) 321387500000 1 = true :=
    take_step (n := 2) (t := 120) (b := 30482) rfl rfl ArealUCore.ArealUK.chunk_15240 s41
  have s39 : leavesOK ctxLitU 159800000000 0 ((leaves.drop 30478).take 122) 321387500000 1 = true :=
    take_step (n := 2) (t := 122) (b := 30480) rfl rfl ArealUCore.ArealUK.chunk_15239 s40
  have s38 : leavesOK ctxLitU 159787500000 0 ((leaves.drop 30476).take 124) 321387500000 1 = true :=
    take_step (n := 2) (t := 124) (b := 30478) rfl rfl ArealUCore.ArealUK.chunk_15238 s39
  have s37 : leavesOK ctxLitU 159775000000 0 ((leaves.drop 30474).take 126) 321387500000 1 = true :=
    take_step (n := 2) (t := 126) (b := 30476) rfl rfl ArealUCore.ArealUK.chunk_15237 s38
  have s36 : leavesOK ctxLitU 159762500000 0 ((leaves.drop 30472).take 128) 321387500000 1 = true :=
    take_step (n := 2) (t := 128) (b := 30474) rfl rfl ArealUCore.ArealUK.chunk_15236 s37
  have s35 : leavesOK ctxLitU 159750000000 0 ((leaves.drop 30470).take 130) 321387500000 1 = true :=
    take_step (n := 2) (t := 130) (b := 30472) rfl rfl ArealUCore.ArealUK.chunk_15235 s36
  have s34 : leavesOK ctxLitU 159737500000 0 ((leaves.drop 30468).take 132) 321387500000 1 = true :=
    take_step (n := 2) (t := 132) (b := 30470) rfl rfl ArealUCore.ArealUK.chunk_15234 s35
  have s33 : leavesOK ctxLitU 159725000000 0 ((leaves.drop 30466).take 134) 321387500000 1 = true :=
    take_step (n := 2) (t := 134) (b := 30468) rfl rfl ArealUCore.ArealUK.chunk_15233 s34
  have s32 : leavesOK ctxLitU 319412500000 1 ((leaves.drop 30464).take 136) 321387500000 1 = true :=
    take_step (n := 2) (t := 136) (b := 30466) rfl rfl ArealUCore.ArealUK.chunk_15232 s33
  have s31 : leavesOK ctxLitU 159693750000 0 ((leaves.drop 30462).take 138) 321387500000 1 = true :=
    take_step (n := 2) (t := 138) (b := 30464) rfl rfl ArealUCore.ArealUK.chunk_15231 s32
  have s30 : leavesOK ctxLitU 159681250000 0 ((leaves.drop 30460).take 140) 321387500000 1 = true :=
    take_step (n := 2) (t := 140) (b := 30462) rfl rfl ArealUCore.ArealUK.chunk_15230 s31
  have s29 : leavesOK ctxLitU 159662500000 0 ((leaves.drop 30458).take 142) 321387500000 1 = true :=
    take_step (n := 2) (t := 142) (b := 30460) rfl rfl ArealUCore.ArealUK.chunk_15229 s30
  have s28 : leavesOK ctxLitU 319275000000 1 ((leaves.drop 30456).take 144) 321387500000 1 = true :=
    take_step (n := 2) (t := 144) (b := 30458) rfl rfl ArealUCore.ArealUK.chunk_15228 s29
  have s27 : leavesOK ctxLitU 319237500000 1 ((leaves.drop 30454).take 146) 321387500000 1 = true :=
    take_step (n := 2) (t := 146) (b := 30456) rfl rfl ArealUCore.ArealUK.chunk_15227 s28
  have s26 : leavesOK ctxLitU 319212500000 1 ((leaves.drop 30452).take 148) 321387500000 1 = true :=
    take_step (n := 2) (t := 148) (b := 30454) rfl rfl ArealUCore.ArealUK.chunk_15226 s27
  have s25 : leavesOK ctxLitU 159593750000 0 ((leaves.drop 30450).take 150) 321387500000 1 = true :=
    take_step (n := 2) (t := 150) (b := 30452) rfl rfl ArealUCore.ArealUK.chunk_15225 s26
  have s24 : leavesOK ctxLitU 159581250000 0 ((leaves.drop 30448).take 152) 321387500000 1 = true :=
    take_step (n := 2) (t := 152) (b := 30450) rfl rfl ArealUCore.ArealUK.chunk_15224 s25
  have s23 : leavesOK ctxLitU 159568750000 0 ((leaves.drop 30446).take 154) 321387500000 1 = true :=
    take_step (n := 2) (t := 154) (b := 30448) rfl rfl ArealUCore.ArealUK.chunk_15223 s24
  have s22 : leavesOK ctxLitU 159556250000 0 ((leaves.drop 30444).take 156) 321387500000 1 = true :=
    take_step (n := 2) (t := 156) (b := 30446) rfl rfl ArealUCore.ArealUK.chunk_15222 s23
  have s21 : leavesOK ctxLitU 159543750000 0 ((leaves.drop 30442).take 158) 321387500000 1 = true :=
    take_step (n := 2) (t := 158) (b := 30444) rfl rfl ArealUCore.ArealUK.chunk_15221 s22
  have s20 : leavesOK ctxLitU 159531250000 0 ((leaves.drop 30440).take 160) 321387500000 1 = true :=
    take_step (n := 2) (t := 160) (b := 30442) rfl rfl ArealUCore.ArealUK.chunk_15220 s21
  have s19 : leavesOK ctxLitU 319037500000 1 ((leaves.drop 30438).take 162) 321387500000 1 = true :=
    take_step (n := 2) (t := 162) (b := 30440) rfl rfl ArealUCore.ArealUK.chunk_15219 s20
  have s18 : leavesOK ctxLitU 319012500000 1 ((leaves.drop 30436).take 164) 321387500000 1 = true :=
    take_step (n := 2) (t := 164) (b := 30438) rfl rfl ArealUCore.ArealUK.chunk_15218 s19
  have s17 : leavesOK ctxLitU 318975000000 1 ((leaves.drop 30434).take 166) 321387500000 1 = true :=
    take_step (n := 2) (t := 166) (b := 30436) rfl rfl ArealUCore.ArealUK.chunk_15217 s18
  have s16 : leavesOK ctxLitU 159462500000 0 ((leaves.drop 30432).take 168) 321387500000 1 = true :=
    take_step (n := 2) (t := 168) (b := 30434) rfl rfl ArealUCore.ArealUK.chunk_15216 s17
  have s15 : leavesOK ctxLitU 159443750000 0 ((leaves.drop 30430).take 170) 321387500000 1 = true :=
    take_step (n := 2) (t := 170) (b := 30432) rfl rfl ArealUCore.ArealUK.chunk_15215 s16
  have s14 : leavesOK ctxLitU 159431250000 0 ((leaves.drop 30428).take 172) 321387500000 1 = true :=
    take_step (n := 2) (t := 172) (b := 30430) rfl rfl ArealUCore.ArealUK.chunk_15214 s15
  have s13 : leavesOK ctxLitU 159412500000 0 ((leaves.drop 30426).take 174) 321387500000 1 = true :=
    take_step (n := 2) (t := 174) (b := 30428) rfl rfl ArealUCore.ArealUK.chunk_15213 s14
  have s12 : leavesOK ctxLitU 159387500000 0 ((leaves.drop 30424).take 176) 321387500000 1 = true :=
    take_step (n := 2) (t := 176) (b := 30426) rfl rfl ArealUCore.ArealUK.chunk_15212 s13
  have s11 : leavesOK ctxLitU 159368750000 0 ((leaves.drop 30422).take 178) 321387500000 1 = true :=
    take_step (n := 2) (t := 178) (b := 30424) rfl rfl ArealUCore.ArealUK.chunk_15211 s12
  have s10 : leavesOK ctxLitU 159356250000 0 ((leaves.drop 30420).take 180) 321387500000 1 = true :=
    take_step (n := 2) (t := 180) (b := 30422) rfl rfl ArealUCore.ArealUK.chunk_15210 s11
  have s9 : leavesOK ctxLitU 159343750000 0 ((leaves.drop 30418).take 182) 321387500000 1 = true :=
    take_step (n := 2) (t := 182) (b := 30420) rfl rfl ArealUCore.ArealUK.chunk_15209 s10
  have s8 : leavesOK ctxLitU 159331250000 0 ((leaves.drop 30416).take 184) 321387500000 1 = true :=
    take_step (n := 2) (t := 184) (b := 30418) rfl rfl ArealUCore.ArealUK.chunk_15208 s9
  have s7 : leavesOK ctxLitU 159312500000 0 ((leaves.drop 30414).take 186) 321387500000 1 = true :=
    take_step (n := 2) (t := 186) (b := 30416) rfl rfl ArealUCore.ArealUK.chunk_15207 s8
  have s6 : leavesOK ctxLitU 318587500000 1 ((leaves.drop 30412).take 188) 321387500000 1 = true :=
    take_step (n := 2) (t := 188) (b := 30414) rfl rfl ArealUCore.ArealUK.chunk_15206 s7
  have s5 : leavesOK ctxLitU 318562500000 1 ((leaves.drop 30410).take 190) 321387500000 1 = true :=
    take_step (n := 2) (t := 190) (b := 30412) rfl rfl ArealUCore.ArealUK.chunk_15205 s6
  have s4 : leavesOK ctxLitU 159268750000 0 ((leaves.drop 30408).take 192) 321387500000 1 = true :=
    take_step (n := 2) (t := 192) (b := 30410) rfl rfl ArealUCore.ArealUK.chunk_15204 s5
  have s3 : leavesOK ctxLitU 159256250000 0 ((leaves.drop 30406).take 194) 321387500000 1 = true :=
    take_step (n := 2) (t := 194) (b := 30408) rfl rfl ArealUCore.ArealUK.chunk_15203 s4
  have s2 : leavesOK ctxLitU 159243750000 0 ((leaves.drop 30404).take 196) 321387500000 1 = true :=
    take_step (n := 2) (t := 196) (b := 30406) rfl rfl ArealUCore.ArealUK.chunk_15202 s3
  have s1 : leavesOK ctxLitU 159231250000 0 ((leaves.drop 30402).take 198) 321387500000 1 = true :=
    take_step (n := 2) (t := 198) (b := 30404) rfl rfl ArealUCore.ArealUK.chunk_15201 s2
  have s0 : leavesOK ctxLitU 159218750000 0 ((leaves.drop 30400).take 200) 321387500000 1 = true :=
    take_step (n := 2) (t := 200) (b := 30402) rfl rfl ArealUCore.ArealUK.chunk_15200 s1
  exact s0

end Areal.UCert

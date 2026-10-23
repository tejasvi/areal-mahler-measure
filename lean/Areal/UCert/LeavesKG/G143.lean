import ArealUK.Chunk14300
import ArealUK.Chunk14301
import ArealUK.Chunk14302
import ArealUK.Chunk14303
import ArealUK.Chunk14304
import ArealUK.Chunk14305
import ArealUK.Chunk14306
import ArealUK.Chunk14307
import ArealUK.Chunk14308
import ArealUK.Chunk14309
import ArealUK.Chunk14310
import ArealUK.Chunk14311
import ArealUK.Chunk14312
import ArealUK.Chunk14313
import ArealUK.Chunk14314
import ArealUK.Chunk14315
import ArealUK.Chunk14316
import ArealUK.Chunk14317
import ArealUK.Chunk14318
import ArealUK.Chunk14319
import ArealUK.Chunk14320
import ArealUK.Chunk14321
import ArealUK.Chunk14322
import ArealUK.Chunk14323
import ArealUK.Chunk14324
import ArealUK.Chunk14325
import ArealUK.Chunk14326
import ArealUK.Chunk14327
import ArealUK.Chunk14328
import ArealUK.Chunk14329
import ArealUK.Chunk14330
import ArealUK.Chunk14331
import ArealUK.Chunk14332
import ArealUK.Chunk14333
import ArealUK.Chunk14334
import ArealUK.Chunk14335
import ArealUK.Chunk14336
import ArealUK.Chunk14337
import ArealUK.Chunk14338
import ArealUK.Chunk14339
import ArealUK.Chunk14340
import ArealUK.Chunk14341
import ArealUK.Chunk14342
import ArealUK.Chunk14343
import ArealUK.Chunk14344
import ArealUK.Chunk14345
import ArealUK.Chunk14346
import ArealUK.Chunk14347
import ArealUK.Chunk14348
import ArealUK.Chunk14349
import ArealUK.Chunk14350
import ArealUK.Chunk14351
import ArealUK.Chunk14352
import ArealUK.Chunk14353
import ArealUK.Chunk14354
import ArealUK.Chunk14355
import ArealUK.Chunk14356
import ArealUK.Chunk14357
import ArealUK.Chunk14358
import ArealUK.Chunk14359
import ArealUK.Chunk14360
import ArealUK.Chunk14361
import ArealUK.Chunk14362
import ArealUK.Chunk14363
import ArealUK.Chunk14364
import ArealUK.Chunk14365
import ArealUK.Chunk14366
import ArealUK.Chunk14367
import ArealUK.Chunk14368
import ArealUK.Chunk14369
import ArealUK.Chunk14370
import ArealUK.Chunk14371
import ArealUK.Chunk14372
import ArealUK.Chunk14373
import ArealUK.Chunk14374
import ArealUK.Chunk14375
import ArealUK.Chunk14376
import ArealUK.Chunk14377
import ArealUK.Chunk14378
import ArealUK.Chunk14379
import ArealUK.Chunk14380
import ArealUK.Chunk14381
import ArealUK.Chunk14382
import ArealUK.Chunk14383
import ArealUK.Chunk14384
import ArealUK.Chunk14385
import ArealUK.Chunk14386
import ArealUK.Chunk14387
import ArealUK.Chunk14388
import ArealUK.Chunk14389
import ArealUK.Chunk14390
import ArealUK.Chunk14391
import ArealUK.Chunk14392
import ArealUK.Chunk14393
import ArealUK.Chunk14394
import ArealUK.Chunk14395
import ArealUK.Chunk14396
import ArealUK.Chunk14397
import ArealUK.Chunk14398
import ArealUK.Chunk14399
import Areal.UCert.LeavesKGen

/-! Group 143 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_143 : leavesOK ctxLitU 294750000000 1 ((leaves.drop 28600).take 200) 297200000000 1 = true := by
  have s99 := ArealUCore.ArealUK.chunk_14399
  have s98 : leavesOK ctxLitU 297150000000 1 ((leaves.drop 28796).take 4) 297200000000 1 = true :=
    take_step (n := 2) (t := 4) (b := 28798) rfl rfl ArealUCore.ArealUK.chunk_14398 s99
  have s97 : leavesOK ctxLitU 297137500000 1 ((leaves.drop 28794).take 6) 297200000000 1 = true :=
    take_step (n := 2) (t := 6) (b := 28796) rfl rfl ArealUCore.ArealUK.chunk_14397 s98
  have s96 : leavesOK ctxLitU 297125000000 1 ((leaves.drop 28792).take 8) 297200000000 1 = true :=
    take_step (n := 2) (t := 8) (b := 28794) rfl rfl ArealUCore.ArealUK.chunk_14396 s97
  have s95 : leavesOK ctxLitU 148550000000 0 ((leaves.drop 28790).take 10) 297200000000 1 = true :=
    take_step (n := 2) (t := 10) (b := 28792) rfl rfl ArealUCore.ArealUK.chunk_14395 s96
  have s94 : leavesOK ctxLitU 148537500000 0 ((leaves.drop 28788).take 12) 297200000000 1 = true :=
    take_step (n := 2) (t := 12) (b := 28790) rfl rfl ArealUCore.ArealUK.chunk_14394 s95
  have s93 : leavesOK ctxLitU 297062500000 1 ((leaves.drop 28786).take 14) 297200000000 1 = true :=
    take_step (n := 2) (t := 14) (b := 28788) rfl rfl ArealUCore.ArealUK.chunk_14393 s94
  have s92 : leavesOK ctxLitU 297050000000 1 ((leaves.drop 28784).take 16) 297200000000 1 = true :=
    take_step (n := 2) (t := 16) (b := 28786) rfl rfl ArealUCore.ArealUK.chunk_14392 s93
  have s91 : leavesOK ctxLitU 297025000000 1 ((leaves.drop 28782).take 18) 297200000000 1 = true :=
    take_step (n := 2) (t := 18) (b := 28784) rfl rfl ArealUCore.ArealUK.chunk_14391 s92
  have s90 : leavesOK ctxLitU 297000000000 1 ((leaves.drop 28780).take 20) 297200000000 1 = true :=
    take_step (n := 2) (t := 20) (b := 28782) rfl rfl ArealUCore.ArealUK.chunk_14390 s91
  have s89 : leavesOK ctxLitU 296975000000 1 ((leaves.drop 28778).take 22) 297200000000 1 = true :=
    take_step (n := 2) (t := 22) (b := 28780) rfl rfl ArealUCore.ArealUK.chunk_14389 s90
  have s88 : leavesOK ctxLitU 296950000000 1 ((leaves.drop 28776).take 24) 297200000000 1 = true :=
    take_step (n := 2) (t := 24) (b := 28778) rfl rfl ArealUCore.ArealUK.chunk_14388 s89
  have s87 : leavesOK ctxLitU 148462500000 0 ((leaves.drop 28774).take 26) 297200000000 1 = true :=
    take_step (n := 2) (t := 26) (b := 28776) rfl rfl ArealUCore.ArealUK.chunk_14387 s88
  have s86 : leavesOK ctxLitU 148450000000 0 ((leaves.drop 28772).take 28) 297200000000 1 = true :=
    take_step (n := 2) (t := 28) (b := 28774) rfl rfl ArealUCore.ArealUK.chunk_14386 s87
  have s85 : leavesOK ctxLitU 148437500000 0 ((leaves.drop 28770).take 30) 297200000000 1 = true :=
    take_step (n := 2) (t := 30) (b := 28772) rfl rfl ArealUCore.ArealUK.chunk_14385 s86
  have s84 : leavesOK ctxLitU 148425000000 0 ((leaves.drop 28768).take 32) 297200000000 1 = true :=
    take_step (n := 2) (t := 32) (b := 28770) rfl rfl ArealUCore.ArealUK.chunk_14384 s85
  have s83 : leavesOK ctxLitU 296825000000 1 ((leaves.drop 28766).take 34) 297200000000 1 = true :=
    take_step (n := 2) (t := 34) (b := 28768) rfl rfl ArealUCore.ArealUK.chunk_14383 s84
  have s82 : leavesOK ctxLitU 296800000000 1 ((leaves.drop 28764).take 36) 297200000000 1 = true :=
    take_step (n := 2) (t := 36) (b := 28766) rfl rfl ArealUCore.ArealUK.chunk_14382 s83
  have s81 : leavesOK ctxLitU 593550000000 2 ((leaves.drop 28762).take 38) 297200000000 1 = true :=
    take_step (n := 2) (t := 38) (b := 28764) rfl rfl ArealUCore.ArealUK.chunk_14381 s82
  have s80 : leavesOK ctxLitU 593500000000 2 ((leaves.drop 28760).take 40) 297200000000 1 = true :=
    take_step (n := 2) (t := 40) (b := 28762) rfl rfl ArealUCore.ArealUK.chunk_14380 s81
  have s79 : leavesOK ctxLitU 593450000000 2 ((leaves.drop 28758).take 42) 297200000000 1 = true :=
    take_step (n := 2) (t := 42) (b := 28760) rfl rfl ArealUCore.ArealUK.chunk_14379 s80
  have s78 : leavesOK ctxLitU 296675000000 1 ((leaves.drop 28756).take 44) 297200000000 1 = true :=
    take_step (n := 2) (t := 44) (b := 28758) rfl rfl ArealUCore.ArealUK.chunk_14378 s79
  have s77 : leavesOK ctxLitU 593275000000 2 ((leaves.drop 28754).take 46) 297200000000 1 = true :=
    take_step (n := 2) (t := 46) (b := 28756) rfl rfl ArealUCore.ArealUK.chunk_14377 s78
  have s76 : leavesOK ctxLitU 593225000000 2 ((leaves.drop 28752).take 48) 297200000000 1 = true :=
    take_step (n := 2) (t := 48) (b := 28754) rfl rfl ArealUCore.ArealUK.chunk_14376 s77
  have s75 : leavesOK ctxLitU 593175000000 2 ((leaves.drop 28750).take 50) 297200000000 1 = true :=
    take_step (n := 2) (t := 50) (b := 28752) rfl rfl ArealUCore.ArealUK.chunk_14375 s76
  have s74 : leavesOK ctxLitU 593125000000 2 ((leaves.drop 28748).take 52) 297200000000 1 = true :=
    take_step (n := 2) (t := 52) (b := 28750) rfl rfl ArealUCore.ArealUK.chunk_14374 s75
  have s73 : leavesOK ctxLitU 296525000000 1 ((leaves.drop 28746).take 54) 297200000000 1 = true :=
    take_step (n := 2) (t := 54) (b := 28748) rfl rfl ArealUCore.ArealUK.chunk_14373 s74
  have s72 : leavesOK ctxLitU 296475000000 1 ((leaves.drop 28744).take 56) 297200000000 1 = true :=
    take_step (n := 2) (t := 56) (b := 28746) rfl rfl ArealUCore.ArealUK.chunk_14372 s73
  have s71 : leavesOK ctxLitU 592900000000 2 ((leaves.drop 28742).take 58) 297200000000 1 = true :=
    take_step (n := 2) (t := 58) (b := 28744) rfl rfl ArealUCore.ArealUK.chunk_14371 s72
  have s70 : leavesOK ctxLitU 592850000000 2 ((leaves.drop 28740).take 60) 297200000000 1 = true :=
    take_step (n := 2) (t := 60) (b := 28742) rfl rfl ArealUCore.ArealUK.chunk_14370 s71
  have s69 : leavesOK ctxLitU 592800000000 2 ((leaves.drop 28738).take 62) 297200000000 1 = true :=
    take_step (n := 2) (t := 62) (b := 28740) rfl rfl ArealUCore.ArealUK.chunk_14369 s70
  have s68 : leavesOK ctxLitU 296375000000 1 ((leaves.drop 28736).take 64) 297200000000 1 = true :=
    take_step (n := 2) (t := 64) (b := 28738) rfl rfl ArealUCore.ArealUK.chunk_14368 s69
  have s67 : leavesOK ctxLitU 296350000000 1 ((leaves.drop 28734).take 66) 297200000000 1 = true :=
    take_step (n := 2) (t := 66) (b := 28736) rfl rfl ArealUCore.ArealUK.chunk_14367 s68
  have s66 : leavesOK ctxLitU 148162500000 0 ((leaves.drop 28732).take 68) 297200000000 1 = true :=
    take_step (n := 2) (t := 68) (b := 28734) rfl rfl ArealUCore.ArealUK.chunk_14366 s67
  have s65 : leavesOK ctxLitU 148150000000 0 ((leaves.drop 28730).take 70) 297200000000 1 = true :=
    take_step (n := 2) (t := 70) (b := 28732) rfl rfl ArealUCore.ArealUK.chunk_14365 s66
  have s64 : leavesOK ctxLitU 148137500000 0 ((leaves.drop 28728).take 72) 297200000000 1 = true :=
    take_step (n := 2) (t := 72) (b := 28730) rfl rfl ArealUCore.ArealUK.chunk_14364 s65
  have s63 : leavesOK ctxLitU 148125000000 0 ((leaves.drop 28726).take 74) 297200000000 1 = true :=
    take_step (n := 2) (t := 74) (b := 28728) rfl rfl ArealUCore.ArealUK.chunk_14363 s64
  have s62 : leavesOK ctxLitU 296225000000 1 ((leaves.drop 28724).take 76) 297200000000 1 = true :=
    take_step (n := 2) (t := 76) (b := 28726) rfl rfl ArealUCore.ArealUK.chunk_14362 s63
  have s61 : leavesOK ctxLitU 296200000000 1 ((leaves.drop 28722).take 78) 297200000000 1 = true :=
    take_step (n := 2) (t := 78) (b := 28724) rfl rfl ArealUCore.ArealUK.chunk_14361 s62
  have s60 : leavesOK ctxLitU 296175000000 1 ((leaves.drop 28720).take 80) 297200000000 1 = true :=
    take_step (n := 2) (t := 80) (b := 28722) rfl rfl ArealUCore.ArealUK.chunk_14360 s61
  have s59 : leavesOK ctxLitU 296150000000 1 ((leaves.drop 28718).take 82) 297200000000 1 = true :=
    take_step (n := 2) (t := 82) (b := 28720) rfl rfl ArealUCore.ArealUK.chunk_14359 s60
  have s58 : leavesOK ctxLitU 148062500000 0 ((leaves.drop 28716).take 84) 297200000000 1 = true :=
    take_step (n := 2) (t := 84) (b := 28718) rfl rfl ArealUCore.ArealUK.chunk_14358 s59
  have s57 : leavesOK ctxLitU 148050000000 0 ((leaves.drop 28714).take 86) 297200000000 1 = true :=
    take_step (n := 2) (t := 86) (b := 28716) rfl rfl ArealUCore.ArealUK.chunk_14357 s58
  have s56 : leavesOK ctxLitU 148037500000 0 ((leaves.drop 28712).take 88) 297200000000 1 = true :=
    take_step (n := 2) (t := 88) (b := 28714) rfl rfl ArealUCore.ArealUK.chunk_14356 s57
  have s55 : leavesOK ctxLitU 296062500000 1 ((leaves.drop 28710).take 90) 297200000000 1 = true :=
    take_step (n := 2) (t := 90) (b := 28712) rfl rfl ArealUCore.ArealUK.chunk_14355 s56
  have s54 : leavesOK ctxLitU 296050000000 1 ((leaves.drop 28708).take 92) 297200000000 1 = true :=
    take_step (n := 2) (t := 92) (b := 28710) rfl rfl ArealUCore.ArealUK.chunk_14354 s55
  have s53 : leavesOK ctxLitU 296025000000 1 ((leaves.drop 28706).take 94) 297200000000 1 = true :=
    take_step (n := 2) (t := 94) (b := 28708) rfl rfl ArealUCore.ArealUK.chunk_14353 s54
  have s52 : leavesOK ctxLitU 296000000000 1 ((leaves.drop 28704).take 96) 297200000000 1 = true :=
    take_step (n := 2) (t := 96) (b := 28706) rfl rfl ArealUCore.ArealUK.chunk_14352 s53
  have s51 : leavesOK ctxLitU 295975000000 1 ((leaves.drop 28702).take 98) 297200000000 1 = true :=
    take_step (n := 2) (t := 98) (b := 28704) rfl rfl ArealUCore.ArealUK.chunk_14351 s52
  have s50 : leavesOK ctxLitU 295950000000 1 ((leaves.drop 28700).take 100) 297200000000 1 = true :=
    take_step (n := 2) (t := 100) (b := 28702) rfl rfl ArealUCore.ArealUK.chunk_14350 s51
  have s49 : leavesOK ctxLitU 147962500000 0 ((leaves.drop 28698).take 102) 297200000000 1 = true :=
    take_step (n := 2) (t := 102) (b := 28700) rfl rfl ArealUCore.ArealUK.chunk_14349 s50
  have s48 : leavesOK ctxLitU 147950000000 0 ((leaves.drop 28696).take 104) 297200000000 1 = true :=
    take_step (n := 2) (t := 104) (b := 28698) rfl rfl ArealUCore.ArealUK.chunk_14348 s49
  have s47 : leavesOK ctxLitU 147937500000 0 ((leaves.drop 28694).take 106) 297200000000 1 = true :=
    take_step (n := 2) (t := 106) (b := 28696) rfl rfl ArealUCore.ArealUK.chunk_14347 s48
  have s46 : leavesOK ctxLitU 147925000000 0 ((leaves.drop 28692).take 108) 297200000000 1 = true :=
    take_step (n := 2) (t := 108) (b := 28694) rfl rfl ArealUCore.ArealUK.chunk_14346 s47
  have s45 : leavesOK ctxLitU 295825000000 1 ((leaves.drop 28690).take 110) 297200000000 1 = true :=
    take_step (n := 2) (t := 110) (b := 28692) rfl rfl ArealUCore.ArealUK.chunk_14345 s46
  have s44 : leavesOK ctxLitU 295800000000 1 ((leaves.drop 28688).take 112) 297200000000 1 = true :=
    take_step (n := 2) (t := 112) (b := 28690) rfl rfl ArealUCore.ArealUK.chunk_14344 s45
  have s43 : leavesOK ctxLitU 295775000000 1 ((leaves.drop 28686).take 114) 297200000000 1 = true :=
    take_step (n := 2) (t := 114) (b := 28688) rfl rfl ArealUCore.ArealUK.chunk_14343 s44
  have s42 : leavesOK ctxLitU 295750000000 1 ((leaves.drop 28684).take 116) 297200000000 1 = true :=
    take_step (n := 2) (t := 116) (b := 28686) rfl rfl ArealUCore.ArealUK.chunk_14342 s43
  have s41 : leavesOK ctxLitU 147862500000 0 ((leaves.drop 28682).take 118) 297200000000 1 = true :=
    take_step (n := 2) (t := 118) (b := 28684) rfl rfl ArealUCore.ArealUK.chunk_14341 s42
  have s40 : leavesOK ctxLitU 147850000000 0 ((leaves.drop 28680).take 120) 297200000000 1 = true :=
    take_step (n := 2) (t := 120) (b := 28682) rfl rfl ArealUCore.ArealUK.chunk_14340 s41
  have s39 : leavesOK ctxLitU 147837500000 0 ((leaves.drop 28678).take 122) 297200000000 1 = true :=
    take_step (n := 2) (t := 122) (b := 28680) rfl rfl ArealUCore.ArealUK.chunk_14339 s40
  have s38 : leavesOK ctxLitU 147825000000 0 ((leaves.drop 28676).take 124) 297200000000 1 = true :=
    take_step (n := 2) (t := 124) (b := 28678) rfl rfl ArealUCore.ArealUK.chunk_14338 s39
  have s37 : leavesOK ctxLitU 295625000000 1 ((leaves.drop 28674).take 126) 297200000000 1 = true :=
    take_step (n := 2) (t := 126) (b := 28676) rfl rfl ArealUCore.ArealUK.chunk_14337 s38
  have s36 : leavesOK ctxLitU 295600000000 1 ((leaves.drop 28672).take 128) 297200000000 1 = true :=
    take_step (n := 2) (t := 128) (b := 28674) rfl rfl ArealUCore.ArealUK.chunk_14336 s37
  have s35 : leavesOK ctxLitU 295575000000 1 ((leaves.drop 28670).take 130) 297200000000 1 = true :=
    take_step (n := 2) (t := 130) (b := 28672) rfl rfl ArealUCore.ArealUK.chunk_14335 s36
  have s34 : leavesOK ctxLitU 295550000000 1 ((leaves.drop 28668).take 132) 297200000000 1 = true :=
    take_step (n := 2) (t := 132) (b := 28670) rfl rfl ArealUCore.ArealUK.chunk_14334 s35
  have s33 : leavesOK ctxLitU 295537500000 1 ((leaves.drop 28666).take 134) 297200000000 1 = true :=
    take_step (n := 2) (t := 134) (b := 28668) rfl rfl ArealUCore.ArealUK.chunk_14333 s34
  have s32 : leavesOK ctxLitU 295525000000 1 ((leaves.drop 28664).take 136) 297200000000 1 = true :=
    take_step (n := 2) (t := 136) (b := 28666) rfl rfl ArealUCore.ArealUK.chunk_14332 s33
  have s31 : leavesOK ctxLitU 147750000000 0 ((leaves.drop 28662).take 138) 297200000000 1 = true :=
    take_step (n := 2) (t := 138) (b := 28664) rfl rfl ArealUCore.ArealUK.chunk_14331 s32
  have s30 : leavesOK ctxLitU 295475000000 1 ((leaves.drop 28660).take 140) 297200000000 1 = true :=
    take_step (n := 2) (t := 140) (b := 28662) rfl rfl ArealUCore.ArealUK.chunk_14330 s31
  have s29 : leavesOK ctxLitU 295450000000 1 ((leaves.drop 28658).take 142) 297200000000 1 = true :=
    take_step (n := 2) (t := 142) (b := 28660) rfl rfl ArealUCore.ArealUK.chunk_14329 s30
  have s28 : leavesOK ctxLitU 590850000000 2 ((leaves.drop 28656).take 144) 297200000000 1 = true :=
    take_step (n := 2) (t := 144) (b := 28658) rfl rfl ArealUCore.ArealUK.chunk_14328 s29
  have s27 : leavesOK ctxLitU 590800000000 2 ((leaves.drop 28654).take 146) 297200000000 1 = true :=
    take_step (n := 2) (t := 146) (b := 28656) rfl rfl ArealUCore.ArealUK.chunk_14327 s28
  have s26 : leavesOK ctxLitU 590750000000 2 ((leaves.drop 28652).take 148) 297200000000 1 = true :=
    take_step (n := 2) (t := 148) (b := 28654) rfl rfl ArealUCore.ArealUK.chunk_14326 s27
  have s25 : leavesOK ctxLitU 590700000000 2 ((leaves.drop 28650).take 150) 297200000000 1 = true :=
    take_step (n := 2) (t := 150) (b := 28652) rfl rfl ArealUCore.ArealUK.chunk_14325 s26
  have s24 : leavesOK ctxLitU 590650000000 2 ((leaves.drop 28648).take 152) 297200000000 1 = true :=
    take_step (n := 2) (t := 152) (b := 28650) rfl rfl ArealUCore.ArealUK.chunk_14324 s25
  have s23 : leavesOK ctxLitU 590600000000 2 ((leaves.drop 28646).take 154) 297200000000 1 = true :=
    take_step (n := 2) (t := 154) (b := 28648) rfl rfl ArealUCore.ArealUK.chunk_14323 s24
  have s22 : leavesOK ctxLitU 590550000000 2 ((leaves.drop 28644).take 156) 297200000000 1 = true :=
    take_step (n := 2) (t := 156) (b := 28646) rfl rfl ArealUCore.ArealUK.chunk_14322 s23
  have s21 : leavesOK ctxLitU 590500000000 2 ((leaves.drop 28642).take 158) 297200000000 1 = true :=
    take_step (n := 2) (t := 158) (b := 28644) rfl rfl ArealUCore.ArealUK.chunk_14321 s22
  have s20 : leavesOK ctxLitU 590450000000 2 ((leaves.drop 28640).take 160) 297200000000 1 = true :=
    take_step (n := 2) (t := 160) (b := 28642) rfl rfl ArealUCore.ArealUK.chunk_14320 s21
  have s19 : leavesOK ctxLitU 590400000000 2 ((leaves.drop 28638).take 162) 297200000000 1 = true :=
    take_step (n := 2) (t := 162) (b := 28640) rfl rfl ArealUCore.ArealUK.chunk_14319 s20
  have s18 : leavesOK ctxLitU 295175000000 1 ((leaves.drop 28636).take 164) 297200000000 1 = true :=
    take_step (n := 2) (t := 164) (b := 28638) rfl rfl ArealUCore.ArealUK.chunk_14318 s19
  have s17 : leavesOK ctxLitU 295150000000 1 ((leaves.drop 28634).take 166) 297200000000 1 = true :=
    take_step (n := 2) (t := 166) (b := 28636) rfl rfl ArealUCore.ArealUK.chunk_14317 s18
  have s16 : leavesOK ctxLitU 295137500000 1 ((leaves.drop 28632).take 168) 297200000000 1 = true :=
    take_step (n := 2) (t := 168) (b := 28634) rfl rfl ArealUCore.ArealUK.chunk_14316 s17
  have s15 : leavesOK ctxLitU 295125000000 1 ((leaves.drop 28630).take 170) 297200000000 1 = true :=
    take_step (n := 2) (t := 170) (b := 28632) rfl rfl ArealUCore.ArealUK.chunk_14315 s16
  have s14 : leavesOK ctxLitU 147550000000 0 ((leaves.drop 28628).take 172) 297200000000 1 = true :=
    take_step (n := 2) (t := 172) (b := 28630) rfl rfl ArealUCore.ArealUK.chunk_14314 s15
  have s13 : leavesOK ctxLitU 147537500000 0 ((leaves.drop 28626).take 174) 297200000000 1 = true :=
    take_step (n := 2) (t := 174) (b := 28628) rfl rfl ArealUCore.ArealUK.chunk_14313 s14
  have s12 : leavesOK ctxLitU 147525000000 0 ((leaves.drop 28624).take 176) 297200000000 1 = true :=
    take_step (n := 2) (t := 176) (b := 28626) rfl rfl ArealUCore.ArealUK.chunk_14312 s13
  have s11 : leavesOK ctxLitU 295025000000 1 ((leaves.drop 28622).take 178) 297200000000 1 = true :=
    take_step (n := 2) (t := 178) (b := 28624) rfl rfl ArealUCore.ArealUK.chunk_14311 s12
  have s10 : leavesOK ctxLitU 295000000000 1 ((leaves.drop 28620).take 180) 297200000000 1 = true :=
    take_step (n := 2) (t := 180) (b := 28622) rfl rfl ArealUCore.ArealUK.chunk_14310 s11
  have s9 : leavesOK ctxLitU 294975000000 1 ((leaves.drop 28618).take 182) 297200000000 1 = true :=
    take_step (n := 2) (t := 182) (b := 28620) rfl rfl ArealUCore.ArealUK.chunk_14309 s10
  have s8 : leavesOK ctxLitU 294950000000 1 ((leaves.drop 28616).take 184) 297200000000 1 = true :=
    take_step (n := 2) (t := 184) (b := 28618) rfl rfl ArealUCore.ArealUK.chunk_14308 s9
  have s7 : leavesOK ctxLitU 147462500000 0 ((leaves.drop 28614).take 186) 297200000000 1 = true :=
    take_step (n := 2) (t := 186) (b := 28616) rfl rfl ArealUCore.ArealUK.chunk_14307 s8
  have s6 : leavesOK ctxLitU 147450000000 0 ((leaves.drop 28612).take 188) 297200000000 1 = true :=
    take_step (n := 2) (t := 188) (b := 28614) rfl rfl ArealUCore.ArealUK.chunk_14306 s7
  have s5 : leavesOK ctxLitU 147437500000 0 ((leaves.drop 28610).take 190) 297200000000 1 = true :=
    take_step (n := 2) (t := 190) (b := 28612) rfl rfl ArealUCore.ArealUK.chunk_14305 s6
  have s4 : leavesOK ctxLitU 147425000000 0 ((leaves.drop 28608).take 192) 297200000000 1 = true :=
    take_step (n := 2) (t := 192) (b := 28610) rfl rfl ArealUCore.ArealUK.chunk_14304 s5
  have s3 : leavesOK ctxLitU 294825000000 1 ((leaves.drop 28606).take 194) 297200000000 1 = true :=
    take_step (n := 2) (t := 194) (b := 28608) rfl rfl ArealUCore.ArealUK.chunk_14303 s4
  have s2 : leavesOK ctxLitU 294800000000 1 ((leaves.drop 28604).take 196) 297200000000 1 = true :=
    take_step (n := 2) (t := 196) (b := 28606) rfl rfl ArealUCore.ArealUK.chunk_14302 s3
  have s1 : leavesOK ctxLitU 294775000000 1 ((leaves.drop 28602).take 198) 297200000000 1 = true :=
    take_step (n := 2) (t := 198) (b := 28604) rfl rfl ArealUCore.ArealUK.chunk_14301 s2
  have s0 : leavesOK ctxLitU 294750000000 1 ((leaves.drop 28600).take 200) 297200000000 1 = true :=
    take_step (n := 2) (t := 200) (b := 28602) rfl rfl ArealUCore.ArealUK.chunk_14300 s1
  exact s0

end Areal.UCert

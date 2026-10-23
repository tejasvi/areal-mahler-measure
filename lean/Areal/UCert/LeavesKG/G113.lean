import ArealUK.Chunk11300
import ArealUK.Chunk11301
import ArealUK.Chunk11302
import ArealUK.Chunk11303
import ArealUK.Chunk11304
import ArealUK.Chunk11305
import ArealUK.Chunk11306
import ArealUK.Chunk11307
import ArealUK.Chunk11308
import ArealUK.Chunk11309
import ArealUK.Chunk11310
import ArealUK.Chunk11311
import ArealUK.Chunk11312
import ArealUK.Chunk11313
import ArealUK.Chunk11314
import ArealUK.Chunk11315
import ArealUK.Chunk11316
import ArealUK.Chunk11317
import ArealUK.Chunk11318
import ArealUK.Chunk11319
import ArealUK.Chunk11320
import ArealUK.Chunk11321
import ArealUK.Chunk11322
import ArealUK.Chunk11323
import ArealUK.Chunk11324
import ArealUK.Chunk11325
import ArealUK.Chunk11326
import ArealUK.Chunk11327
import ArealUK.Chunk11328
import ArealUK.Chunk11329
import ArealUK.Chunk11330
import ArealUK.Chunk11331
import ArealUK.Chunk11332
import ArealUK.Chunk11333
import ArealUK.Chunk11334
import ArealUK.Chunk11335
import ArealUK.Chunk11336
import ArealUK.Chunk11337
import ArealUK.Chunk11338
import ArealUK.Chunk11339
import ArealUK.Chunk11340
import ArealUK.Chunk11341
import ArealUK.Chunk11342
import ArealUK.Chunk11343
import ArealUK.Chunk11344
import ArealUK.Chunk11345
import ArealUK.Chunk11346
import ArealUK.Chunk11347
import ArealUK.Chunk11348
import ArealUK.Chunk11349
import ArealUK.Chunk11350
import ArealUK.Chunk11351
import ArealUK.Chunk11352
import ArealUK.Chunk11353
import ArealUK.Chunk11354
import ArealUK.Chunk11355
import ArealUK.Chunk11356
import ArealUK.Chunk11357
import ArealUK.Chunk11358
import ArealUK.Chunk11359
import ArealUK.Chunk11360
import ArealUK.Chunk11361
import ArealUK.Chunk11362
import ArealUK.Chunk11363
import ArealUK.Chunk11364
import ArealUK.Chunk11365
import ArealUK.Chunk11366
import ArealUK.Chunk11367
import ArealUK.Chunk11368
import ArealUK.Chunk11369
import ArealUK.Chunk11370
import ArealUK.Chunk11371
import ArealUK.Chunk11372
import ArealUK.Chunk11373
import ArealUK.Chunk11374
import ArealUK.Chunk11375
import ArealUK.Chunk11376
import ArealUK.Chunk11377
import ArealUK.Chunk11378
import ArealUK.Chunk11379
import ArealUK.Chunk11380
import ArealUK.Chunk11381
import ArealUK.Chunk11382
import ArealUK.Chunk11383
import ArealUK.Chunk11384
import ArealUK.Chunk11385
import ArealUK.Chunk11386
import ArealUK.Chunk11387
import ArealUK.Chunk11388
import ArealUK.Chunk11389
import ArealUK.Chunk11390
import ArealUK.Chunk11391
import ArealUK.Chunk11392
import ArealUK.Chunk11393
import ArealUK.Chunk11394
import ArealUK.Chunk11395
import ArealUK.Chunk11396
import ArealUK.Chunk11397
import ArealUK.Chunk11398
import ArealUK.Chunk11399
import Areal.UCert.LeavesKGen

/-! Group 113 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_113 : leavesOK ctxLitU 422900000000 2 ((leaves.drop 22600).take 200) 107525000000 0 = true := by
  have s99 := ArealUCore.ArealUK.chunk_11399
  have s98 : leavesOK ctxLitU 107425000000 0 ((leaves.drop 22796).take 4) 107525000000 0 = true :=
    take_step (n := 2) (t := 4) (b := 22798) rfl rfl ArealUCore.ArealUK.chunk_11398 s99
  have s97 : leavesOK ctxLitU 107375000000 0 ((leaves.drop 22794).take 6) 107525000000 0 = true :=
    take_step (n := 2) (t := 6) (b := 22796) rfl rfl ArealUCore.ArealUK.chunk_11397 s98
  have s96 : leavesOK ctxLitU 107325000000 0 ((leaves.drop 22792).take 8) 107525000000 0 = true :=
    take_step (n := 2) (t := 8) (b := 22794) rfl rfl ArealUCore.ArealUK.chunk_11396 s97
  have s95 : leavesOK ctxLitU 107275000000 0 ((leaves.drop 22790).take 10) 107525000000 0 = true :=
    take_step (n := 2) (t := 10) (b := 22792) rfl rfl ArealUCore.ArealUK.chunk_11395 s96
  have s94 : leavesOK ctxLitU 107225000000 0 ((leaves.drop 22788).take 12) 107525000000 0 = true :=
    take_step (n := 2) (t := 12) (b := 22790) rfl rfl ArealUCore.ArealUK.chunk_11394 s95
  have s93 : leavesOK ctxLitU 107175000000 0 ((leaves.drop 22786).take 14) 107525000000 0 = true :=
    take_step (n := 2) (t := 14) (b := 22788) rfl rfl ArealUCore.ArealUK.chunk_11393 s94
  have s92 : leavesOK ctxLitU 107125000000 0 ((leaves.drop 22784).take 16) 107525000000 0 = true :=
    take_step (n := 2) (t := 16) (b := 22786) rfl rfl ArealUCore.ArealUK.chunk_11392 s93
  have s91 : leavesOK ctxLitU 107075000000 0 ((leaves.drop 22782).take 18) 107525000000 0 = true :=
    take_step (n := 2) (t := 18) (b := 22784) rfl rfl ArealUCore.ArealUK.chunk_11391 s92
  have s90 : leavesOK ctxLitU 107025000000 0 ((leaves.drop 22780).take 20) 107525000000 0 = true :=
    take_step (n := 2) (t := 20) (b := 22782) rfl rfl ArealUCore.ArealUK.chunk_11390 s91
  have s89 : leavesOK ctxLitU 106975000000 0 ((leaves.drop 22778).take 22) 107525000000 0 = true :=
    take_step (n := 2) (t := 22) (b := 22780) rfl rfl ArealUCore.ArealUK.chunk_11389 s90
  have s88 : leavesOK ctxLitU 106925000000 0 ((leaves.drop 22776).take 24) 107525000000 0 = true :=
    take_step (n := 2) (t := 24) (b := 22778) rfl rfl ArealUCore.ArealUK.chunk_11388 s89
  have s87 : leavesOK ctxLitU 106875000000 0 ((leaves.drop 22774).take 26) 107525000000 0 = true :=
    take_step (n := 2) (t := 26) (b := 22776) rfl rfl ArealUCore.ArealUK.chunk_11387 s88
  have s86 : leavesOK ctxLitU 106825000000 0 ((leaves.drop 22772).take 28) 107525000000 0 = true :=
    take_step (n := 2) (t := 28) (b := 22774) rfl rfl ArealUCore.ArealUK.chunk_11386 s87
  have s85 : leavesOK ctxLitU 106775000000 0 ((leaves.drop 22770).take 30) 107525000000 0 = true :=
    take_step (n := 2) (t := 30) (b := 22772) rfl rfl ArealUCore.ArealUK.chunk_11385 s86
  have s84 : leavesOK ctxLitU 106737500000 0 ((leaves.drop 22768).take 32) 107525000000 0 = true :=
    take_step (n := 2) (t := 32) (b := 22770) rfl rfl ArealUCore.ArealUK.chunk_11384 s85
  have s83 : leavesOK ctxLitU 106718750000 0 ((leaves.drop 22766).take 34) 107525000000 0 = true :=
    take_step (n := 2) (t := 34) (b := 22768) rfl rfl ArealUCore.ArealUK.chunk_11383 s84
  have s82 : leavesOK ctxLitU 106706250000 0 ((leaves.drop 22764).take 36) 107525000000 0 = true :=
    take_step (n := 2) (t := 36) (b := 22766) rfl rfl ArealUCore.ArealUK.chunk_11382 s83
  have s81 : leavesOK ctxLitU 106693750000 0 ((leaves.drop 22762).take 38) 107525000000 0 = true :=
    take_step (n := 2) (t := 38) (b := 22764) rfl rfl ArealUCore.ArealUK.chunk_11381 s82
  have s80 : leavesOK ctxLitU 213368750000 1 ((leaves.drop 22760).take 40) 107525000000 0 = true :=
    take_step (n := 2) (t := 40) (b := 22762) rfl rfl ArealUCore.ArealUK.chunk_11380 s81
  have s79 : leavesOK ctxLitU 426718750000 2 ((leaves.drop 22758).take 42) 107525000000 0 = true :=
    take_step (n := 2) (t := 42) (b := 22760) rfl rfl ArealUCore.ArealUK.chunk_11379 s80
  have s78 : leavesOK ctxLitU 213350000000 1 ((leaves.drop 22756).take 44) 107525000000 0 = true :=
    take_step (n := 2) (t := 44) (b := 22758) rfl rfl ArealUCore.ArealUK.chunk_11378 s79
  have s77 : leavesOK ctxLitU 213331250000 1 ((leaves.drop 22754).take 46) 107525000000 0 = true :=
    take_step (n := 2) (t := 46) (b := 22756) rfl rfl ArealUCore.ArealUK.chunk_11377 s78
  have s76 : leavesOK ctxLitU 426643750000 2 ((leaves.drop 22752).take 48) 107525000000 0 = true :=
    take_step (n := 2) (t := 48) (b := 22754) rfl rfl ArealUCore.ArealUK.chunk_11376 s77
  have s75 : leavesOK ctxLitU 213312500000 1 ((leaves.drop 22750).take 50) 107525000000 0 = true :=
    take_step (n := 2) (t := 50) (b := 22752) rfl rfl ArealUCore.ArealUK.chunk_11375 s76
  have s74 : leavesOK ctxLitU 213287500000 1 ((leaves.drop 22748).take 52) 107525000000 0 = true :=
    take_step (n := 2) (t := 52) (b := 22750) rfl rfl ArealUCore.ArealUK.chunk_11374 s75
  have s73 : leavesOK ctxLitU 426537500000 2 ((leaves.drop 22746).take 54) 107525000000 0 = true :=
    take_step (n := 2) (t := 54) (b := 22748) rfl rfl ArealUCore.ArealUK.chunk_11373 s74
  have s72 : leavesOK ctxLitU 213250000000 1 ((leaves.drop 22744).take 56) 107525000000 0 = true :=
    take_step (n := 2) (t := 56) (b := 22746) rfl rfl ArealUCore.ArealUK.chunk_11372 s73
  have s71 : leavesOK ctxLitU 426450000000 2 ((leaves.drop 22742).take 58) 107525000000 0 = true :=
    take_step (n := 2) (t := 58) (b := 22744) rfl rfl ArealUCore.ArealUK.chunk_11371 s72
  have s70 : leavesOK ctxLitU 426400000000 2 ((leaves.drop 22740).take 60) 107525000000 0 = true :=
    take_step (n := 2) (t := 60) (b := 22742) rfl rfl ArealUCore.ArealUK.chunk_11370 s71
  have s69 : leavesOK ctxLitU 426350000000 2 ((leaves.drop 22738).take 62) 107525000000 0 = true :=
    take_step (n := 2) (t := 62) (b := 22740) rfl rfl ArealUCore.ArealUK.chunk_11369 s70
  have s68 : leavesOK ctxLitU 426300000000 2 ((leaves.drop 22736).take 64) 107525000000 0 = true :=
    take_step (n := 2) (t := 64) (b := 22738) rfl rfl ArealUCore.ArealUK.chunk_11368 s69
  have s67 : leavesOK ctxLitU 426250000000 2 ((leaves.drop 22734).take 66) 107525000000 0 = true :=
    take_step (n := 2) (t := 66) (b := 22736) rfl rfl ArealUCore.ArealUK.chunk_11367 s68
  have s66 : leavesOK ctxLitU 426200000000 2 ((leaves.drop 22732).take 68) 107525000000 0 = true :=
    take_step (n := 2) (t := 68) (b := 22734) rfl rfl ArealUCore.ArealUK.chunk_11366 s67
  have s65 : leavesOK ctxLitU 426150000000 2 ((leaves.drop 22730).take 70) 107525000000 0 = true :=
    take_step (n := 2) (t := 70) (b := 22732) rfl rfl ArealUCore.ArealUK.chunk_11365 s66
  have s64 : leavesOK ctxLitU 426100000000 2 ((leaves.drop 22728).take 72) 107525000000 0 = true :=
    take_step (n := 2) (t := 72) (b := 22730) rfl rfl ArealUCore.ArealUK.chunk_11364 s65
  have s63 : leavesOK ctxLitU 426050000000 2 ((leaves.drop 22726).take 74) 107525000000 0 = true :=
    take_step (n := 2) (t := 74) (b := 22728) rfl rfl ArealUCore.ArealUK.chunk_11363 s64
  have s62 : leavesOK ctxLitU 426000000000 2 ((leaves.drop 22724).take 76) 107525000000 0 = true :=
    take_step (n := 2) (t := 76) (b := 22726) rfl rfl ArealUCore.ArealUK.chunk_11362 s63
  have s61 : leavesOK ctxLitU 425950000000 2 ((leaves.drop 22722).take 78) 107525000000 0 = true :=
    take_step (n := 2) (t := 78) (b := 22724) rfl rfl ArealUCore.ArealUK.chunk_11361 s62
  have s60 : leavesOK ctxLitU 425900000000 2 ((leaves.drop 22720).take 80) 107525000000 0 = true :=
    take_step (n := 2) (t := 80) (b := 22722) rfl rfl ArealUCore.ArealUK.chunk_11360 s61
  have s59 : leavesOK ctxLitU 425850000000 2 ((leaves.drop 22718).take 82) 107525000000 0 = true :=
    take_step (n := 2) (t := 82) (b := 22720) rfl rfl ArealUCore.ArealUK.chunk_11359 s60
  have s58 : leavesOK ctxLitU 425800000000 2 ((leaves.drop 22716).take 84) 107525000000 0 = true :=
    take_step (n := 2) (t := 84) (b := 22718) rfl rfl ArealUCore.ArealUK.chunk_11358 s59
  have s57 : leavesOK ctxLitU 425750000000 2 ((leaves.drop 22714).take 86) 107525000000 0 = true :=
    take_step (n := 2) (t := 86) (b := 22716) rfl rfl ArealUCore.ArealUK.chunk_11357 s58
  have s56 : leavesOK ctxLitU 425700000000 2 ((leaves.drop 22712).take 88) 107525000000 0 = true :=
    take_step (n := 2) (t := 88) (b := 22714) rfl rfl ArealUCore.ArealUK.chunk_11356 s57
  have s55 : leavesOK ctxLitU 425650000000 2 ((leaves.drop 22710).take 90) 107525000000 0 = true :=
    take_step (n := 2) (t := 90) (b := 22712) rfl rfl ArealUCore.ArealUK.chunk_11355 s56
  have s54 : leavesOK ctxLitU 425600000000 2 ((leaves.drop 22708).take 92) 107525000000 0 = true :=
    take_step (n := 2) (t := 92) (b := 22710) rfl rfl ArealUCore.ArealUK.chunk_11354 s55
  have s53 : leavesOK ctxLitU 425550000000 2 ((leaves.drop 22706).take 94) 107525000000 0 = true :=
    take_step (n := 2) (t := 94) (b := 22708) rfl rfl ArealUCore.ArealUK.chunk_11353 s54
  have s52 : leavesOK ctxLitU 425500000000 2 ((leaves.drop 22704).take 96) 107525000000 0 = true :=
    take_step (n := 2) (t := 96) (b := 22706) rfl rfl ArealUCore.ArealUK.chunk_11352 s53
  have s51 : leavesOK ctxLitU 425450000000 2 ((leaves.drop 22702).take 98) 107525000000 0 = true :=
    take_step (n := 2) (t := 98) (b := 22704) rfl rfl ArealUCore.ArealUK.chunk_11351 s52
  have s50 : leavesOK ctxLitU 425400000000 2 ((leaves.drop 22700).take 100) 107525000000 0 = true :=
    take_step (n := 2) (t := 100) (b := 22702) rfl rfl ArealUCore.ArealUK.chunk_11350 s51
  have s49 : leavesOK ctxLitU 425350000000 2 ((leaves.drop 22698).take 102) 107525000000 0 = true :=
    take_step (n := 2) (t := 102) (b := 22700) rfl rfl ArealUCore.ArealUK.chunk_11349 s50
  have s48 : leavesOK ctxLitU 425300000000 2 ((leaves.drop 22696).take 104) 107525000000 0 = true :=
    take_step (n := 2) (t := 104) (b := 22698) rfl rfl ArealUCore.ArealUK.chunk_11348 s49
  have s47 : leavesOK ctxLitU 425250000000 2 ((leaves.drop 22694).take 106) 107525000000 0 = true :=
    take_step (n := 2) (t := 106) (b := 22696) rfl rfl ArealUCore.ArealUK.chunk_11347 s48
  have s46 : leavesOK ctxLitU 425200000000 2 ((leaves.drop 22692).take 108) 107525000000 0 = true :=
    take_step (n := 2) (t := 108) (b := 22694) rfl rfl ArealUCore.ArealUK.chunk_11346 s47
  have s45 : leavesOK ctxLitU 425150000000 2 ((leaves.drop 22690).take 110) 107525000000 0 = true :=
    take_step (n := 2) (t := 110) (b := 22692) rfl rfl ArealUCore.ArealUK.chunk_11345 s46
  have s44 : leavesOK ctxLitU 425100000000 2 ((leaves.drop 22688).take 112) 107525000000 0 = true :=
    take_step (n := 2) (t := 112) (b := 22690) rfl rfl ArealUCore.ArealUK.chunk_11344 s45
  have s43 : leavesOK ctxLitU 425050000000 2 ((leaves.drop 22686).take 114) 107525000000 0 = true :=
    take_step (n := 2) (t := 114) (b := 22688) rfl rfl ArealUCore.ArealUK.chunk_11343 s44
  have s42 : leavesOK ctxLitU 425000000000 2 ((leaves.drop 22684).take 116) 107525000000 0 = true :=
    take_step (n := 2) (t := 116) (b := 22686) rfl rfl ArealUCore.ArealUK.chunk_11342 s43
  have s41 : leavesOK ctxLitU 424950000000 2 ((leaves.drop 22682).take 118) 107525000000 0 = true :=
    take_step (n := 2) (t := 118) (b := 22684) rfl rfl ArealUCore.ArealUK.chunk_11341 s42
  have s40 : leavesOK ctxLitU 424900000000 2 ((leaves.drop 22680).take 120) 107525000000 0 = true :=
    take_step (n := 2) (t := 120) (b := 22682) rfl rfl ArealUCore.ArealUK.chunk_11340 s41
  have s39 : leavesOK ctxLitU 424850000000 2 ((leaves.drop 22678).take 122) 107525000000 0 = true :=
    take_step (n := 2) (t := 122) (b := 22680) rfl rfl ArealUCore.ArealUK.chunk_11339 s40
  have s38 : leavesOK ctxLitU 424800000000 2 ((leaves.drop 22676).take 124) 107525000000 0 = true :=
    take_step (n := 2) (t := 124) (b := 22678) rfl rfl ArealUCore.ArealUK.chunk_11338 s39
  have s37 : leavesOK ctxLitU 424750000000 2 ((leaves.drop 22674).take 126) 107525000000 0 = true :=
    take_step (n := 2) (t := 126) (b := 22676) rfl rfl ArealUCore.ArealUK.chunk_11337 s38
  have s36 : leavesOK ctxLitU 424700000000 2 ((leaves.drop 22672).take 128) 107525000000 0 = true :=
    take_step (n := 2) (t := 128) (b := 22674) rfl rfl ArealUCore.ArealUK.chunk_11336 s37
  have s35 : leavesOK ctxLitU 424650000000 2 ((leaves.drop 22670).take 130) 107525000000 0 = true :=
    take_step (n := 2) (t := 130) (b := 22672) rfl rfl ArealUCore.ArealUK.chunk_11335 s36
  have s34 : leavesOK ctxLitU 424600000000 2 ((leaves.drop 22668).take 132) 107525000000 0 = true :=
    take_step (n := 2) (t := 132) (b := 22670) rfl rfl ArealUCore.ArealUK.chunk_11334 s35
  have s33 : leavesOK ctxLitU 424550000000 2 ((leaves.drop 22666).take 134) 107525000000 0 = true :=
    take_step (n := 2) (t := 134) (b := 22668) rfl rfl ArealUCore.ArealUK.chunk_11333 s34
  have s32 : leavesOK ctxLitU 424500000000 2 ((leaves.drop 22664).take 136) 107525000000 0 = true :=
    take_step (n := 2) (t := 136) (b := 22666) rfl rfl ArealUCore.ArealUK.chunk_11332 s33
  have s31 : leavesOK ctxLitU 424450000000 2 ((leaves.drop 22662).take 138) 107525000000 0 = true :=
    take_step (n := 2) (t := 138) (b := 22664) rfl rfl ArealUCore.ArealUK.chunk_11331 s32
  have s30 : leavesOK ctxLitU 424400000000 2 ((leaves.drop 22660).take 140) 107525000000 0 = true :=
    take_step (n := 2) (t := 140) (b := 22662) rfl rfl ArealUCore.ArealUK.chunk_11330 s31
  have s29 : leavesOK ctxLitU 424350000000 2 ((leaves.drop 22658).take 142) 107525000000 0 = true :=
    take_step (n := 2) (t := 142) (b := 22660) rfl rfl ArealUCore.ArealUK.chunk_11329 s30
  have s28 : leavesOK ctxLitU 424300000000 2 ((leaves.drop 22656).take 144) 107525000000 0 = true :=
    take_step (n := 2) (t := 144) (b := 22658) rfl rfl ArealUCore.ArealUK.chunk_11328 s29
  have s27 : leavesOK ctxLitU 424250000000 2 ((leaves.drop 22654).take 146) 107525000000 0 = true :=
    take_step (n := 2) (t := 146) (b := 22656) rfl rfl ArealUCore.ArealUK.chunk_11327 s28
  have s26 : leavesOK ctxLitU 424200000000 2 ((leaves.drop 22652).take 148) 107525000000 0 = true :=
    take_step (n := 2) (t := 148) (b := 22654) rfl rfl ArealUCore.ArealUK.chunk_11326 s27
  have s25 : leavesOK ctxLitU 424150000000 2 ((leaves.drop 22650).take 150) 107525000000 0 = true :=
    take_step (n := 2) (t := 150) (b := 22652) rfl rfl ArealUCore.ArealUK.chunk_11325 s26
  have s24 : leavesOK ctxLitU 424100000000 2 ((leaves.drop 22648).take 152) 107525000000 0 = true :=
    take_step (n := 2) (t := 152) (b := 22650) rfl rfl ArealUCore.ArealUK.chunk_11324 s25
  have s23 : leavesOK ctxLitU 424050000000 2 ((leaves.drop 22646).take 154) 107525000000 0 = true :=
    take_step (n := 2) (t := 154) (b := 22648) rfl rfl ArealUCore.ArealUK.chunk_11323 s24
  have s22 : leavesOK ctxLitU 424000000000 2 ((leaves.drop 22644).take 156) 107525000000 0 = true :=
    take_step (n := 2) (t := 156) (b := 22646) rfl rfl ArealUCore.ArealUK.chunk_11322 s23
  have s21 : leavesOK ctxLitU 423950000000 2 ((leaves.drop 22642).take 158) 107525000000 0 = true :=
    take_step (n := 2) (t := 158) (b := 22644) rfl rfl ArealUCore.ArealUK.chunk_11321 s22
  have s20 : leavesOK ctxLitU 423900000000 2 ((leaves.drop 22640).take 160) 107525000000 0 = true :=
    take_step (n := 2) (t := 160) (b := 22642) rfl rfl ArealUCore.ArealUK.chunk_11320 s21
  have s19 : leavesOK ctxLitU 423850000000 2 ((leaves.drop 22638).take 162) 107525000000 0 = true :=
    take_step (n := 2) (t := 162) (b := 22640) rfl rfl ArealUCore.ArealUK.chunk_11319 s20
  have s18 : leavesOK ctxLitU 423800000000 2 ((leaves.drop 22636).take 164) 107525000000 0 = true :=
    take_step (n := 2) (t := 164) (b := 22638) rfl rfl ArealUCore.ArealUK.chunk_11318 s19
  have s17 : leavesOK ctxLitU 423750000000 2 ((leaves.drop 22634).take 166) 107525000000 0 = true :=
    take_step (n := 2) (t := 166) (b := 22636) rfl rfl ArealUCore.ArealUK.chunk_11317 s18
  have s16 : leavesOK ctxLitU 423700000000 2 ((leaves.drop 22632).take 168) 107525000000 0 = true :=
    take_step (n := 2) (t := 168) (b := 22634) rfl rfl ArealUCore.ArealUK.chunk_11316 s17
  have s15 : leavesOK ctxLitU 423650000000 2 ((leaves.drop 22630).take 170) 107525000000 0 = true :=
    take_step (n := 2) (t := 170) (b := 22632) rfl rfl ArealUCore.ArealUK.chunk_11315 s16
  have s14 : leavesOK ctxLitU 423600000000 2 ((leaves.drop 22628).take 172) 107525000000 0 = true :=
    take_step (n := 2) (t := 172) (b := 22630) rfl rfl ArealUCore.ArealUK.chunk_11314 s15
  have s13 : leavesOK ctxLitU 423550000000 2 ((leaves.drop 22626).take 174) 107525000000 0 = true :=
    take_step (n := 2) (t := 174) (b := 22628) rfl rfl ArealUCore.ArealUK.chunk_11313 s14
  have s12 : leavesOK ctxLitU 423500000000 2 ((leaves.drop 22624).take 176) 107525000000 0 = true :=
    take_step (n := 2) (t := 176) (b := 22626) rfl rfl ArealUCore.ArealUK.chunk_11312 s13
  have s11 : leavesOK ctxLitU 423450000000 2 ((leaves.drop 22622).take 178) 107525000000 0 = true :=
    take_step (n := 2) (t := 178) (b := 22624) rfl rfl ArealUCore.ArealUK.chunk_11311 s12
  have s10 : leavesOK ctxLitU 423400000000 2 ((leaves.drop 22620).take 180) 107525000000 0 = true :=
    take_step (n := 2) (t := 180) (b := 22622) rfl rfl ArealUCore.ArealUK.chunk_11310 s11
  have s9 : leavesOK ctxLitU 423350000000 2 ((leaves.drop 22618).take 182) 107525000000 0 = true :=
    take_step (n := 2) (t := 182) (b := 22620) rfl rfl ArealUCore.ArealUK.chunk_11309 s10
  have s8 : leavesOK ctxLitU 423300000000 2 ((leaves.drop 22616).take 184) 107525000000 0 = true :=
    take_step (n := 2) (t := 184) (b := 22618) rfl rfl ArealUCore.ArealUK.chunk_11308 s9
  have s7 : leavesOK ctxLitU 423250000000 2 ((leaves.drop 22614).take 186) 107525000000 0 = true :=
    take_step (n := 2) (t := 186) (b := 22616) rfl rfl ArealUCore.ArealUK.chunk_11307 s8
  have s6 : leavesOK ctxLitU 423200000000 2 ((leaves.drop 22612).take 188) 107525000000 0 = true :=
    take_step (n := 2) (t := 188) (b := 22614) rfl rfl ArealUCore.ArealUK.chunk_11306 s7
  have s5 : leavesOK ctxLitU 423150000000 2 ((leaves.drop 22610).take 190) 107525000000 0 = true :=
    take_step (n := 2) (t := 190) (b := 22612) rfl rfl ArealUCore.ArealUK.chunk_11305 s6
  have s4 : leavesOK ctxLitU 423100000000 2 ((leaves.drop 22608).take 192) 107525000000 0 = true :=
    take_step (n := 2) (t := 192) (b := 22610) rfl rfl ArealUCore.ArealUK.chunk_11304 s5
  have s3 : leavesOK ctxLitU 423050000000 2 ((leaves.drop 22606).take 194) 107525000000 0 = true :=
    take_step (n := 2) (t := 194) (b := 22608) rfl rfl ArealUCore.ArealUK.chunk_11303 s4
  have s2 : leavesOK ctxLitU 423000000000 2 ((leaves.drop 22604).take 196) 107525000000 0 = true :=
    take_step (n := 2) (t := 196) (b := 22606) rfl rfl ArealUCore.ArealUK.chunk_11302 s3
  have s1 : leavesOK ctxLitU 422950000000 2 ((leaves.drop 22602).take 198) 107525000000 0 = true :=
    take_step (n := 2) (t := 198) (b := 22604) rfl rfl ArealUCore.ArealUK.chunk_11301 s2
  have s0 : leavesOK ctxLitU 422900000000 2 ((leaves.drop 22600).take 200) 107525000000 0 = true :=
    take_step (n := 2) (t := 200) (b := 22602) rfl rfl ArealUCore.ArealUK.chunk_11300 s1
  exact s0

end Areal.UCert

import ArealUK.Chunk10300
import ArealUK.Chunk10301
import ArealUK.Chunk10302
import ArealUK.Chunk10303
import ArealUK.Chunk10304
import ArealUK.Chunk10305
import ArealUK.Chunk10306
import ArealUK.Chunk10307
import ArealUK.Chunk10308
import ArealUK.Chunk10309
import ArealUK.Chunk10310
import ArealUK.Chunk10311
import ArealUK.Chunk10312
import ArealUK.Chunk10313
import ArealUK.Chunk10314
import ArealUK.Chunk10315
import ArealUK.Chunk10316
import ArealUK.Chunk10317
import ArealUK.Chunk10318
import ArealUK.Chunk10319
import ArealUK.Chunk10320
import ArealUK.Chunk10321
import ArealUK.Chunk10322
import ArealUK.Chunk10323
import ArealUK.Chunk10324
import ArealUK.Chunk10325
import ArealUK.Chunk10326
import ArealUK.Chunk10327
import ArealUK.Chunk10328
import ArealUK.Chunk10329
import ArealUK.Chunk10330
import ArealUK.Chunk10331
import ArealUK.Chunk10332
import ArealUK.Chunk10333
import ArealUK.Chunk10334
import ArealUK.Chunk10335
import ArealUK.Chunk10336
import ArealUK.Chunk10337
import ArealUK.Chunk10338
import ArealUK.Chunk10339
import ArealUK.Chunk10340
import ArealUK.Chunk10341
import ArealUK.Chunk10342
import ArealUK.Chunk10343
import ArealUK.Chunk10344
import ArealUK.Chunk10345
import ArealUK.Chunk10346
import ArealUK.Chunk10347
import ArealUK.Chunk10348
import ArealUK.Chunk10349
import ArealUK.Chunk10350
import ArealUK.Chunk10351
import ArealUK.Chunk10352
import ArealUK.Chunk10353
import ArealUK.Chunk10354
import ArealUK.Chunk10355
import ArealUK.Chunk10356
import ArealUK.Chunk10357
import ArealUK.Chunk10358
import ArealUK.Chunk10359
import ArealUK.Chunk10360
import ArealUK.Chunk10361
import ArealUK.Chunk10362
import ArealUK.Chunk10363
import ArealUK.Chunk10364
import ArealUK.Chunk10365
import ArealUK.Chunk10366
import ArealUK.Chunk10367
import ArealUK.Chunk10368
import ArealUK.Chunk10369
import ArealUK.Chunk10370
import ArealUK.Chunk10371
import ArealUK.Chunk10372
import ArealUK.Chunk10373
import ArealUK.Chunk10374
import ArealUK.Chunk10375
import ArealUK.Chunk10376
import ArealUK.Chunk10377
import ArealUK.Chunk10378
import ArealUK.Chunk10379
import ArealUK.Chunk10380
import ArealUK.Chunk10381
import ArealUK.Chunk10382
import ArealUK.Chunk10383
import ArealUK.Chunk10384
import ArealUK.Chunk10385
import ArealUK.Chunk10386
import ArealUK.Chunk10387
import ArealUK.Chunk10388
import ArealUK.Chunk10389
import ArealUK.Chunk10390
import ArealUK.Chunk10391
import ArealUK.Chunk10392
import ArealUK.Chunk10393
import ArealUK.Chunk10394
import ArealUK.Chunk10395
import ArealUK.Chunk10396
import ArealUK.Chunk10397
import ArealUK.Chunk10398
import ArealUK.Chunk10399
import Areal.UCert.LeavesKGen

/-! Group 103 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_103 : leavesOK ctxLitU 372150000000 2 ((leaves.drop 20600).take 200) 377150000000 2 = true := by
  have s99 := ArealUCore.ArealUK.chunk_10399
  have s98 : leavesOK ctxLitU 377050000000 2 ((leaves.drop 20796).take 4) 377150000000 2 = true :=
    take_step (n := 2) (t := 4) (b := 20798) rfl rfl ArealUCore.ArealUK.chunk_10398 s99
  have s97 : leavesOK ctxLitU 377000000000 2 ((leaves.drop 20794).take 6) 377150000000 2 = true :=
    take_step (n := 2) (t := 6) (b := 20796) rfl rfl ArealUCore.ArealUK.chunk_10397 s98
  have s96 : leavesOK ctxLitU 376950000000 2 ((leaves.drop 20792).take 8) 377150000000 2 = true :=
    take_step (n := 2) (t := 8) (b := 20794) rfl rfl ArealUCore.ArealUK.chunk_10396 s97
  have s95 : leavesOK ctxLitU 376900000000 2 ((leaves.drop 20790).take 10) 377150000000 2 = true :=
    take_step (n := 2) (t := 10) (b := 20792) rfl rfl ArealUCore.ArealUK.chunk_10395 s96
  have s94 : leavesOK ctxLitU 376850000000 2 ((leaves.drop 20788).take 12) 377150000000 2 = true :=
    take_step (n := 2) (t := 12) (b := 20790) rfl rfl ArealUCore.ArealUK.chunk_10394 s95
  have s93 : leavesOK ctxLitU 376800000000 2 ((leaves.drop 20786).take 14) 377150000000 2 = true :=
    take_step (n := 2) (t := 14) (b := 20788) rfl rfl ArealUCore.ArealUK.chunk_10393 s94
  have s92 : leavesOK ctxLitU 376750000000 2 ((leaves.drop 20784).take 16) 377150000000 2 = true :=
    take_step (n := 2) (t := 16) (b := 20786) rfl rfl ArealUCore.ArealUK.chunk_10392 s93
  have s91 : leavesOK ctxLitU 376700000000 2 ((leaves.drop 20782).take 18) 377150000000 2 = true :=
    take_step (n := 2) (t := 18) (b := 20784) rfl rfl ArealUCore.ArealUK.chunk_10391 s92
  have s90 : leavesOK ctxLitU 376650000000 2 ((leaves.drop 20780).take 20) 377150000000 2 = true :=
    take_step (n := 2) (t := 20) (b := 20782) rfl rfl ArealUCore.ArealUK.chunk_10390 s91
  have s89 : leavesOK ctxLitU 376600000000 2 ((leaves.drop 20778).take 22) 377150000000 2 = true :=
    take_step (n := 2) (t := 22) (b := 20780) rfl rfl ArealUCore.ArealUK.chunk_10389 s90
  have s88 : leavesOK ctxLitU 376550000000 2 ((leaves.drop 20776).take 24) 377150000000 2 = true :=
    take_step (n := 2) (t := 24) (b := 20778) rfl rfl ArealUCore.ArealUK.chunk_10388 s89
  have s87 : leavesOK ctxLitU 376500000000 2 ((leaves.drop 20774).take 26) 377150000000 2 = true :=
    take_step (n := 2) (t := 26) (b := 20776) rfl rfl ArealUCore.ArealUK.chunk_10387 s88
  have s86 : leavesOK ctxLitU 376450000000 2 ((leaves.drop 20772).take 28) 377150000000 2 = true :=
    take_step (n := 2) (t := 28) (b := 20774) rfl rfl ArealUCore.ArealUK.chunk_10386 s87
  have s85 : leavesOK ctxLitU 376400000000 2 ((leaves.drop 20770).take 30) 377150000000 2 = true :=
    take_step (n := 2) (t := 30) (b := 20772) rfl rfl ArealUCore.ArealUK.chunk_10385 s86
  have s84 : leavesOK ctxLitU 376350000000 2 ((leaves.drop 20768).take 32) 377150000000 2 = true :=
    take_step (n := 2) (t := 32) (b := 20770) rfl rfl ArealUCore.ArealUK.chunk_10384 s85
  have s83 : leavesOK ctxLitU 376300000000 2 ((leaves.drop 20766).take 34) 377150000000 2 = true :=
    take_step (n := 2) (t := 34) (b := 20768) rfl rfl ArealUCore.ArealUK.chunk_10383 s84
  have s82 : leavesOK ctxLitU 376250000000 2 ((leaves.drop 20764).take 36) 377150000000 2 = true :=
    take_step (n := 2) (t := 36) (b := 20766) rfl rfl ArealUCore.ArealUK.chunk_10382 s83
  have s81 : leavesOK ctxLitU 376200000000 2 ((leaves.drop 20762).take 38) 377150000000 2 = true :=
    take_step (n := 2) (t := 38) (b := 20764) rfl rfl ArealUCore.ArealUK.chunk_10381 s82
  have s80 : leavesOK ctxLitU 376150000000 2 ((leaves.drop 20760).take 40) 377150000000 2 = true :=
    take_step (n := 2) (t := 40) (b := 20762) rfl rfl ArealUCore.ArealUK.chunk_10380 s81
  have s79 : leavesOK ctxLitU 376100000000 2 ((leaves.drop 20758).take 42) 377150000000 2 = true :=
    take_step (n := 2) (t := 42) (b := 20760) rfl rfl ArealUCore.ArealUK.chunk_10379 s80
  have s78 : leavesOK ctxLitU 376050000000 2 ((leaves.drop 20756).take 44) 377150000000 2 = true :=
    take_step (n := 2) (t := 44) (b := 20758) rfl rfl ArealUCore.ArealUK.chunk_10378 s79
  have s77 : leavesOK ctxLitU 376000000000 2 ((leaves.drop 20754).take 46) 377150000000 2 = true :=
    take_step (n := 2) (t := 46) (b := 20756) rfl rfl ArealUCore.ArealUK.chunk_10377 s78
  have s76 : leavesOK ctxLitU 375950000000 2 ((leaves.drop 20752).take 48) 377150000000 2 = true :=
    take_step (n := 2) (t := 48) (b := 20754) rfl rfl ArealUCore.ArealUK.chunk_10376 s77
  have s75 : leavesOK ctxLitU 375900000000 2 ((leaves.drop 20750).take 50) 377150000000 2 = true :=
    take_step (n := 2) (t := 50) (b := 20752) rfl rfl ArealUCore.ArealUK.chunk_10375 s76
  have s74 : leavesOK ctxLitU 375850000000 2 ((leaves.drop 20748).take 52) 377150000000 2 = true :=
    take_step (n := 2) (t := 52) (b := 20750) rfl rfl ArealUCore.ArealUK.chunk_10374 s75
  have s73 : leavesOK ctxLitU 375800000000 2 ((leaves.drop 20746).take 54) 377150000000 2 = true :=
    take_step (n := 2) (t := 54) (b := 20748) rfl rfl ArealUCore.ArealUK.chunk_10373 s74
  have s72 : leavesOK ctxLitU 375750000000 2 ((leaves.drop 20744).take 56) 377150000000 2 = true :=
    take_step (n := 2) (t := 56) (b := 20746) rfl rfl ArealUCore.ArealUK.chunk_10372 s73
  have s71 : leavesOK ctxLitU 375700000000 2 ((leaves.drop 20742).take 58) 377150000000 2 = true :=
    take_step (n := 2) (t := 58) (b := 20744) rfl rfl ArealUCore.ArealUK.chunk_10371 s72
  have s70 : leavesOK ctxLitU 375650000000 2 ((leaves.drop 20740).take 60) 377150000000 2 = true :=
    take_step (n := 2) (t := 60) (b := 20742) rfl rfl ArealUCore.ArealUK.chunk_10370 s71
  have s69 : leavesOK ctxLitU 375600000000 2 ((leaves.drop 20738).take 62) 377150000000 2 = true :=
    take_step (n := 2) (t := 62) (b := 20740) rfl rfl ArealUCore.ArealUK.chunk_10369 s70
  have s68 : leavesOK ctxLitU 375550000000 2 ((leaves.drop 20736).take 64) 377150000000 2 = true :=
    take_step (n := 2) (t := 64) (b := 20738) rfl rfl ArealUCore.ArealUK.chunk_10368 s69
  have s67 : leavesOK ctxLitU 375500000000 2 ((leaves.drop 20734).take 66) 377150000000 2 = true :=
    take_step (n := 2) (t := 66) (b := 20736) rfl rfl ArealUCore.ArealUK.chunk_10367 s68
  have s66 : leavesOK ctxLitU 375450000000 2 ((leaves.drop 20732).take 68) 377150000000 2 = true :=
    take_step (n := 2) (t := 68) (b := 20734) rfl rfl ArealUCore.ArealUK.chunk_10366 s67
  have s65 : leavesOK ctxLitU 375400000000 2 ((leaves.drop 20730).take 70) 377150000000 2 = true :=
    take_step (n := 2) (t := 70) (b := 20732) rfl rfl ArealUCore.ArealUK.chunk_10365 s66
  have s64 : leavesOK ctxLitU 375350000000 2 ((leaves.drop 20728).take 72) 377150000000 2 = true :=
    take_step (n := 2) (t := 72) (b := 20730) rfl rfl ArealUCore.ArealUK.chunk_10364 s65
  have s63 : leavesOK ctxLitU 375300000000 2 ((leaves.drop 20726).take 74) 377150000000 2 = true :=
    take_step (n := 2) (t := 74) (b := 20728) rfl rfl ArealUCore.ArealUK.chunk_10363 s64
  have s62 : leavesOK ctxLitU 375250000000 2 ((leaves.drop 20724).take 76) 377150000000 2 = true :=
    take_step (n := 2) (t := 76) (b := 20726) rfl rfl ArealUCore.ArealUK.chunk_10362 s63
  have s61 : leavesOK ctxLitU 375200000000 2 ((leaves.drop 20722).take 78) 377150000000 2 = true :=
    take_step (n := 2) (t := 78) (b := 20724) rfl rfl ArealUCore.ArealUK.chunk_10361 s62
  have s60 : leavesOK ctxLitU 375150000000 2 ((leaves.drop 20720).take 80) 377150000000 2 = true :=
    take_step (n := 2) (t := 80) (b := 20722) rfl rfl ArealUCore.ArealUK.chunk_10360 s61
  have s59 : leavesOK ctxLitU 375100000000 2 ((leaves.drop 20718).take 82) 377150000000 2 = true :=
    take_step (n := 2) (t := 82) (b := 20720) rfl rfl ArealUCore.ArealUK.chunk_10359 s60
  have s58 : leavesOK ctxLitU 375050000000 2 ((leaves.drop 20716).take 84) 377150000000 2 = true :=
    take_step (n := 2) (t := 84) (b := 20718) rfl rfl ArealUCore.ArealUK.chunk_10358 s59
  have s57 : leavesOK ctxLitU 375000000000 2 ((leaves.drop 20714).take 86) 377150000000 2 = true :=
    take_step (n := 2) (t := 86) (b := 20716) rfl rfl ArealUCore.ArealUK.chunk_10357 s58
  have s56 : leavesOK ctxLitU 374950000000 2 ((leaves.drop 20712).take 88) 377150000000 2 = true :=
    take_step (n := 2) (t := 88) (b := 20714) rfl rfl ArealUCore.ArealUK.chunk_10356 s57
  have s55 : leavesOK ctxLitU 374900000000 2 ((leaves.drop 20710).take 90) 377150000000 2 = true :=
    take_step (n := 2) (t := 90) (b := 20712) rfl rfl ArealUCore.ArealUK.chunk_10355 s56
  have s54 : leavesOK ctxLitU 374850000000 2 ((leaves.drop 20708).take 92) 377150000000 2 = true :=
    take_step (n := 2) (t := 92) (b := 20710) rfl rfl ArealUCore.ArealUK.chunk_10354 s55
  have s53 : leavesOK ctxLitU 374800000000 2 ((leaves.drop 20706).take 94) 377150000000 2 = true :=
    take_step (n := 2) (t := 94) (b := 20708) rfl rfl ArealUCore.ArealUK.chunk_10353 s54
  have s52 : leavesOK ctxLitU 374750000000 2 ((leaves.drop 20704).take 96) 377150000000 2 = true :=
    take_step (n := 2) (t := 96) (b := 20706) rfl rfl ArealUCore.ArealUK.chunk_10352 s53
  have s51 : leavesOK ctxLitU 374700000000 2 ((leaves.drop 20702).take 98) 377150000000 2 = true :=
    take_step (n := 2) (t := 98) (b := 20704) rfl rfl ArealUCore.ArealUK.chunk_10351 s52
  have s50 : leavesOK ctxLitU 374650000000 2 ((leaves.drop 20700).take 100) 377150000000 2 = true :=
    take_step (n := 2) (t := 100) (b := 20702) rfl rfl ArealUCore.ArealUK.chunk_10350 s51
  have s49 : leavesOK ctxLitU 374600000000 2 ((leaves.drop 20698).take 102) 377150000000 2 = true :=
    take_step (n := 2) (t := 102) (b := 20700) rfl rfl ArealUCore.ArealUK.chunk_10349 s50
  have s48 : leavesOK ctxLitU 374550000000 2 ((leaves.drop 20696).take 104) 377150000000 2 = true :=
    take_step (n := 2) (t := 104) (b := 20698) rfl rfl ArealUCore.ArealUK.chunk_10348 s49
  have s47 : leavesOK ctxLitU 374500000000 2 ((leaves.drop 20694).take 106) 377150000000 2 = true :=
    take_step (n := 2) (t := 106) (b := 20696) rfl rfl ArealUCore.ArealUK.chunk_10347 s48
  have s46 : leavesOK ctxLitU 374450000000 2 ((leaves.drop 20692).take 108) 377150000000 2 = true :=
    take_step (n := 2) (t := 108) (b := 20694) rfl rfl ArealUCore.ArealUK.chunk_10346 s47
  have s45 : leavesOK ctxLitU 374400000000 2 ((leaves.drop 20690).take 110) 377150000000 2 = true :=
    take_step (n := 2) (t := 110) (b := 20692) rfl rfl ArealUCore.ArealUK.chunk_10345 s46
  have s44 : leavesOK ctxLitU 374350000000 2 ((leaves.drop 20688).take 112) 377150000000 2 = true :=
    take_step (n := 2) (t := 112) (b := 20690) rfl rfl ArealUCore.ArealUK.chunk_10344 s45
  have s43 : leavesOK ctxLitU 374300000000 2 ((leaves.drop 20686).take 114) 377150000000 2 = true :=
    take_step (n := 2) (t := 114) (b := 20688) rfl rfl ArealUCore.ArealUK.chunk_10343 s44
  have s42 : leavesOK ctxLitU 374250000000 2 ((leaves.drop 20684).take 116) 377150000000 2 = true :=
    take_step (n := 2) (t := 116) (b := 20686) rfl rfl ArealUCore.ArealUK.chunk_10342 s43
  have s41 : leavesOK ctxLitU 374200000000 2 ((leaves.drop 20682).take 118) 377150000000 2 = true :=
    take_step (n := 2) (t := 118) (b := 20684) rfl rfl ArealUCore.ArealUK.chunk_10341 s42
  have s40 : leavesOK ctxLitU 374150000000 2 ((leaves.drop 20680).take 120) 377150000000 2 = true :=
    take_step (n := 2) (t := 120) (b := 20682) rfl rfl ArealUCore.ArealUK.chunk_10340 s41
  have s39 : leavesOK ctxLitU 374100000000 2 ((leaves.drop 20678).take 122) 377150000000 2 = true :=
    take_step (n := 2) (t := 122) (b := 20680) rfl rfl ArealUCore.ArealUK.chunk_10339 s40
  have s38 : leavesOK ctxLitU 374050000000 2 ((leaves.drop 20676).take 124) 377150000000 2 = true :=
    take_step (n := 2) (t := 124) (b := 20678) rfl rfl ArealUCore.ArealUK.chunk_10338 s39
  have s37 : leavesOK ctxLitU 374000000000 2 ((leaves.drop 20674).take 126) 377150000000 2 = true :=
    take_step (n := 2) (t := 126) (b := 20676) rfl rfl ArealUCore.ArealUK.chunk_10337 s38
  have s36 : leavesOK ctxLitU 373950000000 2 ((leaves.drop 20672).take 128) 377150000000 2 = true :=
    take_step (n := 2) (t := 128) (b := 20674) rfl rfl ArealUCore.ArealUK.chunk_10336 s37
  have s35 : leavesOK ctxLitU 373900000000 2 ((leaves.drop 20670).take 130) 377150000000 2 = true :=
    take_step (n := 2) (t := 130) (b := 20672) rfl rfl ArealUCore.ArealUK.chunk_10335 s36
  have s34 : leavesOK ctxLitU 373850000000 2 ((leaves.drop 20668).take 132) 377150000000 2 = true :=
    take_step (n := 2) (t := 132) (b := 20670) rfl rfl ArealUCore.ArealUK.chunk_10334 s35
  have s33 : leavesOK ctxLitU 373800000000 2 ((leaves.drop 20666).take 134) 377150000000 2 = true :=
    take_step (n := 2) (t := 134) (b := 20668) rfl rfl ArealUCore.ArealUK.chunk_10333 s34
  have s32 : leavesOK ctxLitU 373750000000 2 ((leaves.drop 20664).take 136) 377150000000 2 = true :=
    take_step (n := 2) (t := 136) (b := 20666) rfl rfl ArealUCore.ArealUK.chunk_10332 s33
  have s31 : leavesOK ctxLitU 373700000000 2 ((leaves.drop 20662).take 138) 377150000000 2 = true :=
    take_step (n := 2) (t := 138) (b := 20664) rfl rfl ArealUCore.ArealUK.chunk_10331 s32
  have s30 : leavesOK ctxLitU 373650000000 2 ((leaves.drop 20660).take 140) 377150000000 2 = true :=
    take_step (n := 2) (t := 140) (b := 20662) rfl rfl ArealUCore.ArealUK.chunk_10330 s31
  have s29 : leavesOK ctxLitU 373600000000 2 ((leaves.drop 20658).take 142) 377150000000 2 = true :=
    take_step (n := 2) (t := 142) (b := 20660) rfl rfl ArealUCore.ArealUK.chunk_10329 s30
  have s28 : leavesOK ctxLitU 373550000000 2 ((leaves.drop 20656).take 144) 377150000000 2 = true :=
    take_step (n := 2) (t := 144) (b := 20658) rfl rfl ArealUCore.ArealUK.chunk_10328 s29
  have s27 : leavesOK ctxLitU 373500000000 2 ((leaves.drop 20654).take 146) 377150000000 2 = true :=
    take_step (n := 2) (t := 146) (b := 20656) rfl rfl ArealUCore.ArealUK.chunk_10327 s28
  have s26 : leavesOK ctxLitU 373450000000 2 ((leaves.drop 20652).take 148) 377150000000 2 = true :=
    take_step (n := 2) (t := 148) (b := 20654) rfl rfl ArealUCore.ArealUK.chunk_10326 s27
  have s25 : leavesOK ctxLitU 373400000000 2 ((leaves.drop 20650).take 150) 377150000000 2 = true :=
    take_step (n := 2) (t := 150) (b := 20652) rfl rfl ArealUCore.ArealUK.chunk_10325 s26
  have s24 : leavesOK ctxLitU 373350000000 2 ((leaves.drop 20648).take 152) 377150000000 2 = true :=
    take_step (n := 2) (t := 152) (b := 20650) rfl rfl ArealUCore.ArealUK.chunk_10324 s25
  have s23 : leavesOK ctxLitU 373300000000 2 ((leaves.drop 20646).take 154) 377150000000 2 = true :=
    take_step (n := 2) (t := 154) (b := 20648) rfl rfl ArealUCore.ArealUK.chunk_10323 s24
  have s22 : leavesOK ctxLitU 373250000000 2 ((leaves.drop 20644).take 156) 377150000000 2 = true :=
    take_step (n := 2) (t := 156) (b := 20646) rfl rfl ArealUCore.ArealUK.chunk_10322 s23
  have s21 : leavesOK ctxLitU 373200000000 2 ((leaves.drop 20642).take 158) 377150000000 2 = true :=
    take_step (n := 2) (t := 158) (b := 20644) rfl rfl ArealUCore.ArealUK.chunk_10321 s22
  have s20 : leavesOK ctxLitU 373150000000 2 ((leaves.drop 20640).take 160) 377150000000 2 = true :=
    take_step (n := 2) (t := 160) (b := 20642) rfl rfl ArealUCore.ArealUK.chunk_10320 s21
  have s19 : leavesOK ctxLitU 373100000000 2 ((leaves.drop 20638).take 162) 377150000000 2 = true :=
    take_step (n := 2) (t := 162) (b := 20640) rfl rfl ArealUCore.ArealUK.chunk_10319 s20
  have s18 : leavesOK ctxLitU 373050000000 2 ((leaves.drop 20636).take 164) 377150000000 2 = true :=
    take_step (n := 2) (t := 164) (b := 20638) rfl rfl ArealUCore.ArealUK.chunk_10318 s19
  have s17 : leavesOK ctxLitU 373000000000 2 ((leaves.drop 20634).take 166) 377150000000 2 = true :=
    take_step (n := 2) (t := 166) (b := 20636) rfl rfl ArealUCore.ArealUK.chunk_10317 s18
  have s16 : leavesOK ctxLitU 372950000000 2 ((leaves.drop 20632).take 168) 377150000000 2 = true :=
    take_step (n := 2) (t := 168) (b := 20634) rfl rfl ArealUCore.ArealUK.chunk_10316 s17
  have s15 : leavesOK ctxLitU 372900000000 2 ((leaves.drop 20630).take 170) 377150000000 2 = true :=
    take_step (n := 2) (t := 170) (b := 20632) rfl rfl ArealUCore.ArealUK.chunk_10315 s16
  have s14 : leavesOK ctxLitU 372850000000 2 ((leaves.drop 20628).take 172) 377150000000 2 = true :=
    take_step (n := 2) (t := 172) (b := 20630) rfl rfl ArealUCore.ArealUK.chunk_10314 s15
  have s13 : leavesOK ctxLitU 372800000000 2 ((leaves.drop 20626).take 174) 377150000000 2 = true :=
    take_step (n := 2) (t := 174) (b := 20628) rfl rfl ArealUCore.ArealUK.chunk_10313 s14
  have s12 : leavesOK ctxLitU 372750000000 2 ((leaves.drop 20624).take 176) 377150000000 2 = true :=
    take_step (n := 2) (t := 176) (b := 20626) rfl rfl ArealUCore.ArealUK.chunk_10312 s13
  have s11 : leavesOK ctxLitU 372700000000 2 ((leaves.drop 20622).take 178) 377150000000 2 = true :=
    take_step (n := 2) (t := 178) (b := 20624) rfl rfl ArealUCore.ArealUK.chunk_10311 s12
  have s10 : leavesOK ctxLitU 372650000000 2 ((leaves.drop 20620).take 180) 377150000000 2 = true :=
    take_step (n := 2) (t := 180) (b := 20622) rfl rfl ArealUCore.ArealUK.chunk_10310 s11
  have s9 : leavesOK ctxLitU 372600000000 2 ((leaves.drop 20618).take 182) 377150000000 2 = true :=
    take_step (n := 2) (t := 182) (b := 20620) rfl rfl ArealUCore.ArealUK.chunk_10309 s10
  have s8 : leavesOK ctxLitU 372550000000 2 ((leaves.drop 20616).take 184) 377150000000 2 = true :=
    take_step (n := 2) (t := 184) (b := 20618) rfl rfl ArealUCore.ArealUK.chunk_10308 s9
  have s7 : leavesOK ctxLitU 372500000000 2 ((leaves.drop 20614).take 186) 377150000000 2 = true :=
    take_step (n := 2) (t := 186) (b := 20616) rfl rfl ArealUCore.ArealUK.chunk_10307 s8
  have s6 : leavesOK ctxLitU 372450000000 2 ((leaves.drop 20612).take 188) 377150000000 2 = true :=
    take_step (n := 2) (t := 188) (b := 20614) rfl rfl ArealUCore.ArealUK.chunk_10306 s7
  have s5 : leavesOK ctxLitU 372400000000 2 ((leaves.drop 20610).take 190) 377150000000 2 = true :=
    take_step (n := 2) (t := 190) (b := 20612) rfl rfl ArealUCore.ArealUK.chunk_10305 s6
  have s4 : leavesOK ctxLitU 372350000000 2 ((leaves.drop 20608).take 192) 377150000000 2 = true :=
    take_step (n := 2) (t := 192) (b := 20610) rfl rfl ArealUCore.ArealUK.chunk_10304 s5
  have s3 : leavesOK ctxLitU 372300000000 2 ((leaves.drop 20606).take 194) 377150000000 2 = true :=
    take_step (n := 2) (t := 194) (b := 20608) rfl rfl ArealUCore.ArealUK.chunk_10303 s4
  have s2 : leavesOK ctxLitU 372250000000 2 ((leaves.drop 20604).take 196) 377150000000 2 = true :=
    take_step (n := 2) (t := 196) (b := 20606) rfl rfl ArealUCore.ArealUK.chunk_10302 s3
  have s1 : leavesOK ctxLitU 372200000000 2 ((leaves.drop 20602).take 198) 377150000000 2 = true :=
    take_step (n := 2) (t := 198) (b := 20604) rfl rfl ArealUCore.ArealUK.chunk_10301 s2
  have s0 : leavesOK ctxLitU 372150000000 2 ((leaves.drop 20600).take 200) 377150000000 2 = true :=
    take_step (n := 2) (t := 200) (b := 20602) rfl rfl ArealUCore.ArealUK.chunk_10300 s1
  exact s0

end Areal.UCert

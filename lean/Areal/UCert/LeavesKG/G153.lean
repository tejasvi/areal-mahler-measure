import ArealUK.Chunk15300
import ArealUK.Chunk15301
import ArealUK.Chunk15302
import ArealUK.Chunk15303
import ArealUK.Chunk15304
import ArealUK.Chunk15305
import ArealUK.Chunk15306
import ArealUK.Chunk15307
import ArealUK.Chunk15308
import ArealUK.Chunk15309
import ArealUK.Chunk15310
import ArealUK.Chunk15311
import ArealUK.Chunk15312
import ArealUK.Chunk15313
import ArealUK.Chunk15314
import ArealUK.Chunk15315
import ArealUK.Chunk15316
import ArealUK.Chunk15317
import ArealUK.Chunk15318
import ArealUK.Chunk15319
import ArealUK.Chunk15320
import ArealUK.Chunk15321
import ArealUK.Chunk15322
import ArealUK.Chunk15323
import ArealUK.Chunk15324
import ArealUK.Chunk15325
import ArealUK.Chunk15326
import ArealUK.Chunk15327
import ArealUK.Chunk15328
import ArealUK.Chunk15329
import ArealUK.Chunk15330
import ArealUK.Chunk15331
import ArealUK.Chunk15332
import ArealUK.Chunk15333
import ArealUK.Chunk15334
import ArealUK.Chunk15335
import ArealUK.Chunk15336
import ArealUK.Chunk15337
import ArealUK.Chunk15338
import ArealUK.Chunk15339
import ArealUK.Chunk15340
import ArealUK.Chunk15341
import ArealUK.Chunk15342
import ArealUK.Chunk15343
import ArealUK.Chunk15344
import ArealUK.Chunk15345
import ArealUK.Chunk15346
import ArealUK.Chunk15347
import ArealUK.Chunk15348
import ArealUK.Chunk15349
import ArealUK.Chunk15350
import ArealUK.Chunk15351
import ArealUK.Chunk15352
import ArealUK.Chunk15353
import ArealUK.Chunk15354
import ArealUK.Chunk15355
import ArealUK.Chunk15356
import ArealUK.Chunk15357
import ArealUK.Chunk15358
import ArealUK.Chunk15359
import ArealUK.Chunk15360
import ArealUK.Chunk15361
import ArealUK.Chunk15362
import ArealUK.Chunk15363
import ArealUK.Chunk15364
import ArealUK.Chunk15365
import ArealUK.Chunk15366
import ArealUK.Chunk15367
import ArealUK.Chunk15368
import ArealUK.Chunk15369
import ArealUK.Chunk15370
import ArealUK.Chunk15371
import ArealUK.Chunk15372
import ArealUK.Chunk15373
import ArealUK.Chunk15374
import ArealUK.Chunk15375
import ArealUK.Chunk15376
import ArealUK.Chunk15377
import ArealUK.Chunk15378
import ArealUK.Chunk15379
import ArealUK.Chunk15380
import ArealUK.Chunk15381
import ArealUK.Chunk15382
import ArealUK.Chunk15383
import ArealUK.Chunk15384
import ArealUK.Chunk15385
import ArealUK.Chunk15386
import ArealUK.Chunk15387
import ArealUK.Chunk15388
import ArealUK.Chunk15389
import ArealUK.Chunk15390
import ArealUK.Chunk15391
import ArealUK.Chunk15392
import ArealUK.Chunk15393
import ArealUK.Chunk15394
import ArealUK.Chunk15395
import ArealUK.Chunk15396
import ArealUK.Chunk15397
import ArealUK.Chunk15398
import ArealUK.Chunk15399
import Areal.UCert.LeavesKGen

/-! Group 153 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_153 : leavesOK ctxLitU 321387500000 1 ((leaves.drop 30600).take 200) 324387500000 1 = true := by
  have s99 := ArealUCore.ArealUK.chunk_15399
  have s98 : leavesOK ctxLitU 324325000000 1 ((leaves.drop 30796).take 4) 324387500000 1 = true :=
    take_step (n := 2) (t := 4) (b := 30798) rfl rfl ArealUCore.ArealUK.chunk_15398 s99
  have s97 : leavesOK ctxLitU 324275000000 1 ((leaves.drop 30794).take 6) 324387500000 1 = true :=
    take_step (n := 2) (t := 6) (b := 30796) rfl rfl ArealUCore.ArealUK.chunk_15397 s98
  have s96 : leavesOK ctxLitU 324225000000 1 ((leaves.drop 30792).take 8) 324387500000 1 = true :=
    take_step (n := 2) (t := 8) (b := 30794) rfl rfl ArealUCore.ArealUK.chunk_15396 s97
  have s95 : leavesOK ctxLitU 324187500000 1 ((leaves.drop 30790).take 10) 324387500000 1 = true :=
    take_step (n := 2) (t := 10) (b := 30792) rfl rfl ArealUCore.ArealUK.chunk_15395 s96
  have s94 : leavesOK ctxLitU 324162500000 1 ((leaves.drop 30788).take 12) 324387500000 1 = true :=
    take_step (n := 2) (t := 12) (b := 30790) rfl rfl ArealUCore.ArealUK.chunk_15394 s95
  have s93 : leavesOK ctxLitU 162068750000 0 ((leaves.drop 30786).take 14) 324387500000 1 = true :=
    take_step (n := 2) (t := 14) (b := 30788) rfl rfl ArealUCore.ArealUK.chunk_15393 s94
  have s92 : leavesOK ctxLitU 162056250000 0 ((leaves.drop 30784).take 16) 324387500000 1 = true :=
    take_step (n := 2) (t := 16) (b := 30786) rfl rfl ArealUCore.ArealUK.chunk_15392 s93
  have s91 : leavesOK ctxLitU 162043750000 0 ((leaves.drop 30782).take 18) 324387500000 1 = true :=
    take_step (n := 2) (t := 18) (b := 30784) rfl rfl ArealUCore.ArealUK.chunk_15391 s92
  have s90 : leavesOK ctxLitU 162031250000 0 ((leaves.drop 30780).take 20) 324387500000 1 = true :=
    take_step (n := 2) (t := 20) (b := 30782) rfl rfl ArealUCore.ArealUK.chunk_15390 s91
  have s89 : leavesOK ctxLitU 162018750000 0 ((leaves.drop 30778).take 22) 324387500000 1 = true :=
    take_step (n := 2) (t := 22) (b := 30780) rfl rfl ArealUCore.ArealUK.chunk_15389 s90
  have s88 : leavesOK ctxLitU 162006250000 0 ((leaves.drop 30776).take 24) 324387500000 1 = true :=
    take_step (n := 2) (t := 24) (b := 30778) rfl rfl ArealUCore.ArealUK.chunk_15388 s89
  have s87 : leavesOK ctxLitU 161993750000 0 ((leaves.drop 30774).take 26) 324387500000 1 = true :=
    take_step (n := 2) (t := 26) (b := 30776) rfl rfl ArealUCore.ArealUK.chunk_15387 s88
  have s86 : leavesOK ctxLitU 161981250000 0 ((leaves.drop 30772).take 28) 324387500000 1 = true :=
    take_step (n := 2) (t := 28) (b := 30774) rfl rfl ArealUCore.ArealUK.chunk_15386 s87
  have s85 : leavesOK ctxLitU 161968750000 0 ((leaves.drop 30770).take 30) 324387500000 1 = true :=
    take_step (n := 2) (t := 30) (b := 30772) rfl rfl ArealUCore.ArealUK.chunk_15385 s86
  have s84 : leavesOK ctxLitU 161956250000 0 ((leaves.drop 30768).take 32) 324387500000 1 = true :=
    take_step (n := 2) (t := 32) (b := 30770) rfl rfl ArealUCore.ArealUK.chunk_15384 s85
  have s83 : leavesOK ctxLitU 161943750000 0 ((leaves.drop 30766).take 34) 324387500000 1 = true :=
    take_step (n := 2) (t := 34) (b := 30768) rfl rfl ArealUCore.ArealUK.chunk_15383 s84
  have s82 : leavesOK ctxLitU 161931250000 0 ((leaves.drop 30764).take 36) 324387500000 1 = true :=
    take_step (n := 2) (t := 36) (b := 30766) rfl rfl ArealUCore.ArealUK.chunk_15382 s83
  have s81 : leavesOK ctxLitU 323837500000 1 ((leaves.drop 30762).take 38) 324387500000 1 = true :=
    take_step (n := 2) (t := 38) (b := 30764) rfl rfl ArealUCore.ArealUK.chunk_15381 s82
  have s80 : leavesOK ctxLitU 323812500000 1 ((leaves.drop 30760).take 40) 324387500000 1 = true :=
    take_step (n := 2) (t := 40) (b := 30762) rfl rfl ArealUCore.ArealUK.chunk_15380 s81
  have s79 : leavesOK ctxLitU 161887500000 0 ((leaves.drop 30758).take 42) 324387500000 1 = true :=
    take_step (n := 2) (t := 42) (b := 30760) rfl rfl ArealUCore.ArealUK.chunk_15379 s80
  have s78 : leavesOK ctxLitU 161868750000 0 ((leaves.drop 30756).take 44) 324387500000 1 = true :=
    take_step (n := 2) (t := 44) (b := 30758) rfl rfl ArealUCore.ArealUK.chunk_15378 s79
  have s77 : leavesOK ctxLitU 161856250000 0 ((leaves.drop 30754).take 46) 324387500000 1 = true :=
    take_step (n := 2) (t := 46) (b := 30756) rfl rfl ArealUCore.ArealUK.chunk_15377 s78
  have s76 : leavesOK ctxLitU 161843750000 0 ((leaves.drop 30752).take 48) 324387500000 1 = true :=
    take_step (n := 2) (t := 48) (b := 30754) rfl rfl ArealUCore.ArealUK.chunk_15376 s77
  have s75 : leavesOK ctxLitU 161831250000 0 ((leaves.drop 30750).take 50) 324387500000 1 = true :=
    take_step (n := 2) (t := 50) (b := 30752) rfl rfl ArealUCore.ArealUK.chunk_15375 s76
  have s74 : leavesOK ctxLitU 323637500000 1 ((leaves.drop 30748).take 52) 324387500000 1 = true :=
    take_step (n := 2) (t := 52) (b := 30750) rfl rfl ArealUCore.ArealUK.chunk_15374 s75
  have s73 : leavesOK ctxLitU 161800000000 0 ((leaves.drop 30746).take 54) 324387500000 1 = true :=
    take_step (n := 2) (t := 54) (b := 30748) rfl rfl ArealUCore.ArealUK.chunk_15373 s74
  have s72 : leavesOK ctxLitU 161775000000 0 ((leaves.drop 30744).take 56) 324387500000 1 = true :=
    take_step (n := 2) (t := 56) (b := 30746) rfl rfl ArealUCore.ArealUK.chunk_15372 s73
  have s71 : leavesOK ctxLitU 161762500000 0 ((leaves.drop 30742).take 58) 324387500000 1 = true :=
    take_step (n := 2) (t := 58) (b := 30744) rfl rfl ArealUCore.ArealUK.chunk_15371 s72
  have s70 : leavesOK ctxLitU 161750000000 0 ((leaves.drop 30740).take 60) 324387500000 1 = true :=
    take_step (n := 2) (t := 60) (b := 30742) rfl rfl ArealUCore.ArealUK.chunk_15370 s71
  have s69 : leavesOK ctxLitU 161737500000 0 ((leaves.drop 30738).take 62) 324387500000 1 = true :=
    take_step (n := 2) (t := 62) (b := 30740) rfl rfl ArealUCore.ArealUK.chunk_15369 s70
  have s68 : leavesOK ctxLitU 161725000000 0 ((leaves.drop 30736).take 64) 324387500000 1 = true :=
    take_step (n := 2) (t := 64) (b := 30738) rfl rfl ArealUCore.ArealUK.chunk_15368 s69
  have s67 : leavesOK ctxLitU 323425000000 1 ((leaves.drop 30734).take 66) 324387500000 1 = true :=
    take_step (n := 2) (t := 66) (b := 30736) rfl rfl ArealUCore.ArealUK.chunk_15367 s68
  have s66 : leavesOK ctxLitU 323400000000 1 ((leaves.drop 30732).take 68) 324387500000 1 = true :=
    take_step (n := 2) (t := 68) (b := 30734) rfl rfl ArealUCore.ArealUK.chunk_15366 s67
  have s65 : leavesOK ctxLitU 161675000000 0 ((leaves.drop 30730).take 70) 324387500000 1 = true :=
    take_step (n := 2) (t := 70) (b := 30732) rfl rfl ArealUCore.ArealUK.chunk_15365 s66
  have s64 : leavesOK ctxLitU 161662500000 0 ((leaves.drop 30728).take 72) 324387500000 1 = true :=
    take_step (n := 2) (t := 72) (b := 30730) rfl rfl ArealUCore.ArealUK.chunk_15364 s65
  have s63 : leavesOK ctxLitU 161650000000 0 ((leaves.drop 30726).take 74) 324387500000 1 = true :=
    take_step (n := 2) (t := 74) (b := 30728) rfl rfl ArealUCore.ArealUK.chunk_15363 s64
  have s62 : leavesOK ctxLitU 161637500000 0 ((leaves.drop 30724).take 76) 324387500000 1 = true :=
    take_step (n := 2) (t := 76) (b := 30726) rfl rfl ArealUCore.ArealUK.chunk_15362 s63
  have s61 : leavesOK ctxLitU 161625000000 0 ((leaves.drop 30722).take 78) 324387500000 1 = true :=
    take_step (n := 2) (t := 78) (b := 30724) rfl rfl ArealUCore.ArealUK.chunk_15361 s62
  have s60 : leavesOK ctxLitU 161600000000 0 ((leaves.drop 30720).take 80) 324387500000 1 = true :=
    take_step (n := 2) (t := 80) (b := 30722) rfl rfl ArealUCore.ArealUK.chunk_15360 s61
  have s59 : leavesOK ctxLitU 161575000000 0 ((leaves.drop 30718).take 82) 324387500000 1 = true :=
    take_step (n := 2) (t := 82) (b := 30720) rfl rfl ArealUCore.ArealUK.chunk_15359 s60
  have s58 : leavesOK ctxLitU 161562500000 0 ((leaves.drop 30716).take 84) 324387500000 1 = true :=
    take_step (n := 2) (t := 84) (b := 30718) rfl rfl ArealUCore.ArealUK.chunk_15358 s59
  have s57 : leavesOK ctxLitU 161550000000 0 ((leaves.drop 30714).take 86) 324387500000 1 = true :=
    take_step (n := 2) (t := 86) (b := 30716) rfl rfl ArealUCore.ArealUK.chunk_15357 s58
  have s56 : leavesOK ctxLitU 161537500000 0 ((leaves.drop 30712).take 88) 324387500000 1 = true :=
    take_step (n := 2) (t := 88) (b := 30714) rfl rfl ArealUCore.ArealUK.chunk_15356 s57
  have s55 : leavesOK ctxLitU 161525000000 0 ((leaves.drop 30710).take 90) 324387500000 1 = true :=
    take_step (n := 2) (t := 90) (b := 30712) rfl rfl ArealUCore.ArealUK.chunk_15355 s56
  have s54 : leavesOK ctxLitU 161500000000 0 ((leaves.drop 30708).take 92) 324387500000 1 = true :=
    take_step (n := 2) (t := 92) (b := 30710) rfl rfl ArealUCore.ArealUK.chunk_15354 s55
  have s53 : leavesOK ctxLitU 322975000000 1 ((leaves.drop 30706).take 94) 324387500000 1 = true :=
    take_step (n := 2) (t := 94) (b := 30708) rfl rfl ArealUCore.ArealUK.chunk_15353 s54
  have s52 : leavesOK ctxLitU 322950000000 1 ((leaves.drop 30704).take 96) 324387500000 1 = true :=
    take_step (n := 2) (t := 96) (b := 30706) rfl rfl ArealUCore.ArealUK.chunk_15352 s53
  have s51 : leavesOK ctxLitU 161462500000 0 ((leaves.drop 30702).take 98) 324387500000 1 = true :=
    take_step (n := 2) (t := 98) (b := 30704) rfl rfl ArealUCore.ArealUK.chunk_15351 s52
  have s50 : leavesOK ctxLitU 161450000000 0 ((leaves.drop 30700).take 100) 324387500000 1 = true :=
    take_step (n := 2) (t := 100) (b := 30702) rfl rfl ArealUCore.ArealUK.chunk_15350 s51
  have s49 : leavesOK ctxLitU 161425000000 0 ((leaves.drop 30698).take 102) 324387500000 1 = true :=
    take_step (n := 2) (t := 102) (b := 30700) rfl rfl ArealUCore.ArealUK.chunk_15349 s50
  have s48 : leavesOK ctxLitU 161412500000 0 ((leaves.drop 30696).take 104) 324387500000 1 = true :=
    take_step (n := 2) (t := 104) (b := 30698) rfl rfl ArealUCore.ArealUK.chunk_15348 s49
  have s47 : leavesOK ctxLitU 161400000000 0 ((leaves.drop 30694).take 106) 324387500000 1 = true :=
    take_step (n := 2) (t := 106) (b := 30696) rfl rfl ArealUCore.ArealUK.chunk_15347 s48
  have s46 : leavesOK ctxLitU 161387500000 0 ((leaves.drop 30692).take 108) 324387500000 1 = true :=
    take_step (n := 2) (t := 108) (b := 30694) rfl rfl ArealUCore.ArealUK.chunk_15346 s47
  have s45 : leavesOK ctxLitU 161375000000 0 ((leaves.drop 30690).take 110) 324387500000 1 = true :=
    take_step (n := 2) (t := 110) (b := 30692) rfl rfl ArealUCore.ArealUK.chunk_15345 s46
  have s44 : leavesOK ctxLitU 161362500000 0 ((leaves.drop 30688).take 112) 324387500000 1 = true :=
    take_step (n := 2) (t := 112) (b := 30690) rfl rfl ArealUCore.ArealUK.chunk_15344 s45
  have s43 : leavesOK ctxLitU 161350000000 0 ((leaves.drop 30686).take 114) 324387500000 1 = true :=
    take_step (n := 2) (t := 114) (b := 30688) rfl rfl ArealUCore.ArealUK.chunk_15343 s44
  have s42 : leavesOK ctxLitU 161337500000 0 ((leaves.drop 30684).take 116) 324387500000 1 = true :=
    take_step (n := 2) (t := 116) (b := 30686) rfl rfl ArealUCore.ArealUK.chunk_15342 s43
  have s41 : leavesOK ctxLitU 161325000000 0 ((leaves.drop 30682).take 118) 324387500000 1 = true :=
    take_step (n := 2) (t := 118) (b := 30684) rfl rfl ArealUCore.ArealUK.chunk_15341 s42
  have s40 : leavesOK ctxLitU 161300000000 0 ((leaves.drop 30680).take 120) 324387500000 1 = true :=
    take_step (n := 2) (t := 120) (b := 30682) rfl rfl ArealUCore.ArealUK.chunk_15340 s41
  have s39 : leavesOK ctxLitU 161275000000 0 ((leaves.drop 30678).take 122) 324387500000 1 = true :=
    take_step (n := 2) (t := 122) (b := 30680) rfl rfl ArealUCore.ArealUK.chunk_15339 s40
  have s38 : leavesOK ctxLitU 161262500000 0 ((leaves.drop 30676).take 124) 324387500000 1 = true :=
    take_step (n := 2) (t := 124) (b := 30678) rfl rfl ArealUCore.ArealUK.chunk_15338 s39
  have s37 : leavesOK ctxLitU 161250000000 0 ((leaves.drop 30674).take 126) 324387500000 1 = true :=
    take_step (n := 2) (t := 126) (b := 30676) rfl rfl ArealUCore.ArealUK.chunk_15337 s38
  have s36 : leavesOK ctxLitU 161237500000 0 ((leaves.drop 30672).take 128) 324387500000 1 = true :=
    take_step (n := 2) (t := 128) (b := 30674) rfl rfl ArealUCore.ArealUK.chunk_15336 s37
  have s35 : leavesOK ctxLitU 161225000000 0 ((leaves.drop 30670).take 130) 324387500000 1 = true :=
    take_step (n := 2) (t := 130) (b := 30672) rfl rfl ArealUCore.ArealUK.chunk_15335 s36
  have s34 : leavesOK ctxLitU 161200000000 0 ((leaves.drop 30668).take 132) 324387500000 1 = true :=
    take_step (n := 2) (t := 132) (b := 30670) rfl rfl ArealUCore.ArealUK.chunk_15334 s35
  have s33 : leavesOK ctxLitU 161187500000 0 ((leaves.drop 30666).take 134) 324387500000 1 = true :=
    take_step (n := 2) (t := 134) (b := 30668) rfl rfl ArealUCore.ArealUK.chunk_15333 s34
  have s32 : leavesOK ctxLitU 161175000000 0 ((leaves.drop 30664).take 136) 324387500000 1 = true :=
    take_step (n := 2) (t := 136) (b := 30666) rfl rfl ArealUCore.ArealUK.chunk_15332 s33
  have s31 : leavesOK ctxLitU 161162500000 0 ((leaves.drop 30662).take 138) 324387500000 1 = true :=
    take_step (n := 2) (t := 138) (b := 30664) rfl rfl ArealUCore.ArealUK.chunk_15331 s32
  have s30 : leavesOK ctxLitU 161150000000 0 ((leaves.drop 30660).take 140) 324387500000 1 = true :=
    take_step (n := 2) (t := 140) (b := 30662) rfl rfl ArealUCore.ArealUK.chunk_15330 s31
  have s29 : leavesOK ctxLitU 161137500000 0 ((leaves.drop 30658).take 142) 324387500000 1 = true :=
    take_step (n := 2) (t := 142) (b := 30660) rfl rfl ArealUCore.ArealUK.chunk_15329 s30
  have s28 : leavesOK ctxLitU 161125000000 0 ((leaves.drop 30656).take 144) 324387500000 1 = true :=
    take_step (n := 2) (t := 144) (b := 30658) rfl rfl ArealUCore.ArealUK.chunk_15328 s29
  have s27 : leavesOK ctxLitU 322225000000 1 ((leaves.drop 30654).take 146) 324387500000 1 = true :=
    take_step (n := 2) (t := 146) (b := 30656) rfl rfl ArealUCore.ArealUK.chunk_15327 s28
  have s26 : leavesOK ctxLitU 322200000000 1 ((leaves.drop 30652).take 148) 324387500000 1 = true :=
    take_step (n := 2) (t := 148) (b := 30654) rfl rfl ArealUCore.ArealUK.chunk_15326 s27
  have s25 : leavesOK ctxLitU 322150000000 1 ((leaves.drop 30650).take 150) 324387500000 1 = true :=
    take_step (n := 2) (t := 150) (b := 30652) rfl rfl ArealUCore.ArealUK.chunk_15325 s26
  have s24 : leavesOK ctxLitU 161050000000 0 ((leaves.drop 30648).take 152) 324387500000 1 = true :=
    take_step (n := 2) (t := 152) (b := 30650) rfl rfl ArealUCore.ArealUK.chunk_15324 s25
  have s23 : leavesOK ctxLitU 161037500000 0 ((leaves.drop 30646).take 154) 324387500000 1 = true :=
    take_step (n := 2) (t := 154) (b := 30648) rfl rfl ArealUCore.ArealUK.chunk_15323 s24
  have s22 : leavesOK ctxLitU 161025000000 0 ((leaves.drop 30644).take 156) 324387500000 1 = true :=
    take_step (n := 2) (t := 156) (b := 30646) rfl rfl ArealUCore.ArealUK.chunk_15322 s23
  have s21 : leavesOK ctxLitU 161000000000 0 ((leaves.drop 30642).take 158) 324387500000 1 = true :=
    take_step (n := 2) (t := 158) (b := 30644) rfl rfl ArealUCore.ArealUK.chunk_15321 s22
  have s20 : leavesOK ctxLitU 160975000000 0 ((leaves.drop 30640).take 160) 324387500000 1 = true :=
    take_step (n := 2) (t := 160) (b := 30642) rfl rfl ArealUCore.ArealUK.chunk_15320 s21
  have s19 : leavesOK ctxLitU 160962500000 0 ((leaves.drop 30638).take 162) 324387500000 1 = true :=
    take_step (n := 2) (t := 162) (b := 30640) rfl rfl ArealUCore.ArealUK.chunk_15319 s20
  have s18 : leavesOK ctxLitU 160950000000 0 ((leaves.drop 30636).take 164) 324387500000 1 = true :=
    take_step (n := 2) (t := 164) (b := 30638) rfl rfl ArealUCore.ArealUK.chunk_15318 s19
  have s17 : leavesOK ctxLitU 160937500000 0 ((leaves.drop 30634).take 166) 324387500000 1 = true :=
    take_step (n := 2) (t := 166) (b := 30636) rfl rfl ArealUCore.ArealUK.chunk_15317 s18
  have s16 : leavesOK ctxLitU 160925000000 0 ((leaves.drop 30632).take 168) 324387500000 1 = true :=
    take_step (n := 2) (t := 168) (b := 30634) rfl rfl ArealUCore.ArealUK.chunk_15316 s17
  have s15 : leavesOK ctxLitU 321825000000 1 ((leaves.drop 30630).take 170) 324387500000 1 = true :=
    take_step (n := 2) (t := 170) (b := 30632) rfl rfl ArealUCore.ArealUK.chunk_15315 s16
  have s14 : leavesOK ctxLitU 321800000000 1 ((leaves.drop 30628).take 172) 324387500000 1 = true :=
    take_step (n := 2) (t := 172) (b := 30630) rfl rfl ArealUCore.ArealUK.chunk_15314 s15
  have s13 : leavesOK ctxLitU 160887500000 0 ((leaves.drop 30626).take 174) 324387500000 1 = true :=
    take_step (n := 2) (t := 174) (b := 30628) rfl rfl ArealUCore.ArealUK.chunk_15313 s14
  have s12 : leavesOK ctxLitU 160875000000 0 ((leaves.drop 30624).take 176) 324387500000 1 = true :=
    take_step (n := 2) (t := 176) (b := 30626) rfl rfl ArealUCore.ArealUK.chunk_15312 s13
  have s11 : leavesOK ctxLitU 160862500000 0 ((leaves.drop 30622).take 178) 324387500000 1 = true :=
    take_step (n := 2) (t := 178) (b := 30624) rfl rfl ArealUCore.ArealUK.chunk_15311 s12
  have s10 : leavesOK ctxLitU 160850000000 0 ((leaves.drop 30620).take 180) 324387500000 1 = true :=
    take_step (n := 2) (t := 180) (b := 30622) rfl rfl ArealUCore.ArealUK.chunk_15310 s11
  have s9 : leavesOK ctxLitU 321675000000 1 ((leaves.drop 30618).take 182) 324387500000 1 = true :=
    take_step (n := 2) (t := 182) (b := 30620) rfl rfl ArealUCore.ArealUK.chunk_15309 s10
  have s8 : leavesOK ctxLitU 321650000000 1 ((leaves.drop 30616).take 184) 324387500000 1 = true :=
    take_step (n := 2) (t := 184) (b := 30618) rfl rfl ArealUCore.ArealUK.chunk_15308 s9
  have s7 : leavesOK ctxLitU 321600000000 1 ((leaves.drop 30614).take 186) 324387500000 1 = true :=
    take_step (n := 2) (t := 186) (b := 30616) rfl rfl ArealUCore.ArealUK.chunk_15307 s8
  have s6 : leavesOK ctxLitU 321562500000 1 ((leaves.drop 30612).take 188) 324387500000 1 = true :=
    take_step (n := 2) (t := 188) (b := 30614) rfl rfl ArealUCore.ArealUK.chunk_15306 s7
  have s5 : leavesOK ctxLitU 160768750000 0 ((leaves.drop 30610).take 190) 324387500000 1 = true :=
    take_step (n := 2) (t := 190) (b := 30612) rfl rfl ArealUCore.ArealUK.chunk_15305 s6
  have s4 : leavesOK ctxLitU 160756250000 0 ((leaves.drop 30608).take 192) 324387500000 1 = true :=
    take_step (n := 2) (t := 192) (b := 30610) rfl rfl ArealUCore.ArealUK.chunk_15304 s5
  have s3 : leavesOK ctxLitU 160743750000 0 ((leaves.drop 30606).take 194) 324387500000 1 = true :=
    take_step (n := 2) (t := 194) (b := 30608) rfl rfl ArealUCore.ArealUK.chunk_15303 s4
  have s2 : leavesOK ctxLitU 160731250000 0 ((leaves.drop 30604).take 196) 324387500000 1 = true :=
    take_step (n := 2) (t := 196) (b := 30606) rfl rfl ArealUCore.ArealUK.chunk_15302 s3
  have s1 : leavesOK ctxLitU 160712500000 0 ((leaves.drop 30602).take 198) 324387500000 1 = true :=
    take_step (n := 2) (t := 198) (b := 30604) rfl rfl ArealUCore.ArealUK.chunk_15301 s2
  have s0 : leavesOK ctxLitU 321387500000 1 ((leaves.drop 30600).take 200) 324387500000 1 = true :=
    take_step (n := 2) (t := 200) (b := 30602) rfl rfl ArealUCore.ArealUK.chunk_15300 s1
  exact s0

end Areal.UCert

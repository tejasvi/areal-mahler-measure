import ArealUK.Chunk12300
import ArealUK.Chunk12301
import ArealUK.Chunk12302
import ArealUK.Chunk12303
import ArealUK.Chunk12304
import ArealUK.Chunk12305
import ArealUK.Chunk12306
import ArealUK.Chunk12307
import ArealUK.Chunk12308
import ArealUK.Chunk12309
import ArealUK.Chunk12310
import ArealUK.Chunk12311
import ArealUK.Chunk12312
import ArealUK.Chunk12313
import ArealUK.Chunk12314
import ArealUK.Chunk12315
import ArealUK.Chunk12316
import ArealUK.Chunk12317
import ArealUK.Chunk12318
import ArealUK.Chunk12319
import ArealUK.Chunk12320
import ArealUK.Chunk12321
import ArealUK.Chunk12322
import ArealUK.Chunk12323
import ArealUK.Chunk12324
import ArealUK.Chunk12325
import ArealUK.Chunk12326
import ArealUK.Chunk12327
import ArealUK.Chunk12328
import ArealUK.Chunk12329
import ArealUK.Chunk12330
import ArealUK.Chunk12331
import ArealUK.Chunk12332
import ArealUK.Chunk12333
import ArealUK.Chunk12334
import ArealUK.Chunk12335
import ArealUK.Chunk12336
import ArealUK.Chunk12337
import ArealUK.Chunk12338
import ArealUK.Chunk12339
import ArealUK.Chunk12340
import ArealUK.Chunk12341
import ArealUK.Chunk12342
import ArealUK.Chunk12343
import ArealUK.Chunk12344
import ArealUK.Chunk12345
import ArealUK.Chunk12346
import ArealUK.Chunk12347
import ArealUK.Chunk12348
import ArealUK.Chunk12349
import ArealUK.Chunk12350
import ArealUK.Chunk12351
import ArealUK.Chunk12352
import ArealUK.Chunk12353
import ArealUK.Chunk12354
import ArealUK.Chunk12355
import ArealUK.Chunk12356
import ArealUK.Chunk12357
import ArealUK.Chunk12358
import ArealUK.Chunk12359
import ArealUK.Chunk12360
import ArealUK.Chunk12361
import ArealUK.Chunk12362
import ArealUK.Chunk12363
import ArealUK.Chunk12364
import ArealUK.Chunk12365
import ArealUK.Chunk12366
import ArealUK.Chunk12367
import ArealUK.Chunk12368
import ArealUK.Chunk12369
import ArealUK.Chunk12370
import ArealUK.Chunk12371
import ArealUK.Chunk12372
import ArealUK.Chunk12373
import ArealUK.Chunk12374
import ArealUK.Chunk12375
import ArealUK.Chunk12376
import ArealUK.Chunk12377
import ArealUK.Chunk12378
import ArealUK.Chunk12379
import ArealUK.Chunk12380
import ArealUK.Chunk12381
import ArealUK.Chunk12382
import ArealUK.Chunk12383
import ArealUK.Chunk12384
import ArealUK.Chunk12385
import ArealUK.Chunk12386
import ArealUK.Chunk12387
import ArealUK.Chunk12388
import ArealUK.Chunk12389
import ArealUK.Chunk12390
import ArealUK.Chunk12391
import ArealUK.Chunk12392
import ArealUK.Chunk12393
import ArealUK.Chunk12394
import ArealUK.Chunk12395
import ArealUK.Chunk12396
import ArealUK.Chunk12397
import ArealUK.Chunk12398
import ArealUK.Chunk12399
import Areal.UCert.LeavesKGen

/-! Group 123 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_123 : leavesOK ctxLitU 492775000000 2 ((leaves.drop 24600).take 200) 497775000000 2 = true := by
  have s99 := ArealUCore.ArealUK.chunk_12399
  have s98 : leavesOK ctxLitU 497675000000 2 ((leaves.drop 24796).take 4) 497775000000 2 = true :=
    take_step (n := 2) (t := 4) (b := 24798) rfl rfl ArealUCore.ArealUK.chunk_12398 s99
  have s97 : leavesOK ctxLitU 497625000000 2 ((leaves.drop 24794).take 6) 497775000000 2 = true :=
    take_step (n := 2) (t := 6) (b := 24796) rfl rfl ArealUCore.ArealUK.chunk_12397 s98
  have s96 : leavesOK ctxLitU 497575000000 2 ((leaves.drop 24792).take 8) 497775000000 2 = true :=
    take_step (n := 2) (t := 8) (b := 24794) rfl rfl ArealUCore.ArealUK.chunk_12396 s97
  have s95 : leavesOK ctxLitU 497525000000 2 ((leaves.drop 24790).take 10) 497775000000 2 = true :=
    take_step (n := 2) (t := 10) (b := 24792) rfl rfl ArealUCore.ArealUK.chunk_12395 s96
  have s94 : leavesOK ctxLitU 497475000000 2 ((leaves.drop 24788).take 12) 497775000000 2 = true :=
    take_step (n := 2) (t := 12) (b := 24790) rfl rfl ArealUCore.ArealUK.chunk_12394 s95
  have s93 : leavesOK ctxLitU 497425000000 2 ((leaves.drop 24786).take 14) 497775000000 2 = true :=
    take_step (n := 2) (t := 14) (b := 24788) rfl rfl ArealUCore.ArealUK.chunk_12393 s94
  have s92 : leavesOK ctxLitU 497375000000 2 ((leaves.drop 24784).take 16) 497775000000 2 = true :=
    take_step (n := 2) (t := 16) (b := 24786) rfl rfl ArealUCore.ArealUK.chunk_12392 s93
  have s91 : leavesOK ctxLitU 497325000000 2 ((leaves.drop 24782).take 18) 497775000000 2 = true :=
    take_step (n := 2) (t := 18) (b := 24784) rfl rfl ArealUCore.ArealUK.chunk_12391 s92
  have s90 : leavesOK ctxLitU 497275000000 2 ((leaves.drop 24780).take 20) 497775000000 2 = true :=
    take_step (n := 2) (t := 20) (b := 24782) rfl rfl ArealUCore.ArealUK.chunk_12390 s91
  have s89 : leavesOK ctxLitU 497225000000 2 ((leaves.drop 24778).take 22) 497775000000 2 = true :=
    take_step (n := 2) (t := 22) (b := 24780) rfl rfl ArealUCore.ArealUK.chunk_12389 s90
  have s88 : leavesOK ctxLitU 497175000000 2 ((leaves.drop 24776).take 24) 497775000000 2 = true :=
    take_step (n := 2) (t := 24) (b := 24778) rfl rfl ArealUCore.ArealUK.chunk_12388 s89
  have s87 : leavesOK ctxLitU 497125000000 2 ((leaves.drop 24774).take 26) 497775000000 2 = true :=
    take_step (n := 2) (t := 26) (b := 24776) rfl rfl ArealUCore.ArealUK.chunk_12387 s88
  have s86 : leavesOK ctxLitU 497075000000 2 ((leaves.drop 24772).take 28) 497775000000 2 = true :=
    take_step (n := 2) (t := 28) (b := 24774) rfl rfl ArealUCore.ArealUK.chunk_12386 s87
  have s85 : leavesOK ctxLitU 497025000000 2 ((leaves.drop 24770).take 30) 497775000000 2 = true :=
    take_step (n := 2) (t := 30) (b := 24772) rfl rfl ArealUCore.ArealUK.chunk_12385 s86
  have s84 : leavesOK ctxLitU 496975000000 2 ((leaves.drop 24768).take 32) 497775000000 2 = true :=
    take_step (n := 2) (t := 32) (b := 24770) rfl rfl ArealUCore.ArealUK.chunk_12384 s85
  have s83 : leavesOK ctxLitU 496925000000 2 ((leaves.drop 24766).take 34) 497775000000 2 = true :=
    take_step (n := 2) (t := 34) (b := 24768) rfl rfl ArealUCore.ArealUK.chunk_12383 s84
  have s82 : leavesOK ctxLitU 496875000000 2 ((leaves.drop 24764).take 36) 497775000000 2 = true :=
    take_step (n := 2) (t := 36) (b := 24766) rfl rfl ArealUCore.ArealUK.chunk_12382 s83
  have s81 : leavesOK ctxLitU 496825000000 2 ((leaves.drop 24762).take 38) 497775000000 2 = true :=
    take_step (n := 2) (t := 38) (b := 24764) rfl rfl ArealUCore.ArealUK.chunk_12381 s82
  have s80 : leavesOK ctxLitU 496775000000 2 ((leaves.drop 24760).take 40) 497775000000 2 = true :=
    take_step (n := 2) (t := 40) (b := 24762) rfl rfl ArealUCore.ArealUK.chunk_12380 s81
  have s79 : leavesOK ctxLitU 496725000000 2 ((leaves.drop 24758).take 42) 497775000000 2 = true :=
    take_step (n := 2) (t := 42) (b := 24760) rfl rfl ArealUCore.ArealUK.chunk_12379 s80
  have s78 : leavesOK ctxLitU 496675000000 2 ((leaves.drop 24756).take 44) 497775000000 2 = true :=
    take_step (n := 2) (t := 44) (b := 24758) rfl rfl ArealUCore.ArealUK.chunk_12378 s79
  have s77 : leavesOK ctxLitU 496625000000 2 ((leaves.drop 24754).take 46) 497775000000 2 = true :=
    take_step (n := 2) (t := 46) (b := 24756) rfl rfl ArealUCore.ArealUK.chunk_12377 s78
  have s76 : leavesOK ctxLitU 496575000000 2 ((leaves.drop 24752).take 48) 497775000000 2 = true :=
    take_step (n := 2) (t := 48) (b := 24754) rfl rfl ArealUCore.ArealUK.chunk_12376 s77
  have s75 : leavesOK ctxLitU 496525000000 2 ((leaves.drop 24750).take 50) 497775000000 2 = true :=
    take_step (n := 2) (t := 50) (b := 24752) rfl rfl ArealUCore.ArealUK.chunk_12375 s76
  have s74 : leavesOK ctxLitU 496475000000 2 ((leaves.drop 24748).take 52) 497775000000 2 = true :=
    take_step (n := 2) (t := 52) (b := 24750) rfl rfl ArealUCore.ArealUK.chunk_12374 s75
  have s73 : leavesOK ctxLitU 496425000000 2 ((leaves.drop 24746).take 54) 497775000000 2 = true :=
    take_step (n := 2) (t := 54) (b := 24748) rfl rfl ArealUCore.ArealUK.chunk_12373 s74
  have s72 : leavesOK ctxLitU 496375000000 2 ((leaves.drop 24744).take 56) 497775000000 2 = true :=
    take_step (n := 2) (t := 56) (b := 24746) rfl rfl ArealUCore.ArealUK.chunk_12372 s73
  have s71 : leavesOK ctxLitU 496325000000 2 ((leaves.drop 24742).take 58) 497775000000 2 = true :=
    take_step (n := 2) (t := 58) (b := 24744) rfl rfl ArealUCore.ArealUK.chunk_12371 s72
  have s70 : leavesOK ctxLitU 496275000000 2 ((leaves.drop 24740).take 60) 497775000000 2 = true :=
    take_step (n := 2) (t := 60) (b := 24742) rfl rfl ArealUCore.ArealUK.chunk_12370 s71
  have s69 : leavesOK ctxLitU 496225000000 2 ((leaves.drop 24738).take 62) 497775000000 2 = true :=
    take_step (n := 2) (t := 62) (b := 24740) rfl rfl ArealUCore.ArealUK.chunk_12369 s70
  have s68 : leavesOK ctxLitU 496175000000 2 ((leaves.drop 24736).take 64) 497775000000 2 = true :=
    take_step (n := 2) (t := 64) (b := 24738) rfl rfl ArealUCore.ArealUK.chunk_12368 s69
  have s67 : leavesOK ctxLitU 496125000000 2 ((leaves.drop 24734).take 66) 497775000000 2 = true :=
    take_step (n := 2) (t := 66) (b := 24736) rfl rfl ArealUCore.ArealUK.chunk_12367 s68
  have s66 : leavesOK ctxLitU 496075000000 2 ((leaves.drop 24732).take 68) 497775000000 2 = true :=
    take_step (n := 2) (t := 68) (b := 24734) rfl rfl ArealUCore.ArealUK.chunk_12366 s67
  have s65 : leavesOK ctxLitU 496025000000 2 ((leaves.drop 24730).take 70) 497775000000 2 = true :=
    take_step (n := 2) (t := 70) (b := 24732) rfl rfl ArealUCore.ArealUK.chunk_12365 s66
  have s64 : leavesOK ctxLitU 495975000000 2 ((leaves.drop 24728).take 72) 497775000000 2 = true :=
    take_step (n := 2) (t := 72) (b := 24730) rfl rfl ArealUCore.ArealUK.chunk_12364 s65
  have s63 : leavesOK ctxLitU 495925000000 2 ((leaves.drop 24726).take 74) 497775000000 2 = true :=
    take_step (n := 2) (t := 74) (b := 24728) rfl rfl ArealUCore.ArealUK.chunk_12363 s64
  have s62 : leavesOK ctxLitU 495875000000 2 ((leaves.drop 24724).take 76) 497775000000 2 = true :=
    take_step (n := 2) (t := 76) (b := 24726) rfl rfl ArealUCore.ArealUK.chunk_12362 s63
  have s61 : leavesOK ctxLitU 495825000000 2 ((leaves.drop 24722).take 78) 497775000000 2 = true :=
    take_step (n := 2) (t := 78) (b := 24724) rfl rfl ArealUCore.ArealUK.chunk_12361 s62
  have s60 : leavesOK ctxLitU 495775000000 2 ((leaves.drop 24720).take 80) 497775000000 2 = true :=
    take_step (n := 2) (t := 80) (b := 24722) rfl rfl ArealUCore.ArealUK.chunk_12360 s61
  have s59 : leavesOK ctxLitU 495725000000 2 ((leaves.drop 24718).take 82) 497775000000 2 = true :=
    take_step (n := 2) (t := 82) (b := 24720) rfl rfl ArealUCore.ArealUK.chunk_12359 s60
  have s58 : leavesOK ctxLitU 495675000000 2 ((leaves.drop 24716).take 84) 497775000000 2 = true :=
    take_step (n := 2) (t := 84) (b := 24718) rfl rfl ArealUCore.ArealUK.chunk_12358 s59
  have s57 : leavesOK ctxLitU 495625000000 2 ((leaves.drop 24714).take 86) 497775000000 2 = true :=
    take_step (n := 2) (t := 86) (b := 24716) rfl rfl ArealUCore.ArealUK.chunk_12357 s58
  have s56 : leavesOK ctxLitU 495575000000 2 ((leaves.drop 24712).take 88) 497775000000 2 = true :=
    take_step (n := 2) (t := 88) (b := 24714) rfl rfl ArealUCore.ArealUK.chunk_12356 s57
  have s55 : leavesOK ctxLitU 495525000000 2 ((leaves.drop 24710).take 90) 497775000000 2 = true :=
    take_step (n := 2) (t := 90) (b := 24712) rfl rfl ArealUCore.ArealUK.chunk_12355 s56
  have s54 : leavesOK ctxLitU 495475000000 2 ((leaves.drop 24708).take 92) 497775000000 2 = true :=
    take_step (n := 2) (t := 92) (b := 24710) rfl rfl ArealUCore.ArealUK.chunk_12354 s55
  have s53 : leavesOK ctxLitU 495425000000 2 ((leaves.drop 24706).take 94) 497775000000 2 = true :=
    take_step (n := 2) (t := 94) (b := 24708) rfl rfl ArealUCore.ArealUK.chunk_12353 s54
  have s52 : leavesOK ctxLitU 495375000000 2 ((leaves.drop 24704).take 96) 497775000000 2 = true :=
    take_step (n := 2) (t := 96) (b := 24706) rfl rfl ArealUCore.ArealUK.chunk_12352 s53
  have s51 : leavesOK ctxLitU 495325000000 2 ((leaves.drop 24702).take 98) 497775000000 2 = true :=
    take_step (n := 2) (t := 98) (b := 24704) rfl rfl ArealUCore.ArealUK.chunk_12351 s52
  have s50 : leavesOK ctxLitU 495275000000 2 ((leaves.drop 24700).take 100) 497775000000 2 = true :=
    take_step (n := 2) (t := 100) (b := 24702) rfl rfl ArealUCore.ArealUK.chunk_12350 s51
  have s49 : leavesOK ctxLitU 495225000000 2 ((leaves.drop 24698).take 102) 497775000000 2 = true :=
    take_step (n := 2) (t := 102) (b := 24700) rfl rfl ArealUCore.ArealUK.chunk_12349 s50
  have s48 : leavesOK ctxLitU 495175000000 2 ((leaves.drop 24696).take 104) 497775000000 2 = true :=
    take_step (n := 2) (t := 104) (b := 24698) rfl rfl ArealUCore.ArealUK.chunk_12348 s49
  have s47 : leavesOK ctxLitU 495125000000 2 ((leaves.drop 24694).take 106) 497775000000 2 = true :=
    take_step (n := 2) (t := 106) (b := 24696) rfl rfl ArealUCore.ArealUK.chunk_12347 s48
  have s46 : leavesOK ctxLitU 495075000000 2 ((leaves.drop 24692).take 108) 497775000000 2 = true :=
    take_step (n := 2) (t := 108) (b := 24694) rfl rfl ArealUCore.ArealUK.chunk_12346 s47
  have s45 : leavesOK ctxLitU 495025000000 2 ((leaves.drop 24690).take 110) 497775000000 2 = true :=
    take_step (n := 2) (t := 110) (b := 24692) rfl rfl ArealUCore.ArealUK.chunk_12345 s46
  have s44 : leavesOK ctxLitU 494975000000 2 ((leaves.drop 24688).take 112) 497775000000 2 = true :=
    take_step (n := 2) (t := 112) (b := 24690) rfl rfl ArealUCore.ArealUK.chunk_12344 s45
  have s43 : leavesOK ctxLitU 494925000000 2 ((leaves.drop 24686).take 114) 497775000000 2 = true :=
    take_step (n := 2) (t := 114) (b := 24688) rfl rfl ArealUCore.ArealUK.chunk_12343 s44
  have s42 : leavesOK ctxLitU 494875000000 2 ((leaves.drop 24684).take 116) 497775000000 2 = true :=
    take_step (n := 2) (t := 116) (b := 24686) rfl rfl ArealUCore.ArealUK.chunk_12342 s43
  have s41 : leavesOK ctxLitU 494825000000 2 ((leaves.drop 24682).take 118) 497775000000 2 = true :=
    take_step (n := 2) (t := 118) (b := 24684) rfl rfl ArealUCore.ArealUK.chunk_12341 s42
  have s40 : leavesOK ctxLitU 494775000000 2 ((leaves.drop 24680).take 120) 497775000000 2 = true :=
    take_step (n := 2) (t := 120) (b := 24682) rfl rfl ArealUCore.ArealUK.chunk_12340 s41
  have s39 : leavesOK ctxLitU 494725000000 2 ((leaves.drop 24678).take 122) 497775000000 2 = true :=
    take_step (n := 2) (t := 122) (b := 24680) rfl rfl ArealUCore.ArealUK.chunk_12339 s40
  have s38 : leavesOK ctxLitU 494675000000 2 ((leaves.drop 24676).take 124) 497775000000 2 = true :=
    take_step (n := 2) (t := 124) (b := 24678) rfl rfl ArealUCore.ArealUK.chunk_12338 s39
  have s37 : leavesOK ctxLitU 494625000000 2 ((leaves.drop 24674).take 126) 497775000000 2 = true :=
    take_step (n := 2) (t := 126) (b := 24676) rfl rfl ArealUCore.ArealUK.chunk_12337 s38
  have s36 : leavesOK ctxLitU 494575000000 2 ((leaves.drop 24672).take 128) 497775000000 2 = true :=
    take_step (n := 2) (t := 128) (b := 24674) rfl rfl ArealUCore.ArealUK.chunk_12336 s37
  have s35 : leavesOK ctxLitU 494525000000 2 ((leaves.drop 24670).take 130) 497775000000 2 = true :=
    take_step (n := 2) (t := 130) (b := 24672) rfl rfl ArealUCore.ArealUK.chunk_12335 s36
  have s34 : leavesOK ctxLitU 494475000000 2 ((leaves.drop 24668).take 132) 497775000000 2 = true :=
    take_step (n := 2) (t := 132) (b := 24670) rfl rfl ArealUCore.ArealUK.chunk_12334 s35
  have s33 : leavesOK ctxLitU 494425000000 2 ((leaves.drop 24666).take 134) 497775000000 2 = true :=
    take_step (n := 2) (t := 134) (b := 24668) rfl rfl ArealUCore.ArealUK.chunk_12333 s34
  have s32 : leavesOK ctxLitU 494375000000 2 ((leaves.drop 24664).take 136) 497775000000 2 = true :=
    take_step (n := 2) (t := 136) (b := 24666) rfl rfl ArealUCore.ArealUK.chunk_12332 s33
  have s31 : leavesOK ctxLitU 494325000000 2 ((leaves.drop 24662).take 138) 497775000000 2 = true :=
    take_step (n := 2) (t := 138) (b := 24664) rfl rfl ArealUCore.ArealUK.chunk_12331 s32
  have s30 : leavesOK ctxLitU 494275000000 2 ((leaves.drop 24660).take 140) 497775000000 2 = true :=
    take_step (n := 2) (t := 140) (b := 24662) rfl rfl ArealUCore.ArealUK.chunk_12330 s31
  have s29 : leavesOK ctxLitU 494225000000 2 ((leaves.drop 24658).take 142) 497775000000 2 = true :=
    take_step (n := 2) (t := 142) (b := 24660) rfl rfl ArealUCore.ArealUK.chunk_12329 s30
  have s28 : leavesOK ctxLitU 494175000000 2 ((leaves.drop 24656).take 144) 497775000000 2 = true :=
    take_step (n := 2) (t := 144) (b := 24658) rfl rfl ArealUCore.ArealUK.chunk_12328 s29
  have s27 : leavesOK ctxLitU 494125000000 2 ((leaves.drop 24654).take 146) 497775000000 2 = true :=
    take_step (n := 2) (t := 146) (b := 24656) rfl rfl ArealUCore.ArealUK.chunk_12327 s28
  have s26 : leavesOK ctxLitU 494075000000 2 ((leaves.drop 24652).take 148) 497775000000 2 = true :=
    take_step (n := 2) (t := 148) (b := 24654) rfl rfl ArealUCore.ArealUK.chunk_12326 s27
  have s25 : leavesOK ctxLitU 494025000000 2 ((leaves.drop 24650).take 150) 497775000000 2 = true :=
    take_step (n := 2) (t := 150) (b := 24652) rfl rfl ArealUCore.ArealUK.chunk_12325 s26
  have s24 : leavesOK ctxLitU 493975000000 2 ((leaves.drop 24648).take 152) 497775000000 2 = true :=
    take_step (n := 2) (t := 152) (b := 24650) rfl rfl ArealUCore.ArealUK.chunk_12324 s25
  have s23 : leavesOK ctxLitU 493925000000 2 ((leaves.drop 24646).take 154) 497775000000 2 = true :=
    take_step (n := 2) (t := 154) (b := 24648) rfl rfl ArealUCore.ArealUK.chunk_12323 s24
  have s22 : leavesOK ctxLitU 493875000000 2 ((leaves.drop 24644).take 156) 497775000000 2 = true :=
    take_step (n := 2) (t := 156) (b := 24646) rfl rfl ArealUCore.ArealUK.chunk_12322 s23
  have s21 : leavesOK ctxLitU 493825000000 2 ((leaves.drop 24642).take 158) 497775000000 2 = true :=
    take_step (n := 2) (t := 158) (b := 24644) rfl rfl ArealUCore.ArealUK.chunk_12321 s22
  have s20 : leavesOK ctxLitU 493775000000 2 ((leaves.drop 24640).take 160) 497775000000 2 = true :=
    take_step (n := 2) (t := 160) (b := 24642) rfl rfl ArealUCore.ArealUK.chunk_12320 s21
  have s19 : leavesOK ctxLitU 493725000000 2 ((leaves.drop 24638).take 162) 497775000000 2 = true :=
    take_step (n := 2) (t := 162) (b := 24640) rfl rfl ArealUCore.ArealUK.chunk_12319 s20
  have s18 : leavesOK ctxLitU 493675000000 2 ((leaves.drop 24636).take 164) 497775000000 2 = true :=
    take_step (n := 2) (t := 164) (b := 24638) rfl rfl ArealUCore.ArealUK.chunk_12318 s19
  have s17 : leavesOK ctxLitU 493625000000 2 ((leaves.drop 24634).take 166) 497775000000 2 = true :=
    take_step (n := 2) (t := 166) (b := 24636) rfl rfl ArealUCore.ArealUK.chunk_12317 s18
  have s16 : leavesOK ctxLitU 493575000000 2 ((leaves.drop 24632).take 168) 497775000000 2 = true :=
    take_step (n := 2) (t := 168) (b := 24634) rfl rfl ArealUCore.ArealUK.chunk_12316 s17
  have s15 : leavesOK ctxLitU 493525000000 2 ((leaves.drop 24630).take 170) 497775000000 2 = true :=
    take_step (n := 2) (t := 170) (b := 24632) rfl rfl ArealUCore.ArealUK.chunk_12315 s16
  have s14 : leavesOK ctxLitU 493475000000 2 ((leaves.drop 24628).take 172) 497775000000 2 = true :=
    take_step (n := 2) (t := 172) (b := 24630) rfl rfl ArealUCore.ArealUK.chunk_12314 s15
  have s13 : leavesOK ctxLitU 493425000000 2 ((leaves.drop 24626).take 174) 497775000000 2 = true :=
    take_step (n := 2) (t := 174) (b := 24628) rfl rfl ArealUCore.ArealUK.chunk_12313 s14
  have s12 : leavesOK ctxLitU 493375000000 2 ((leaves.drop 24624).take 176) 497775000000 2 = true :=
    take_step (n := 2) (t := 176) (b := 24626) rfl rfl ArealUCore.ArealUK.chunk_12312 s13
  have s11 : leavesOK ctxLitU 493325000000 2 ((leaves.drop 24622).take 178) 497775000000 2 = true :=
    take_step (n := 2) (t := 178) (b := 24624) rfl rfl ArealUCore.ArealUK.chunk_12311 s12
  have s10 : leavesOK ctxLitU 493275000000 2 ((leaves.drop 24620).take 180) 497775000000 2 = true :=
    take_step (n := 2) (t := 180) (b := 24622) rfl rfl ArealUCore.ArealUK.chunk_12310 s11
  have s9 : leavesOK ctxLitU 493225000000 2 ((leaves.drop 24618).take 182) 497775000000 2 = true :=
    take_step (n := 2) (t := 182) (b := 24620) rfl rfl ArealUCore.ArealUK.chunk_12309 s10
  have s8 : leavesOK ctxLitU 493175000000 2 ((leaves.drop 24616).take 184) 497775000000 2 = true :=
    take_step (n := 2) (t := 184) (b := 24618) rfl rfl ArealUCore.ArealUK.chunk_12308 s9
  have s7 : leavesOK ctxLitU 493125000000 2 ((leaves.drop 24614).take 186) 497775000000 2 = true :=
    take_step (n := 2) (t := 186) (b := 24616) rfl rfl ArealUCore.ArealUK.chunk_12307 s8
  have s6 : leavesOK ctxLitU 493075000000 2 ((leaves.drop 24612).take 188) 497775000000 2 = true :=
    take_step (n := 2) (t := 188) (b := 24614) rfl rfl ArealUCore.ArealUK.chunk_12306 s7
  have s5 : leavesOK ctxLitU 493025000000 2 ((leaves.drop 24610).take 190) 497775000000 2 = true :=
    take_step (n := 2) (t := 190) (b := 24612) rfl rfl ArealUCore.ArealUK.chunk_12305 s6
  have s4 : leavesOK ctxLitU 492975000000 2 ((leaves.drop 24608).take 192) 497775000000 2 = true :=
    take_step (n := 2) (t := 192) (b := 24610) rfl rfl ArealUCore.ArealUK.chunk_12304 s5
  have s3 : leavesOK ctxLitU 492925000000 2 ((leaves.drop 24606).take 194) 497775000000 2 = true :=
    take_step (n := 2) (t := 194) (b := 24608) rfl rfl ArealUCore.ArealUK.chunk_12303 s4
  have s2 : leavesOK ctxLitU 492875000000 2 ((leaves.drop 24604).take 196) 497775000000 2 = true :=
    take_step (n := 2) (t := 196) (b := 24606) rfl rfl ArealUCore.ArealUK.chunk_12302 s3
  have s1 : leavesOK ctxLitU 492825000000 2 ((leaves.drop 24602).take 198) 497775000000 2 = true :=
    take_step (n := 2) (t := 198) (b := 24604) rfl rfl ArealUCore.ArealUK.chunk_12301 s2
  have s0 : leavesOK ctxLitU 492775000000 2 ((leaves.drop 24600).take 200) 497775000000 2 = true :=
    take_step (n := 2) (t := 200) (b := 24602) rfl rfl ArealUCore.ArealUK.chunk_12300 s1
  exact s0

end Areal.UCert

import ArealUK.Chunk0300
import ArealUK.Chunk0301
import ArealUK.Chunk0302
import ArealUK.Chunk0303
import ArealUK.Chunk0304
import ArealUK.Chunk0305
import ArealUK.Chunk0306
import ArealUK.Chunk0307
import ArealUK.Chunk0308
import ArealUK.Chunk0309
import ArealUK.Chunk0310
import ArealUK.Chunk0311
import ArealUK.Chunk0312
import ArealUK.Chunk0313
import ArealUK.Chunk0314
import ArealUK.Chunk0315
import ArealUK.Chunk0316
import ArealUK.Chunk0317
import ArealUK.Chunk0318
import ArealUK.Chunk0319
import ArealUK.Chunk0320
import ArealUK.Chunk0321
import ArealUK.Chunk0322
import ArealUK.Chunk0323
import ArealUK.Chunk0324
import ArealUK.Chunk0325
import ArealUK.Chunk0326
import ArealUK.Chunk0327
import ArealUK.Chunk0328
import ArealUK.Chunk0329
import ArealUK.Chunk0330
import ArealUK.Chunk0331
import ArealUK.Chunk0332
import ArealUK.Chunk0333
import ArealUK.Chunk0334
import ArealUK.Chunk0335
import ArealUK.Chunk0336
import ArealUK.Chunk0337
import ArealUK.Chunk0338
import ArealUK.Chunk0339
import ArealUK.Chunk0340
import ArealUK.Chunk0341
import ArealUK.Chunk0342
import ArealUK.Chunk0343
import ArealUK.Chunk0344
import ArealUK.Chunk0345
import ArealUK.Chunk0346
import ArealUK.Chunk0347
import ArealUK.Chunk0348
import ArealUK.Chunk0349
import ArealUK.Chunk0350
import ArealUK.Chunk0351
import ArealUK.Chunk0352
import ArealUK.Chunk0353
import ArealUK.Chunk0354
import ArealUK.Chunk0355
import ArealUK.Chunk0356
import ArealUK.Chunk0357
import ArealUK.Chunk0358
import ArealUK.Chunk0359
import ArealUK.Chunk0360
import ArealUK.Chunk0361
import ArealUK.Chunk0362
import ArealUK.Chunk0363
import ArealUK.Chunk0364
import ArealUK.Chunk0365
import ArealUK.Chunk0366
import ArealUK.Chunk0367
import ArealUK.Chunk0368
import ArealUK.Chunk0369
import ArealUK.Chunk0370
import ArealUK.Chunk0371
import ArealUK.Chunk0372
import ArealUK.Chunk0373
import ArealUK.Chunk0374
import ArealUK.Chunk0375
import ArealUK.Chunk0376
import ArealUK.Chunk0377
import ArealUK.Chunk0378
import ArealUK.Chunk0379
import ArealUK.Chunk0380
import ArealUK.Chunk0381
import ArealUK.Chunk0382
import ArealUK.Chunk0383
import ArealUK.Chunk0384
import ArealUK.Chunk0385
import ArealUK.Chunk0386
import ArealUK.Chunk0387
import ArealUK.Chunk0388
import ArealUK.Chunk0389
import ArealUK.Chunk0390
import ArealUK.Chunk0391
import ArealUK.Chunk0392
import ArealUK.Chunk0393
import ArealUK.Chunk0394
import ArealUK.Chunk0395
import ArealUK.Chunk0396
import ArealUK.Chunk0397
import ArealUK.Chunk0398
import ArealUK.Chunk0399
import Areal.UCert.LeavesKGen

/-! Group 3 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_03 : leavesOK ctxLitU 35825000000 4 ((leaves.drop 600).take 200) 157800000000 6 = true := by
  have s99 := ArealUCore.ArealUK.chunk_0399
  have s98 : leavesOK ctxLitU 19706250000 3 ((leaves.drop 796).take 4) 157800000000 6 = true :=
    take_step (n := 2) (t := 4) (b := 798) rfl rfl ArealUCore.ArealUK.chunk_0398 s99
  have s97 : leavesOK ctxLitU 10083990710011 12 ((leaves.drop 794).take 6) 157800000000 6 = true :=
    take_step (n := 2) (t := 6) (b := 796) rfl rfl ArealUCore.ArealUK.chunk_0397 s98
  have s96 : leavesOK ctxLitU 40312772130024 14 ((leaves.drop 792).take 8) 157800000000 6 = true :=
    take_step (n := 2) (t := 8) (b := 794) rfl rfl ArealUCore.ArealUK.chunk_0396 s97
  have s95 : leavesOK ctxLitU 80555972130024 15 ((leaves.drop 790).take 10) 157800000000 6 = true :=
    take_step (n := 2) (t := 10) (b := 792) rfl rfl ArealUCore.ArealUK.chunk_0395 s96
  have s94 : leavesOK ctxLitU 161042372130024 16 ((leaves.drop 788).take 12) 157800000000 6 = true :=
    take_step (n := 2) (t := 12) (b := 790) rfl rfl ArealUCore.ArealUK.chunk_0394 s95
  have s93 : leavesOK ctxLitU 322038362840032 17 ((leaves.drop 786).take 14) 157800000000 6 = true :=
    take_step (n := 2) (t := 14) (b := 788) rfl rfl ArealUCore.ArealUK.chunk_0393 s94
  have s92 : leavesOK ctxLitU 19643750000 3 ((leaves.drop 784).take 16) 157800000000 6 = true :=
    take_step (n := 2) (t := 16) (b := 786) rfl rfl ArealUCore.ArealUK.chunk_0392 s93
  have s91 : leavesOK ctxLitU 39268750000 4 ((leaves.drop 782).take 18) 157800000000 6 = true :=
    take_step (n := 2) (t := 18) (b := 784) rfl rfl ArealUCore.ArealUK.chunk_0391 s92
  have s90 : leavesOK ctxLitU 39256250000 4 ((leaves.drop 780).take 20) 157800000000 6 = true :=
    take_step (n := 2) (t := 20) (b := 782) rfl rfl ArealUCore.ArealUK.chunk_0390 s91
  have s89 : leavesOK ctxLitU 78500000000 5 ((leaves.drop 778).take 22) 157800000000 6 = true :=
    take_step (n := 2) (t := 22) (b := 780) rfl rfl ArealUCore.ArealUK.chunk_0389 s90
  have s88 : leavesOK ctxLitU 78487500000 5 ((leaves.drop 776).take 24) 157800000000 6 = true :=
    take_step (n := 2) (t := 24) (b := 778) rfl rfl ArealUCore.ArealUK.chunk_0388 s89
  have s87 : leavesOK ctxLitU 19612500000 3 ((leaves.drop 774).take 26) 157800000000 6 = true :=
    take_step (n := 2) (t := 26) (b := 776) rfl rfl ArealUCore.ArealUK.chunk_0387 s88
  have s86 : leavesOK ctxLitU 19600000000 3 ((leaves.drop 772).take 28) 157800000000 6 = true :=
    take_step (n := 2) (t := 28) (b := 774) rfl rfl ArealUCore.ArealUK.chunk_0386 s87
  have s85 : leavesOK ctxLitU 19587500000 3 ((leaves.drop 770).take 30) 157800000000 6 = true :=
    take_step (n := 2) (t := 30) (b := 772) rfl rfl ArealUCore.ArealUK.chunk_0385 s86
  have s84 : leavesOK ctxLitU 19575000000 3 ((leaves.drop 768).take 32) 157800000000 6 = true :=
    take_step (n := 2) (t := 32) (b := 770) rfl rfl ArealUCore.ArealUK.chunk_0384 s85
  have s83 : leavesOK ctxLitU 19562500000 3 ((leaves.drop 766).take 34) 157800000000 6 = true :=
    take_step (n := 2) (t := 34) (b := 768) rfl rfl ArealUCore.ArealUK.chunk_0383 s84
  have s82 : leavesOK ctxLitU 19550000000 3 ((leaves.drop 764).take 36) 157800000000 6 = true :=
    take_step (n := 2) (t := 36) (b := 766) rfl rfl ArealUCore.ArealUK.chunk_0382 s83
  have s81 : leavesOK ctxLitU 19537500000 3 ((leaves.drop 762).take 38) 157800000000 6 = true :=
    take_step (n := 2) (t := 38) (b := 764) rfl rfl ArealUCore.ArealUK.chunk_0381 s82
  have s80 : leavesOK ctxLitU 39062500000 4 ((leaves.drop 760).take 40) 157800000000 6 = true :=
    take_step (n := 2) (t := 40) (b := 762) rfl rfl ArealUCore.ArealUK.chunk_0380 s81
  have s79 : leavesOK ctxLitU 39050000000 4 ((leaves.drop 758).take 42) 157800000000 6 = true :=
    take_step (n := 2) (t := 42) (b := 760) rfl rfl ArealUCore.ArealUK.chunk_0379 s80
  have s78 : leavesOK ctxLitU 39037500000 4 ((leaves.drop 756).take 44) 157800000000 6 = true :=
    take_step (n := 2) (t := 44) (b := 758) rfl rfl ArealUCore.ArealUK.chunk_0378 s79
  have s77 : leavesOK ctxLitU 39025000000 4 ((leaves.drop 754).take 46) 157800000000 6 = true :=
    take_step (n := 2) (t := 46) (b := 756) rfl rfl ArealUCore.ArealUK.chunk_0377 s78
  have s76 : leavesOK ctxLitU 19500000000 3 ((leaves.drop 752).take 48) 157800000000 6 = true :=
    take_step (n := 2) (t := 48) (b := 754) rfl rfl ArealUCore.ArealUK.chunk_0376 s77
  have s75 : leavesOK ctxLitU 19487500000 3 ((leaves.drop 750).take 50) 157800000000 6 = true :=
    take_step (n := 2) (t := 50) (b := 752) rfl rfl ArealUCore.ArealUK.chunk_0375 s76
  have s74 : leavesOK ctxLitU 19475000000 3 ((leaves.drop 748).take 52) 157800000000 6 = true :=
    take_step (n := 2) (t := 52) (b := 750) rfl rfl ArealUCore.ArealUK.chunk_0374 s75
  have s73 : leavesOK ctxLitU 19462500000 3 ((leaves.drop 746).take 54) 157800000000 6 = true :=
    take_step (n := 2) (t := 54) (b := 748) rfl rfl ArealUCore.ArealUK.chunk_0373 s74
  have s72 : leavesOK ctxLitU 19450000000 3 ((leaves.drop 744).take 56) 157800000000 6 = true :=
    take_step (n := 2) (t := 56) (b := 746) rfl rfl ArealUCore.ArealUK.chunk_0372 s73
  have s71 : leavesOK ctxLitU 19437500000 3 ((leaves.drop 742).take 58) 157800000000 6 = true :=
    take_step (n := 2) (t := 58) (b := 744) rfl rfl ArealUCore.ArealUK.chunk_0371 s72
  have s70 : leavesOK ctxLitU 19425000000 3 ((leaves.drop 740).take 60) 157800000000 6 = true :=
    take_step (n := 2) (t := 60) (b := 742) rfl rfl ArealUCore.ArealUK.chunk_0370 s71
  have s69 : leavesOK ctxLitU 19412500000 3 ((leaves.drop 738).take 62) 157800000000 6 = true :=
    take_step (n := 2) (t := 62) (b := 740) rfl rfl ArealUCore.ArealUK.chunk_0369 s70
  have s68 : leavesOK ctxLitU 19400000000 3 ((leaves.drop 736).take 64) 157800000000 6 = true :=
    take_step (n := 2) (t := 64) (b := 738) rfl rfl ArealUCore.ArealUK.chunk_0368 s69
  have s67 : leavesOK ctxLitU 19387500000 3 ((leaves.drop 734).take 66) 157800000000 6 = true :=
    take_step (n := 2) (t := 66) (b := 736) rfl rfl ArealUCore.ArealUK.chunk_0367 s68
  have s66 : leavesOK ctxLitU 19375000000 3 ((leaves.drop 732).take 68) 157800000000 6 = true :=
    take_step (n := 2) (t := 68) (b := 734) rfl rfl ArealUCore.ArealUK.chunk_0366 s67
  have s65 : leavesOK ctxLitU 19362500000 3 ((leaves.drop 730).take 70) 157800000000 6 = true :=
    take_step (n := 2) (t := 70) (b := 732) rfl rfl ArealUCore.ArealUK.chunk_0365 s66
  have s64 : leavesOK ctxLitU 19350000000 3 ((leaves.drop 728).take 72) 157800000000 6 = true :=
    take_step (n := 2) (t := 72) (b := 730) rfl rfl ArealUCore.ArealUK.chunk_0364 s65
  have s63 : leavesOK ctxLitU 19337500000 3 ((leaves.drop 726).take 74) 157800000000 6 = true :=
    take_step (n := 2) (t := 74) (b := 728) rfl rfl ArealUCore.ArealUK.chunk_0363 s64
  have s62 : leavesOK ctxLitU 19325000000 3 ((leaves.drop 724).take 76) 157800000000 6 = true :=
    take_step (n := 2) (t := 76) (b := 726) rfl rfl ArealUCore.ArealUK.chunk_0362 s63
  have s61 : leavesOK ctxLitU 19312500000 3 ((leaves.drop 722).take 78) 157800000000 6 = true :=
    take_step (n := 2) (t := 78) (b := 724) rfl rfl ArealUCore.ArealUK.chunk_0361 s62
  have s60 : leavesOK ctxLitU 19300000000 3 ((leaves.drop 720).take 80) 157800000000 6 = true :=
    take_step (n := 2) (t := 80) (b := 722) rfl rfl ArealUCore.ArealUK.chunk_0360 s61
  have s59 : leavesOK ctxLitU 9637500000 2 ((leaves.drop 718).take 82) 157800000000 6 = true :=
    take_step (n := 2) (t := 82) (b := 720) rfl rfl ArealUCore.ArealUK.chunk_0359 s60
  have s58 : leavesOK ctxLitU 9625000000 2 ((leaves.drop 716).take 84) 157800000000 6 = true :=
    take_step (n := 2) (t := 84) (b := 718) rfl rfl ArealUCore.ArealUK.chunk_0358 s59
  have s57 : leavesOK ctxLitU 9612500000 2 ((leaves.drop 714).take 86) 157800000000 6 = true :=
    take_step (n := 2) (t := 86) (b := 716) rfl rfl ArealUCore.ArealUK.chunk_0357 s58
  have s56 : leavesOK ctxLitU 38431250000 4 ((leaves.drop 712).take 88) 157800000000 6 = true :=
    take_step (n := 2) (t := 88) (b := 714) rfl rfl ArealUCore.ArealUK.chunk_0356 s57
  have s55 : leavesOK ctxLitU 19206250000 3 ((leaves.drop 710).take 90) 157800000000 6 = true :=
    take_step (n := 2) (t := 90) (b := 712) rfl rfl ArealUCore.ArealUK.chunk_0355 s56
  have s54 : leavesOK ctxLitU 19643550244296 13 ((leaves.drop 708).take 92) 157800000000 6 = true :=
    take_step (n := 2) (t := 92) (b := 710) rfl rfl ArealUCore.ArealUK.chunk_0354 s55
  have s53 : leavesOK ctxLitU 9813150244293 12 ((leaves.drop 706).take 94) 157800000000 6 = true :=
    take_step (n := 2) (t := 94) (b := 708) rfl rfl ArealUCore.ArealUK.chunk_0353 s54
  have s52 : leavesOK ctxLitU 39195881564782 14 ((leaves.drop 704).take 96) 157800000000 6 = true :=
    take_step (n := 2) (t := 96) (b := 706) rfl rfl ArealUCore.ArealUK.chunk_0352 s53
  have s51 : leavesOK ctxLitU 9784790538095 12 ((leaves.drop 702).take 98) 157800000000 6 = true :=
    take_step (n := 2) (t := 98) (b := 704) rfl rfl ArealUCore.ArealUK.chunk_0351 s52
  have s50 : leavesOK ctxLitU 19087500000 3 ((leaves.drop 700).take 100) 157800000000 6 = true :=
    take_step (n := 2) (t := 100) (b := 702) rfl rfl ArealUCore.ArealUK.chunk_0350 s51
  have s49 : leavesOK ctxLitU 19062500000 3 ((leaves.drop 698).take 102) 157800000000 6 = true :=
    take_step (n := 2) (t := 102) (b := 700) rfl rfl ArealUCore.ArealUK.chunk_0349 s50
  have s48 : leavesOK ctxLitU 38100000000 4 ((leaves.drop 696).take 104) 157800000000 6 = true :=
    take_step (n := 2) (t := 104) (b := 698) rfl rfl ArealUCore.ArealUK.chunk_0348 s49
  have s47 : leavesOK ctxLitU 38075000000 4 ((leaves.drop 694).take 106) 157800000000 6 = true :=
    take_step (n := 2) (t := 106) (b := 696) rfl rfl ArealUCore.ArealUK.chunk_0347 s48
  have s46 : leavesOK ctxLitU 9500000000 2 ((leaves.drop 692).take 108) 157800000000 6 = true :=
    take_step (n := 2) (t := 108) (b := 694) rfl rfl ArealUCore.ArealUK.chunk_0346 s47
  have s45 : leavesOK ctxLitU 9481250000 2 ((leaves.drop 690).take 110) 157800000000 6 = true :=
    take_step (n := 2) (t := 110) (b := 692) rfl rfl ArealUCore.ArealUK.chunk_0345 s46
  have s44 : leavesOK ctxLitU 18950000000 3 ((leaves.drop 688).take 112) 157800000000 6 = true :=
    take_step (n := 2) (t := 112) (b := 690) rfl rfl ArealUCore.ArealUK.chunk_0344 s45
  have s43 : leavesOK ctxLitU 75787500000 5 ((leaves.drop 686).take 114) 157800000000 6 = true :=
    take_step (n := 2) (t := 114) (b := 688) rfl rfl ArealUCore.ArealUK.chunk_0343 s44
  have s42 : leavesOK ctxLitU 18937500000 3 ((leaves.drop 684).take 116) 157800000000 6 = true :=
    take_step (n := 2) (t := 116) (b := 686) rfl rfl ArealUCore.ArealUK.chunk_0342 s43
  have s41 : leavesOK ctxLitU 18925000000 3 ((leaves.drop 682).take 118) 157800000000 6 = true :=
    take_step (n := 2) (t := 118) (b := 684) rfl rfl ArealUCore.ArealUK.chunk_0341 s42
  have s40 : leavesOK ctxLitU 9450000000 2 ((leaves.drop 680).take 120) 157800000000 6 = true :=
    take_step (n := 2) (t := 120) (b := 682) rfl rfl ArealUCore.ArealUK.chunk_0340 s41
  have s39 : leavesOK ctxLitU 9437500000 2 ((leaves.drop 678).take 122) 157800000000 6 = true :=
    take_step (n := 2) (t := 122) (b := 680) rfl rfl ArealUCore.ArealUK.chunk_0339 s40
  have s38 : leavesOK ctxLitU 18862500000 3 ((leaves.drop 676).take 124) 157800000000 6 = true :=
    take_step (n := 2) (t := 124) (b := 678) rfl rfl ArealUCore.ArealUK.chunk_0338 s39
  have s37 : leavesOK ctxLitU 37706250000 4 ((leaves.drop 674).take 126) 157800000000 6 = true :=
    take_step (n := 2) (t := 126) (b := 676) rfl rfl ArealUCore.ArealUK.chunk_0337 s38
  have s36 : leavesOK ctxLitU 9418750000 2 ((leaves.drop 672).take 128) 157800000000 6 = true :=
    take_step (n := 2) (t := 128) (b := 674) rfl rfl ArealUCore.ArealUK.chunk_0336 s37
  have s35 : leavesOK ctxLitU 4700000000 1 ((leaves.drop 670).take 130) 157800000000 6 = true :=
    take_step (n := 2) (t := 130) (b := 672) rfl rfl ArealUCore.ArealUK.chunk_0335 s36
  have s34 : leavesOK ctxLitU 9613315465238 12 ((leaves.drop 668).take 132) 157800000000 6 = true :=
    take_step (n := 2) (t := 132) (b := 670) rfl rfl ArealUCore.ArealUK.chunk_0334 s35
  have s33 : leavesOK ctxLitU 18743750000 3 ((leaves.drop 666).take 134) 157800000000 6 = true :=
    take_step (n := 2) (t := 134) (b := 668) rfl rfl ArealUCore.ArealUK.chunk_0333 s34
  have s32 : leavesOK ctxLitU 9362500000 2 ((leaves.drop 664).take 136) 157800000000 6 = true :=
    take_step (n := 2) (t := 136) (b := 666) rfl rfl ArealUCore.ArealUK.chunk_0332 s33
  have s31 : leavesOK ctxLitU 9350000000 2 ((leaves.drop 662).take 138) 157800000000 6 = true :=
    take_step (n := 2) (t := 138) (b := 664) rfl rfl ArealUCore.ArealUK.chunk_0331 s32
  have s30 : leavesOK ctxLitU 18687500000 3 ((leaves.drop 660).take 140) 157800000000 6 = true :=
    take_step (n := 2) (t := 140) (b := 662) rfl rfl ArealUCore.ArealUK.chunk_0330 s31
  have s29 : leavesOK ctxLitU 37362500000 4 ((leaves.drop 658).take 142) 157800000000 6 = true :=
    take_step (n := 2) (t := 142) (b := 660) rfl rfl ArealUCore.ArealUK.chunk_0329 s30
  have s28 : leavesOK ctxLitU 18668750000 3 ((leaves.drop 656).take 144) 157800000000 6 = true :=
    take_step (n := 2) (t := 144) (b := 658) rfl rfl ArealUCore.ArealUK.chunk_0328 s29
  have s27 : leavesOK ctxLitU 18656250000 3 ((leaves.drop 654).take 146) 157800000000 6 = true :=
    take_step (n := 2) (t := 146) (b := 656) rfl rfl ArealUCore.ArealUK.chunk_0327 s28
  have s26 : leavesOK ctxLitU 18643750000 3 ((leaves.drop 652).take 148) 157800000000 6 = true :=
    take_step (n := 2) (t := 148) (b := 654) rfl rfl ArealUCore.ArealUK.chunk_0326 s27
  have s25 : leavesOK ctxLitU 18631250000 3 ((leaves.drop 650).take 150) 157800000000 6 = true :=
    take_step (n := 2) (t := 150) (b := 652) rfl rfl ArealUCore.ArealUK.chunk_0325 s26
  have s24 : leavesOK ctxLitU 37250000000 4 ((leaves.drop 648).take 152) 157800000000 6 = true :=
    take_step (n := 2) (t := 152) (b := 650) rfl rfl ArealUCore.ArealUK.chunk_0324 s25
  have s23 : leavesOK ctxLitU 37237500000 4 ((leaves.drop 646).take 154) 157800000000 6 = true :=
    take_step (n := 2) (t := 154) (b := 648) rfl rfl ArealUCore.ArealUK.chunk_0323 s24
  have s22 : leavesOK ctxLitU 37225000000 4 ((leaves.drop 644).take 156) 157800000000 6 = true :=
    take_step (n := 2) (t := 156) (b := 646) rfl rfl ArealUCore.ArealUK.chunk_0322 s23
  have s21 : leavesOK ctxLitU 18600000000 3 ((leaves.drop 642).take 158) 157800000000 6 = true :=
    take_step (n := 2) (t := 158) (b := 644) rfl rfl ArealUCore.ArealUK.chunk_0321 s22
  have s20 : leavesOK ctxLitU 37181250000 4 ((leaves.drop 640).take 160) 157800000000 6 = true :=
    take_step (n := 2) (t := 160) (b := 642) rfl rfl ArealUCore.ArealUK.chunk_0320 s21
  have s19 : leavesOK ctxLitU 18581250000 3 ((leaves.drop 638).take 162) 157800000000 6 = true :=
    take_step (n := 2) (t := 162) (b := 640) rfl rfl ArealUCore.ArealUK.chunk_0319 s20
  have s18 : leavesOK ctxLitU 9281250000 2 ((leaves.drop 636).take 164) 157800000000 6 = true :=
    take_step (n := 2) (t := 164) (b := 638) rfl rfl ArealUCore.ArealUK.chunk_0318 s19
  have s17 : leavesOK ctxLitU 9491618732943 12 ((leaves.drop 634).take 166) 157800000000 6 = true :=
    take_step (n := 2) (t := 166) (b := 636) rfl rfl ArealUCore.ArealUK.chunk_0317 s18
  have s16 : leavesOK ctxLitU 18963618732940 13 ((leaves.drop 632).take 168) 157800000000 6 = true :=
    take_step (n := 2) (t := 168) (b := 634) rfl rfl ArealUCore.ArealUK.chunk_0316 s17
  have s15 : leavesOK ctxLitU 151610856198820 16 ((leaves.drop 630).take 170) 157800000000 6 = true :=
    take_step (n := 2) (t := 170) (b := 632) rfl rfl ArealUCore.ArealUK.chunk_0315 s16
  have s14 : leavesOK ctxLitU 303162856198820 17 ((leaves.drop 628).take 172) 157800000000 6 = true :=
    take_step (n := 2) (t := 172) (b := 630) rfl rfl ArealUCore.ArealUK.chunk_0314 s15
  have s13 : leavesOK ctxLitU 303123618732940 17 ((leaves.drop 626).take 174) 157800000000 6 = true :=
    take_step (n := 2) (t := 174) (b := 628) rfl rfl ArealUCore.ArealUK.chunk_0313 s14
  have s12 : leavesOK ctxLitU 18493750000 3 ((leaves.drop 624).take 176) 157800000000 6 = true :=
    take_step (n := 2) (t := 176) (b := 626) rfl rfl ArealUCore.ArealUK.chunk_0312 s13
  have s11 : leavesOK ctxLitU 9237500000 2 ((leaves.drop 622).take 178) 157800000000 6 = true :=
    take_step (n := 2) (t := 178) (b := 624) rfl rfl ArealUCore.ArealUK.chunk_0311 s12
  have s10 : leavesOK ctxLitU 2300000000 0 ((leaves.drop 620).take 180) 157800000000 6 = true :=
    take_step (n := 2) (t := 180) (b := 622) rfl rfl ArealUCore.ArealUK.chunk_0310 s11
  have s9 : leavesOK ctxLitU 2287500000 0 ((leaves.drop 618).take 182) 157800000000 6 = true :=
    take_step (n := 2) (t := 182) (b := 620) rfl rfl ArealUCore.ArealUK.chunk_0309 s10
  have s8 : leavesOK ctxLitU 9329750189442 12 ((leaves.drop 616).take 184) 157800000000 6 = true :=
    take_step (n := 2) (t := 184) (b := 618) rfl rfl ArealUCore.ArealUK.chunk_0308 s9
  have s7 : leavesOK ctxLitU 9318400000000 12 ((leaves.drop 614).take 186) 157800000000 6 = true :=
    take_step (n := 2) (t := 186) (b := 616) rfl rfl ArealUCore.ArealUK.chunk_0307 s8
  have s6 : leavesOK ctxLitU 2262500000 0 ((leaves.drop 612).take 188) 157800000000 6 = true :=
    take_step (n := 2) (t := 188) (b := 614) rfl rfl ArealUCore.ArealUK.chunk_0306 s7
  have s5 : leavesOK ctxLitU 2250000000 0 ((leaves.drop 610).take 190) 157800000000 6 = true :=
    take_step (n := 2) (t := 190) (b := 612) rfl rfl ArealUCore.ArealUK.chunk_0305 s6
  have s4 : leavesOK ctxLitU 8981250000 2 ((leaves.drop 608).take 192) 157800000000 6 = true :=
    take_step (n := 2) (t := 192) (b := 610) rfl rfl ArealUCore.ArealUK.chunk_0304 s5
  have s3 : leavesOK ctxLitU 17943750000 3 ((leaves.drop 606).take 194) 157800000000 6 = true :=
    take_step (n := 2) (t := 194) (b := 608) rfl rfl ArealUCore.ArealUK.chunk_0303 s4
  have s2 : leavesOK ctxLitU 17931250000 3 ((leaves.drop 604).take 196) 157800000000 6 = true :=
    take_step (n := 2) (t := 196) (b := 606) rfl rfl ArealUCore.ArealUK.chunk_0302 s3
  have s1 : leavesOK ctxLitU 17918750000 3 ((leaves.drop 602).take 198) 157800000000 6 = true :=
    take_step (n := 2) (t := 198) (b := 604) rfl rfl ArealUCore.ArealUK.chunk_0301 s2
  have s0 : leavesOK ctxLitU 35825000000 4 ((leaves.drop 600).take 200) 157800000000 6 = true :=
    take_step (n := 2) (t := 200) (b := 602) rfl rfl ArealUCore.ArealUK.chunk_0300 s1
  exact s0

end Areal.UCert

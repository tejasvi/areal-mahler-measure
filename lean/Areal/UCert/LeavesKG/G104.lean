import ArealUK.Chunk10400
import ArealUK.Chunk10401
import ArealUK.Chunk10402
import ArealUK.Chunk10403
import ArealUK.Chunk10404
import ArealUK.Chunk10405
import ArealUK.Chunk10406
import ArealUK.Chunk10407
import ArealUK.Chunk10408
import ArealUK.Chunk10409
import ArealUK.Chunk10410
import ArealUK.Chunk10411
import ArealUK.Chunk10412
import ArealUK.Chunk10413
import ArealUK.Chunk10414
import ArealUK.Chunk10415
import ArealUK.Chunk10416
import ArealUK.Chunk10417
import ArealUK.Chunk10418
import ArealUK.Chunk10419
import ArealUK.Chunk10420
import ArealUK.Chunk10421
import ArealUK.Chunk10422
import ArealUK.Chunk10423
import ArealUK.Chunk10424
import ArealUK.Chunk10425
import ArealUK.Chunk10426
import ArealUK.Chunk10427
import ArealUK.Chunk10428
import ArealUK.Chunk10429
import ArealUK.Chunk10430
import ArealUK.Chunk10431
import ArealUK.Chunk10432
import ArealUK.Chunk10433
import ArealUK.Chunk10434
import ArealUK.Chunk10435
import ArealUK.Chunk10436
import ArealUK.Chunk10437
import ArealUK.Chunk10438
import ArealUK.Chunk10439
import ArealUK.Chunk10440
import ArealUK.Chunk10441
import ArealUK.Chunk10442
import ArealUK.Chunk10443
import ArealUK.Chunk10444
import ArealUK.Chunk10445
import ArealUK.Chunk10446
import ArealUK.Chunk10447
import ArealUK.Chunk10448
import ArealUK.Chunk10449
import ArealUK.Chunk10450
import ArealUK.Chunk10451
import ArealUK.Chunk10452
import ArealUK.Chunk10453
import ArealUK.Chunk10454
import ArealUK.Chunk10455
import ArealUK.Chunk10456
import ArealUK.Chunk10457
import ArealUK.Chunk10458
import ArealUK.Chunk10459
import ArealUK.Chunk10460
import ArealUK.Chunk10461
import ArealUK.Chunk10462
import ArealUK.Chunk10463
import ArealUK.Chunk10464
import ArealUK.Chunk10465
import ArealUK.Chunk10466
import ArealUK.Chunk10467
import ArealUK.Chunk10468
import ArealUK.Chunk10469
import ArealUK.Chunk10470
import ArealUK.Chunk10471
import ArealUK.Chunk10472
import ArealUK.Chunk10473
import ArealUK.Chunk10474
import ArealUK.Chunk10475
import ArealUK.Chunk10476
import ArealUK.Chunk10477
import ArealUK.Chunk10478
import ArealUK.Chunk10479
import ArealUK.Chunk10480
import ArealUK.Chunk10481
import ArealUK.Chunk10482
import ArealUK.Chunk10483
import ArealUK.Chunk10484
import ArealUK.Chunk10485
import ArealUK.Chunk10486
import ArealUK.Chunk10487
import ArealUK.Chunk10488
import ArealUK.Chunk10489
import ArealUK.Chunk10490
import ArealUK.Chunk10491
import ArealUK.Chunk10492
import ArealUK.Chunk10493
import ArealUK.Chunk10494
import ArealUK.Chunk10495
import ArealUK.Chunk10496
import ArealUK.Chunk10497
import ArealUK.Chunk10498
import ArealUK.Chunk10499
import Areal.UCert.LeavesKGen

/-! Group 104 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_104 : leavesOK ctxLitU 377150000000 2 ((leaves.drop 20800).take 200) 382150000000 2 = true := by
  have s99 := ArealUCore.ArealUK.chunk_10499
  have s98 : leavesOK ctxLitU 382050000000 2 ((leaves.drop 20996).take 4) 382150000000 2 = true :=
    take_step (n := 2) (t := 4) (b := 20998) rfl rfl ArealUCore.ArealUK.chunk_10498 s99
  have s97 : leavesOK ctxLitU 382000000000 2 ((leaves.drop 20994).take 6) 382150000000 2 = true :=
    take_step (n := 2) (t := 6) (b := 20996) rfl rfl ArealUCore.ArealUK.chunk_10497 s98
  have s96 : leavesOK ctxLitU 381950000000 2 ((leaves.drop 20992).take 8) 382150000000 2 = true :=
    take_step (n := 2) (t := 8) (b := 20994) rfl rfl ArealUCore.ArealUK.chunk_10496 s97
  have s95 : leavesOK ctxLitU 381900000000 2 ((leaves.drop 20990).take 10) 382150000000 2 = true :=
    take_step (n := 2) (t := 10) (b := 20992) rfl rfl ArealUCore.ArealUK.chunk_10495 s96
  have s94 : leavesOK ctxLitU 381850000000 2 ((leaves.drop 20988).take 12) 382150000000 2 = true :=
    take_step (n := 2) (t := 12) (b := 20990) rfl rfl ArealUCore.ArealUK.chunk_10494 s95
  have s93 : leavesOK ctxLitU 381800000000 2 ((leaves.drop 20986).take 14) 382150000000 2 = true :=
    take_step (n := 2) (t := 14) (b := 20988) rfl rfl ArealUCore.ArealUK.chunk_10493 s94
  have s92 : leavesOK ctxLitU 381750000000 2 ((leaves.drop 20984).take 16) 382150000000 2 = true :=
    take_step (n := 2) (t := 16) (b := 20986) rfl rfl ArealUCore.ArealUK.chunk_10492 s93
  have s91 : leavesOK ctxLitU 381700000000 2 ((leaves.drop 20982).take 18) 382150000000 2 = true :=
    take_step (n := 2) (t := 18) (b := 20984) rfl rfl ArealUCore.ArealUK.chunk_10491 s92
  have s90 : leavesOK ctxLitU 381650000000 2 ((leaves.drop 20980).take 20) 382150000000 2 = true :=
    take_step (n := 2) (t := 20) (b := 20982) rfl rfl ArealUCore.ArealUK.chunk_10490 s91
  have s89 : leavesOK ctxLitU 381600000000 2 ((leaves.drop 20978).take 22) 382150000000 2 = true :=
    take_step (n := 2) (t := 22) (b := 20980) rfl rfl ArealUCore.ArealUK.chunk_10489 s90
  have s88 : leavesOK ctxLitU 381550000000 2 ((leaves.drop 20976).take 24) 382150000000 2 = true :=
    take_step (n := 2) (t := 24) (b := 20978) rfl rfl ArealUCore.ArealUK.chunk_10488 s89
  have s87 : leavesOK ctxLitU 381500000000 2 ((leaves.drop 20974).take 26) 382150000000 2 = true :=
    take_step (n := 2) (t := 26) (b := 20976) rfl rfl ArealUCore.ArealUK.chunk_10487 s88
  have s86 : leavesOK ctxLitU 381450000000 2 ((leaves.drop 20972).take 28) 382150000000 2 = true :=
    take_step (n := 2) (t := 28) (b := 20974) rfl rfl ArealUCore.ArealUK.chunk_10486 s87
  have s85 : leavesOK ctxLitU 381400000000 2 ((leaves.drop 20970).take 30) 382150000000 2 = true :=
    take_step (n := 2) (t := 30) (b := 20972) rfl rfl ArealUCore.ArealUK.chunk_10485 s86
  have s84 : leavesOK ctxLitU 381350000000 2 ((leaves.drop 20968).take 32) 382150000000 2 = true :=
    take_step (n := 2) (t := 32) (b := 20970) rfl rfl ArealUCore.ArealUK.chunk_10484 s85
  have s83 : leavesOK ctxLitU 381300000000 2 ((leaves.drop 20966).take 34) 382150000000 2 = true :=
    take_step (n := 2) (t := 34) (b := 20968) rfl rfl ArealUCore.ArealUK.chunk_10483 s84
  have s82 : leavesOK ctxLitU 381250000000 2 ((leaves.drop 20964).take 36) 382150000000 2 = true :=
    take_step (n := 2) (t := 36) (b := 20966) rfl rfl ArealUCore.ArealUK.chunk_10482 s83
  have s81 : leavesOK ctxLitU 381200000000 2 ((leaves.drop 20962).take 38) 382150000000 2 = true :=
    take_step (n := 2) (t := 38) (b := 20964) rfl rfl ArealUCore.ArealUK.chunk_10481 s82
  have s80 : leavesOK ctxLitU 381150000000 2 ((leaves.drop 20960).take 40) 382150000000 2 = true :=
    take_step (n := 2) (t := 40) (b := 20962) rfl rfl ArealUCore.ArealUK.chunk_10480 s81
  have s79 : leavesOK ctxLitU 381100000000 2 ((leaves.drop 20958).take 42) 382150000000 2 = true :=
    take_step (n := 2) (t := 42) (b := 20960) rfl rfl ArealUCore.ArealUK.chunk_10479 s80
  have s78 : leavesOK ctxLitU 381050000000 2 ((leaves.drop 20956).take 44) 382150000000 2 = true :=
    take_step (n := 2) (t := 44) (b := 20958) rfl rfl ArealUCore.ArealUK.chunk_10478 s79
  have s77 : leavesOK ctxLitU 381000000000 2 ((leaves.drop 20954).take 46) 382150000000 2 = true :=
    take_step (n := 2) (t := 46) (b := 20956) rfl rfl ArealUCore.ArealUK.chunk_10477 s78
  have s76 : leavesOK ctxLitU 380950000000 2 ((leaves.drop 20952).take 48) 382150000000 2 = true :=
    take_step (n := 2) (t := 48) (b := 20954) rfl rfl ArealUCore.ArealUK.chunk_10476 s77
  have s75 : leavesOK ctxLitU 380900000000 2 ((leaves.drop 20950).take 50) 382150000000 2 = true :=
    take_step (n := 2) (t := 50) (b := 20952) rfl rfl ArealUCore.ArealUK.chunk_10475 s76
  have s74 : leavesOK ctxLitU 380850000000 2 ((leaves.drop 20948).take 52) 382150000000 2 = true :=
    take_step (n := 2) (t := 52) (b := 20950) rfl rfl ArealUCore.ArealUK.chunk_10474 s75
  have s73 : leavesOK ctxLitU 380800000000 2 ((leaves.drop 20946).take 54) 382150000000 2 = true :=
    take_step (n := 2) (t := 54) (b := 20948) rfl rfl ArealUCore.ArealUK.chunk_10473 s74
  have s72 : leavesOK ctxLitU 380750000000 2 ((leaves.drop 20944).take 56) 382150000000 2 = true :=
    take_step (n := 2) (t := 56) (b := 20946) rfl rfl ArealUCore.ArealUK.chunk_10472 s73
  have s71 : leavesOK ctxLitU 380700000000 2 ((leaves.drop 20942).take 58) 382150000000 2 = true :=
    take_step (n := 2) (t := 58) (b := 20944) rfl rfl ArealUCore.ArealUK.chunk_10471 s72
  have s70 : leavesOK ctxLitU 380650000000 2 ((leaves.drop 20940).take 60) 382150000000 2 = true :=
    take_step (n := 2) (t := 60) (b := 20942) rfl rfl ArealUCore.ArealUK.chunk_10470 s71
  have s69 : leavesOK ctxLitU 380600000000 2 ((leaves.drop 20938).take 62) 382150000000 2 = true :=
    take_step (n := 2) (t := 62) (b := 20940) rfl rfl ArealUCore.ArealUK.chunk_10469 s70
  have s68 : leavesOK ctxLitU 380550000000 2 ((leaves.drop 20936).take 64) 382150000000 2 = true :=
    take_step (n := 2) (t := 64) (b := 20938) rfl rfl ArealUCore.ArealUK.chunk_10468 s69
  have s67 : leavesOK ctxLitU 380500000000 2 ((leaves.drop 20934).take 66) 382150000000 2 = true :=
    take_step (n := 2) (t := 66) (b := 20936) rfl rfl ArealUCore.ArealUK.chunk_10467 s68
  have s66 : leavesOK ctxLitU 380450000000 2 ((leaves.drop 20932).take 68) 382150000000 2 = true :=
    take_step (n := 2) (t := 68) (b := 20934) rfl rfl ArealUCore.ArealUK.chunk_10466 s67
  have s65 : leavesOK ctxLitU 380400000000 2 ((leaves.drop 20930).take 70) 382150000000 2 = true :=
    take_step (n := 2) (t := 70) (b := 20932) rfl rfl ArealUCore.ArealUK.chunk_10465 s66
  have s64 : leavesOK ctxLitU 380350000000 2 ((leaves.drop 20928).take 72) 382150000000 2 = true :=
    take_step (n := 2) (t := 72) (b := 20930) rfl rfl ArealUCore.ArealUK.chunk_10464 s65
  have s63 : leavesOK ctxLitU 380300000000 2 ((leaves.drop 20926).take 74) 382150000000 2 = true :=
    take_step (n := 2) (t := 74) (b := 20928) rfl rfl ArealUCore.ArealUK.chunk_10463 s64
  have s62 : leavesOK ctxLitU 380250000000 2 ((leaves.drop 20924).take 76) 382150000000 2 = true :=
    take_step (n := 2) (t := 76) (b := 20926) rfl rfl ArealUCore.ArealUK.chunk_10462 s63
  have s61 : leavesOK ctxLitU 380200000000 2 ((leaves.drop 20922).take 78) 382150000000 2 = true :=
    take_step (n := 2) (t := 78) (b := 20924) rfl rfl ArealUCore.ArealUK.chunk_10461 s62
  have s60 : leavesOK ctxLitU 380150000000 2 ((leaves.drop 20920).take 80) 382150000000 2 = true :=
    take_step (n := 2) (t := 80) (b := 20922) rfl rfl ArealUCore.ArealUK.chunk_10460 s61
  have s59 : leavesOK ctxLitU 380100000000 2 ((leaves.drop 20918).take 82) 382150000000 2 = true :=
    take_step (n := 2) (t := 82) (b := 20920) rfl rfl ArealUCore.ArealUK.chunk_10459 s60
  have s58 : leavesOK ctxLitU 380050000000 2 ((leaves.drop 20916).take 84) 382150000000 2 = true :=
    take_step (n := 2) (t := 84) (b := 20918) rfl rfl ArealUCore.ArealUK.chunk_10458 s59
  have s57 : leavesOK ctxLitU 380000000000 2 ((leaves.drop 20914).take 86) 382150000000 2 = true :=
    take_step (n := 2) (t := 86) (b := 20916) rfl rfl ArealUCore.ArealUK.chunk_10457 s58
  have s56 : leavesOK ctxLitU 379950000000 2 ((leaves.drop 20912).take 88) 382150000000 2 = true :=
    take_step (n := 2) (t := 88) (b := 20914) rfl rfl ArealUCore.ArealUK.chunk_10456 s57
  have s55 : leavesOK ctxLitU 379900000000 2 ((leaves.drop 20910).take 90) 382150000000 2 = true :=
    take_step (n := 2) (t := 90) (b := 20912) rfl rfl ArealUCore.ArealUK.chunk_10455 s56
  have s54 : leavesOK ctxLitU 379850000000 2 ((leaves.drop 20908).take 92) 382150000000 2 = true :=
    take_step (n := 2) (t := 92) (b := 20910) rfl rfl ArealUCore.ArealUK.chunk_10454 s55
  have s53 : leavesOK ctxLitU 379800000000 2 ((leaves.drop 20906).take 94) 382150000000 2 = true :=
    take_step (n := 2) (t := 94) (b := 20908) rfl rfl ArealUCore.ArealUK.chunk_10453 s54
  have s52 : leavesOK ctxLitU 379750000000 2 ((leaves.drop 20904).take 96) 382150000000 2 = true :=
    take_step (n := 2) (t := 96) (b := 20906) rfl rfl ArealUCore.ArealUK.chunk_10452 s53
  have s51 : leavesOK ctxLitU 379700000000 2 ((leaves.drop 20902).take 98) 382150000000 2 = true :=
    take_step (n := 2) (t := 98) (b := 20904) rfl rfl ArealUCore.ArealUK.chunk_10451 s52
  have s50 : leavesOK ctxLitU 379650000000 2 ((leaves.drop 20900).take 100) 382150000000 2 = true :=
    take_step (n := 2) (t := 100) (b := 20902) rfl rfl ArealUCore.ArealUK.chunk_10450 s51
  have s49 : leavesOK ctxLitU 379600000000 2 ((leaves.drop 20898).take 102) 382150000000 2 = true :=
    take_step (n := 2) (t := 102) (b := 20900) rfl rfl ArealUCore.ArealUK.chunk_10449 s50
  have s48 : leavesOK ctxLitU 379550000000 2 ((leaves.drop 20896).take 104) 382150000000 2 = true :=
    take_step (n := 2) (t := 104) (b := 20898) rfl rfl ArealUCore.ArealUK.chunk_10448 s49
  have s47 : leavesOK ctxLitU 379500000000 2 ((leaves.drop 20894).take 106) 382150000000 2 = true :=
    take_step (n := 2) (t := 106) (b := 20896) rfl rfl ArealUCore.ArealUK.chunk_10447 s48
  have s46 : leavesOK ctxLitU 379450000000 2 ((leaves.drop 20892).take 108) 382150000000 2 = true :=
    take_step (n := 2) (t := 108) (b := 20894) rfl rfl ArealUCore.ArealUK.chunk_10446 s47
  have s45 : leavesOK ctxLitU 379400000000 2 ((leaves.drop 20890).take 110) 382150000000 2 = true :=
    take_step (n := 2) (t := 110) (b := 20892) rfl rfl ArealUCore.ArealUK.chunk_10445 s46
  have s44 : leavesOK ctxLitU 379350000000 2 ((leaves.drop 20888).take 112) 382150000000 2 = true :=
    take_step (n := 2) (t := 112) (b := 20890) rfl rfl ArealUCore.ArealUK.chunk_10444 s45
  have s43 : leavesOK ctxLitU 379300000000 2 ((leaves.drop 20886).take 114) 382150000000 2 = true :=
    take_step (n := 2) (t := 114) (b := 20888) rfl rfl ArealUCore.ArealUK.chunk_10443 s44
  have s42 : leavesOK ctxLitU 379250000000 2 ((leaves.drop 20884).take 116) 382150000000 2 = true :=
    take_step (n := 2) (t := 116) (b := 20886) rfl rfl ArealUCore.ArealUK.chunk_10442 s43
  have s41 : leavesOK ctxLitU 379200000000 2 ((leaves.drop 20882).take 118) 382150000000 2 = true :=
    take_step (n := 2) (t := 118) (b := 20884) rfl rfl ArealUCore.ArealUK.chunk_10441 s42
  have s40 : leavesOK ctxLitU 379150000000 2 ((leaves.drop 20880).take 120) 382150000000 2 = true :=
    take_step (n := 2) (t := 120) (b := 20882) rfl rfl ArealUCore.ArealUK.chunk_10440 s41
  have s39 : leavesOK ctxLitU 379100000000 2 ((leaves.drop 20878).take 122) 382150000000 2 = true :=
    take_step (n := 2) (t := 122) (b := 20880) rfl rfl ArealUCore.ArealUK.chunk_10439 s40
  have s38 : leavesOK ctxLitU 379050000000 2 ((leaves.drop 20876).take 124) 382150000000 2 = true :=
    take_step (n := 2) (t := 124) (b := 20878) rfl rfl ArealUCore.ArealUK.chunk_10438 s39
  have s37 : leavesOK ctxLitU 379000000000 2 ((leaves.drop 20874).take 126) 382150000000 2 = true :=
    take_step (n := 2) (t := 126) (b := 20876) rfl rfl ArealUCore.ArealUK.chunk_10437 s38
  have s36 : leavesOK ctxLitU 378950000000 2 ((leaves.drop 20872).take 128) 382150000000 2 = true :=
    take_step (n := 2) (t := 128) (b := 20874) rfl rfl ArealUCore.ArealUK.chunk_10436 s37
  have s35 : leavesOK ctxLitU 378900000000 2 ((leaves.drop 20870).take 130) 382150000000 2 = true :=
    take_step (n := 2) (t := 130) (b := 20872) rfl rfl ArealUCore.ArealUK.chunk_10435 s36
  have s34 : leavesOK ctxLitU 378850000000 2 ((leaves.drop 20868).take 132) 382150000000 2 = true :=
    take_step (n := 2) (t := 132) (b := 20870) rfl rfl ArealUCore.ArealUK.chunk_10434 s35
  have s33 : leavesOK ctxLitU 378800000000 2 ((leaves.drop 20866).take 134) 382150000000 2 = true :=
    take_step (n := 2) (t := 134) (b := 20868) rfl rfl ArealUCore.ArealUK.chunk_10433 s34
  have s32 : leavesOK ctxLitU 378750000000 2 ((leaves.drop 20864).take 136) 382150000000 2 = true :=
    take_step (n := 2) (t := 136) (b := 20866) rfl rfl ArealUCore.ArealUK.chunk_10432 s33
  have s31 : leavesOK ctxLitU 378700000000 2 ((leaves.drop 20862).take 138) 382150000000 2 = true :=
    take_step (n := 2) (t := 138) (b := 20864) rfl rfl ArealUCore.ArealUK.chunk_10431 s32
  have s30 : leavesOK ctxLitU 378650000000 2 ((leaves.drop 20860).take 140) 382150000000 2 = true :=
    take_step (n := 2) (t := 140) (b := 20862) rfl rfl ArealUCore.ArealUK.chunk_10430 s31
  have s29 : leavesOK ctxLitU 378600000000 2 ((leaves.drop 20858).take 142) 382150000000 2 = true :=
    take_step (n := 2) (t := 142) (b := 20860) rfl rfl ArealUCore.ArealUK.chunk_10429 s30
  have s28 : leavesOK ctxLitU 378550000000 2 ((leaves.drop 20856).take 144) 382150000000 2 = true :=
    take_step (n := 2) (t := 144) (b := 20858) rfl rfl ArealUCore.ArealUK.chunk_10428 s29
  have s27 : leavesOK ctxLitU 378500000000 2 ((leaves.drop 20854).take 146) 382150000000 2 = true :=
    take_step (n := 2) (t := 146) (b := 20856) rfl rfl ArealUCore.ArealUK.chunk_10427 s28
  have s26 : leavesOK ctxLitU 378450000000 2 ((leaves.drop 20852).take 148) 382150000000 2 = true :=
    take_step (n := 2) (t := 148) (b := 20854) rfl rfl ArealUCore.ArealUK.chunk_10426 s27
  have s25 : leavesOK ctxLitU 378400000000 2 ((leaves.drop 20850).take 150) 382150000000 2 = true :=
    take_step (n := 2) (t := 150) (b := 20852) rfl rfl ArealUCore.ArealUK.chunk_10425 s26
  have s24 : leavesOK ctxLitU 378350000000 2 ((leaves.drop 20848).take 152) 382150000000 2 = true :=
    take_step (n := 2) (t := 152) (b := 20850) rfl rfl ArealUCore.ArealUK.chunk_10424 s25
  have s23 : leavesOK ctxLitU 378300000000 2 ((leaves.drop 20846).take 154) 382150000000 2 = true :=
    take_step (n := 2) (t := 154) (b := 20848) rfl rfl ArealUCore.ArealUK.chunk_10423 s24
  have s22 : leavesOK ctxLitU 378250000000 2 ((leaves.drop 20844).take 156) 382150000000 2 = true :=
    take_step (n := 2) (t := 156) (b := 20846) rfl rfl ArealUCore.ArealUK.chunk_10422 s23
  have s21 : leavesOK ctxLitU 378200000000 2 ((leaves.drop 20842).take 158) 382150000000 2 = true :=
    take_step (n := 2) (t := 158) (b := 20844) rfl rfl ArealUCore.ArealUK.chunk_10421 s22
  have s20 : leavesOK ctxLitU 378150000000 2 ((leaves.drop 20840).take 160) 382150000000 2 = true :=
    take_step (n := 2) (t := 160) (b := 20842) rfl rfl ArealUCore.ArealUK.chunk_10420 s21
  have s19 : leavesOK ctxLitU 378100000000 2 ((leaves.drop 20838).take 162) 382150000000 2 = true :=
    take_step (n := 2) (t := 162) (b := 20840) rfl rfl ArealUCore.ArealUK.chunk_10419 s20
  have s18 : leavesOK ctxLitU 378050000000 2 ((leaves.drop 20836).take 164) 382150000000 2 = true :=
    take_step (n := 2) (t := 164) (b := 20838) rfl rfl ArealUCore.ArealUK.chunk_10418 s19
  have s17 : leavesOK ctxLitU 378000000000 2 ((leaves.drop 20834).take 166) 382150000000 2 = true :=
    take_step (n := 2) (t := 166) (b := 20836) rfl rfl ArealUCore.ArealUK.chunk_10417 s18
  have s16 : leavesOK ctxLitU 377950000000 2 ((leaves.drop 20832).take 168) 382150000000 2 = true :=
    take_step (n := 2) (t := 168) (b := 20834) rfl rfl ArealUCore.ArealUK.chunk_10416 s17
  have s15 : leavesOK ctxLitU 377900000000 2 ((leaves.drop 20830).take 170) 382150000000 2 = true :=
    take_step (n := 2) (t := 170) (b := 20832) rfl rfl ArealUCore.ArealUK.chunk_10415 s16
  have s14 : leavesOK ctxLitU 377850000000 2 ((leaves.drop 20828).take 172) 382150000000 2 = true :=
    take_step (n := 2) (t := 172) (b := 20830) rfl rfl ArealUCore.ArealUK.chunk_10414 s15
  have s13 : leavesOK ctxLitU 377800000000 2 ((leaves.drop 20826).take 174) 382150000000 2 = true :=
    take_step (n := 2) (t := 174) (b := 20828) rfl rfl ArealUCore.ArealUK.chunk_10413 s14
  have s12 : leavesOK ctxLitU 377750000000 2 ((leaves.drop 20824).take 176) 382150000000 2 = true :=
    take_step (n := 2) (t := 176) (b := 20826) rfl rfl ArealUCore.ArealUK.chunk_10412 s13
  have s11 : leavesOK ctxLitU 377700000000 2 ((leaves.drop 20822).take 178) 382150000000 2 = true :=
    take_step (n := 2) (t := 178) (b := 20824) rfl rfl ArealUCore.ArealUK.chunk_10411 s12
  have s10 : leavesOK ctxLitU 377650000000 2 ((leaves.drop 20820).take 180) 382150000000 2 = true :=
    take_step (n := 2) (t := 180) (b := 20822) rfl rfl ArealUCore.ArealUK.chunk_10410 s11
  have s9 : leavesOK ctxLitU 377600000000 2 ((leaves.drop 20818).take 182) 382150000000 2 = true :=
    take_step (n := 2) (t := 182) (b := 20820) rfl rfl ArealUCore.ArealUK.chunk_10409 s10
  have s8 : leavesOK ctxLitU 377550000000 2 ((leaves.drop 20816).take 184) 382150000000 2 = true :=
    take_step (n := 2) (t := 184) (b := 20818) rfl rfl ArealUCore.ArealUK.chunk_10408 s9
  have s7 : leavesOK ctxLitU 377500000000 2 ((leaves.drop 20814).take 186) 382150000000 2 = true :=
    take_step (n := 2) (t := 186) (b := 20816) rfl rfl ArealUCore.ArealUK.chunk_10407 s8
  have s6 : leavesOK ctxLitU 377450000000 2 ((leaves.drop 20812).take 188) 382150000000 2 = true :=
    take_step (n := 2) (t := 188) (b := 20814) rfl rfl ArealUCore.ArealUK.chunk_10406 s7
  have s5 : leavesOK ctxLitU 377400000000 2 ((leaves.drop 20810).take 190) 382150000000 2 = true :=
    take_step (n := 2) (t := 190) (b := 20812) rfl rfl ArealUCore.ArealUK.chunk_10405 s6
  have s4 : leavesOK ctxLitU 377350000000 2 ((leaves.drop 20808).take 192) 382150000000 2 = true :=
    take_step (n := 2) (t := 192) (b := 20810) rfl rfl ArealUCore.ArealUK.chunk_10404 s5
  have s3 : leavesOK ctxLitU 377300000000 2 ((leaves.drop 20806).take 194) 382150000000 2 = true :=
    take_step (n := 2) (t := 194) (b := 20808) rfl rfl ArealUCore.ArealUK.chunk_10403 s4
  have s2 : leavesOK ctxLitU 377250000000 2 ((leaves.drop 20804).take 196) 382150000000 2 = true :=
    take_step (n := 2) (t := 196) (b := 20806) rfl rfl ArealUCore.ArealUK.chunk_10402 s3
  have s1 : leavesOK ctxLitU 377200000000 2 ((leaves.drop 20802).take 198) 382150000000 2 = true :=
    take_step (n := 2) (t := 198) (b := 20804) rfl rfl ArealUCore.ArealUK.chunk_10401 s2
  have s0 : leavesOK ctxLitU 377150000000 2 ((leaves.drop 20800).take 200) 382150000000 2 = true :=
    take_step (n := 2) (t := 200) (b := 20802) rfl rfl ArealUCore.ArealUK.chunk_10400 s1
  exact s0

end Areal.UCert

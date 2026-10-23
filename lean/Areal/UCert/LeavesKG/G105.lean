import ArealUK.Chunk10500
import ArealUK.Chunk10501
import ArealUK.Chunk10502
import ArealUK.Chunk10503
import ArealUK.Chunk10504
import ArealUK.Chunk10505
import ArealUK.Chunk10506
import ArealUK.Chunk10507
import ArealUK.Chunk10508
import ArealUK.Chunk10509
import ArealUK.Chunk10510
import ArealUK.Chunk10511
import ArealUK.Chunk10512
import ArealUK.Chunk10513
import ArealUK.Chunk10514
import ArealUK.Chunk10515
import ArealUK.Chunk10516
import ArealUK.Chunk10517
import ArealUK.Chunk10518
import ArealUK.Chunk10519
import ArealUK.Chunk10520
import ArealUK.Chunk10521
import ArealUK.Chunk10522
import ArealUK.Chunk10523
import ArealUK.Chunk10524
import ArealUK.Chunk10525
import ArealUK.Chunk10526
import ArealUK.Chunk10527
import ArealUK.Chunk10528
import ArealUK.Chunk10529
import ArealUK.Chunk10530
import ArealUK.Chunk10531
import ArealUK.Chunk10532
import ArealUK.Chunk10533
import ArealUK.Chunk10534
import ArealUK.Chunk10535
import ArealUK.Chunk10536
import ArealUK.Chunk10537
import ArealUK.Chunk10538
import ArealUK.Chunk10539
import ArealUK.Chunk10540
import ArealUK.Chunk10541
import ArealUK.Chunk10542
import ArealUK.Chunk10543
import ArealUK.Chunk10544
import ArealUK.Chunk10545
import ArealUK.Chunk10546
import ArealUK.Chunk10547
import ArealUK.Chunk10548
import ArealUK.Chunk10549
import ArealUK.Chunk10550
import ArealUK.Chunk10551
import ArealUK.Chunk10552
import ArealUK.Chunk10553
import ArealUK.Chunk10554
import ArealUK.Chunk10555
import ArealUK.Chunk10556
import ArealUK.Chunk10557
import ArealUK.Chunk10558
import ArealUK.Chunk10559
import ArealUK.Chunk10560
import ArealUK.Chunk10561
import ArealUK.Chunk10562
import ArealUK.Chunk10563
import ArealUK.Chunk10564
import ArealUK.Chunk10565
import ArealUK.Chunk10566
import ArealUK.Chunk10567
import ArealUK.Chunk10568
import ArealUK.Chunk10569
import ArealUK.Chunk10570
import ArealUK.Chunk10571
import ArealUK.Chunk10572
import ArealUK.Chunk10573
import ArealUK.Chunk10574
import ArealUK.Chunk10575
import ArealUK.Chunk10576
import ArealUK.Chunk10577
import ArealUK.Chunk10578
import ArealUK.Chunk10579
import ArealUK.Chunk10580
import ArealUK.Chunk10581
import ArealUK.Chunk10582
import ArealUK.Chunk10583
import ArealUK.Chunk10584
import ArealUK.Chunk10585
import ArealUK.Chunk10586
import ArealUK.Chunk10587
import ArealUK.Chunk10588
import ArealUK.Chunk10589
import ArealUK.Chunk10590
import ArealUK.Chunk10591
import ArealUK.Chunk10592
import ArealUK.Chunk10593
import ArealUK.Chunk10594
import ArealUK.Chunk10595
import ArealUK.Chunk10596
import ArealUK.Chunk10597
import ArealUK.Chunk10598
import ArealUK.Chunk10599
import Areal.UCert.LeavesKGen

/-! Group 105 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_105 : leavesOK ctxLitU 382150000000 2 ((leaves.drop 21000).take 200) 387150000000 2 = true := by
  have s99 := ArealUCore.ArealUK.chunk_10599
  have s98 : leavesOK ctxLitU 387050000000 2 ((leaves.drop 21196).take 4) 387150000000 2 = true :=
    take_step (n := 2) (t := 4) (b := 21198) rfl rfl ArealUCore.ArealUK.chunk_10598 s99
  have s97 : leavesOK ctxLitU 387000000000 2 ((leaves.drop 21194).take 6) 387150000000 2 = true :=
    take_step (n := 2) (t := 6) (b := 21196) rfl rfl ArealUCore.ArealUK.chunk_10597 s98
  have s96 : leavesOK ctxLitU 386950000000 2 ((leaves.drop 21192).take 8) 387150000000 2 = true :=
    take_step (n := 2) (t := 8) (b := 21194) rfl rfl ArealUCore.ArealUK.chunk_10596 s97
  have s95 : leavesOK ctxLitU 386900000000 2 ((leaves.drop 21190).take 10) 387150000000 2 = true :=
    take_step (n := 2) (t := 10) (b := 21192) rfl rfl ArealUCore.ArealUK.chunk_10595 s96
  have s94 : leavesOK ctxLitU 386850000000 2 ((leaves.drop 21188).take 12) 387150000000 2 = true :=
    take_step (n := 2) (t := 12) (b := 21190) rfl rfl ArealUCore.ArealUK.chunk_10594 s95
  have s93 : leavesOK ctxLitU 386800000000 2 ((leaves.drop 21186).take 14) 387150000000 2 = true :=
    take_step (n := 2) (t := 14) (b := 21188) rfl rfl ArealUCore.ArealUK.chunk_10593 s94
  have s92 : leavesOK ctxLitU 386750000000 2 ((leaves.drop 21184).take 16) 387150000000 2 = true :=
    take_step (n := 2) (t := 16) (b := 21186) rfl rfl ArealUCore.ArealUK.chunk_10592 s93
  have s91 : leavesOK ctxLitU 386700000000 2 ((leaves.drop 21182).take 18) 387150000000 2 = true :=
    take_step (n := 2) (t := 18) (b := 21184) rfl rfl ArealUCore.ArealUK.chunk_10591 s92
  have s90 : leavesOK ctxLitU 386650000000 2 ((leaves.drop 21180).take 20) 387150000000 2 = true :=
    take_step (n := 2) (t := 20) (b := 21182) rfl rfl ArealUCore.ArealUK.chunk_10590 s91
  have s89 : leavesOK ctxLitU 386600000000 2 ((leaves.drop 21178).take 22) 387150000000 2 = true :=
    take_step (n := 2) (t := 22) (b := 21180) rfl rfl ArealUCore.ArealUK.chunk_10589 s90
  have s88 : leavesOK ctxLitU 386550000000 2 ((leaves.drop 21176).take 24) 387150000000 2 = true :=
    take_step (n := 2) (t := 24) (b := 21178) rfl rfl ArealUCore.ArealUK.chunk_10588 s89
  have s87 : leavesOK ctxLitU 386500000000 2 ((leaves.drop 21174).take 26) 387150000000 2 = true :=
    take_step (n := 2) (t := 26) (b := 21176) rfl rfl ArealUCore.ArealUK.chunk_10587 s88
  have s86 : leavesOK ctxLitU 386450000000 2 ((leaves.drop 21172).take 28) 387150000000 2 = true :=
    take_step (n := 2) (t := 28) (b := 21174) rfl rfl ArealUCore.ArealUK.chunk_10586 s87
  have s85 : leavesOK ctxLitU 386400000000 2 ((leaves.drop 21170).take 30) 387150000000 2 = true :=
    take_step (n := 2) (t := 30) (b := 21172) rfl rfl ArealUCore.ArealUK.chunk_10585 s86
  have s84 : leavesOK ctxLitU 386350000000 2 ((leaves.drop 21168).take 32) 387150000000 2 = true :=
    take_step (n := 2) (t := 32) (b := 21170) rfl rfl ArealUCore.ArealUK.chunk_10584 s85
  have s83 : leavesOK ctxLitU 386300000000 2 ((leaves.drop 21166).take 34) 387150000000 2 = true :=
    take_step (n := 2) (t := 34) (b := 21168) rfl rfl ArealUCore.ArealUK.chunk_10583 s84
  have s82 : leavesOK ctxLitU 386250000000 2 ((leaves.drop 21164).take 36) 387150000000 2 = true :=
    take_step (n := 2) (t := 36) (b := 21166) rfl rfl ArealUCore.ArealUK.chunk_10582 s83
  have s81 : leavesOK ctxLitU 386200000000 2 ((leaves.drop 21162).take 38) 387150000000 2 = true :=
    take_step (n := 2) (t := 38) (b := 21164) rfl rfl ArealUCore.ArealUK.chunk_10581 s82
  have s80 : leavesOK ctxLitU 386150000000 2 ((leaves.drop 21160).take 40) 387150000000 2 = true :=
    take_step (n := 2) (t := 40) (b := 21162) rfl rfl ArealUCore.ArealUK.chunk_10580 s81
  have s79 : leavesOK ctxLitU 386100000000 2 ((leaves.drop 21158).take 42) 387150000000 2 = true :=
    take_step (n := 2) (t := 42) (b := 21160) rfl rfl ArealUCore.ArealUK.chunk_10579 s80
  have s78 : leavesOK ctxLitU 386050000000 2 ((leaves.drop 21156).take 44) 387150000000 2 = true :=
    take_step (n := 2) (t := 44) (b := 21158) rfl rfl ArealUCore.ArealUK.chunk_10578 s79
  have s77 : leavesOK ctxLitU 386000000000 2 ((leaves.drop 21154).take 46) 387150000000 2 = true :=
    take_step (n := 2) (t := 46) (b := 21156) rfl rfl ArealUCore.ArealUK.chunk_10577 s78
  have s76 : leavesOK ctxLitU 385950000000 2 ((leaves.drop 21152).take 48) 387150000000 2 = true :=
    take_step (n := 2) (t := 48) (b := 21154) rfl rfl ArealUCore.ArealUK.chunk_10576 s77
  have s75 : leavesOK ctxLitU 385900000000 2 ((leaves.drop 21150).take 50) 387150000000 2 = true :=
    take_step (n := 2) (t := 50) (b := 21152) rfl rfl ArealUCore.ArealUK.chunk_10575 s76
  have s74 : leavesOK ctxLitU 385850000000 2 ((leaves.drop 21148).take 52) 387150000000 2 = true :=
    take_step (n := 2) (t := 52) (b := 21150) rfl rfl ArealUCore.ArealUK.chunk_10574 s75
  have s73 : leavesOK ctxLitU 385800000000 2 ((leaves.drop 21146).take 54) 387150000000 2 = true :=
    take_step (n := 2) (t := 54) (b := 21148) rfl rfl ArealUCore.ArealUK.chunk_10573 s74
  have s72 : leavesOK ctxLitU 385750000000 2 ((leaves.drop 21144).take 56) 387150000000 2 = true :=
    take_step (n := 2) (t := 56) (b := 21146) rfl rfl ArealUCore.ArealUK.chunk_10572 s73
  have s71 : leavesOK ctxLitU 385700000000 2 ((leaves.drop 21142).take 58) 387150000000 2 = true :=
    take_step (n := 2) (t := 58) (b := 21144) rfl rfl ArealUCore.ArealUK.chunk_10571 s72
  have s70 : leavesOK ctxLitU 385650000000 2 ((leaves.drop 21140).take 60) 387150000000 2 = true :=
    take_step (n := 2) (t := 60) (b := 21142) rfl rfl ArealUCore.ArealUK.chunk_10570 s71
  have s69 : leavesOK ctxLitU 385600000000 2 ((leaves.drop 21138).take 62) 387150000000 2 = true :=
    take_step (n := 2) (t := 62) (b := 21140) rfl rfl ArealUCore.ArealUK.chunk_10569 s70
  have s68 : leavesOK ctxLitU 385550000000 2 ((leaves.drop 21136).take 64) 387150000000 2 = true :=
    take_step (n := 2) (t := 64) (b := 21138) rfl rfl ArealUCore.ArealUK.chunk_10568 s69
  have s67 : leavesOK ctxLitU 385500000000 2 ((leaves.drop 21134).take 66) 387150000000 2 = true :=
    take_step (n := 2) (t := 66) (b := 21136) rfl rfl ArealUCore.ArealUK.chunk_10567 s68
  have s66 : leavesOK ctxLitU 385450000000 2 ((leaves.drop 21132).take 68) 387150000000 2 = true :=
    take_step (n := 2) (t := 68) (b := 21134) rfl rfl ArealUCore.ArealUK.chunk_10566 s67
  have s65 : leavesOK ctxLitU 385400000000 2 ((leaves.drop 21130).take 70) 387150000000 2 = true :=
    take_step (n := 2) (t := 70) (b := 21132) rfl rfl ArealUCore.ArealUK.chunk_10565 s66
  have s64 : leavesOK ctxLitU 385350000000 2 ((leaves.drop 21128).take 72) 387150000000 2 = true :=
    take_step (n := 2) (t := 72) (b := 21130) rfl rfl ArealUCore.ArealUK.chunk_10564 s65
  have s63 : leavesOK ctxLitU 385300000000 2 ((leaves.drop 21126).take 74) 387150000000 2 = true :=
    take_step (n := 2) (t := 74) (b := 21128) rfl rfl ArealUCore.ArealUK.chunk_10563 s64
  have s62 : leavesOK ctxLitU 385250000000 2 ((leaves.drop 21124).take 76) 387150000000 2 = true :=
    take_step (n := 2) (t := 76) (b := 21126) rfl rfl ArealUCore.ArealUK.chunk_10562 s63
  have s61 : leavesOK ctxLitU 385200000000 2 ((leaves.drop 21122).take 78) 387150000000 2 = true :=
    take_step (n := 2) (t := 78) (b := 21124) rfl rfl ArealUCore.ArealUK.chunk_10561 s62
  have s60 : leavesOK ctxLitU 385150000000 2 ((leaves.drop 21120).take 80) 387150000000 2 = true :=
    take_step (n := 2) (t := 80) (b := 21122) rfl rfl ArealUCore.ArealUK.chunk_10560 s61
  have s59 : leavesOK ctxLitU 385100000000 2 ((leaves.drop 21118).take 82) 387150000000 2 = true :=
    take_step (n := 2) (t := 82) (b := 21120) rfl rfl ArealUCore.ArealUK.chunk_10559 s60
  have s58 : leavesOK ctxLitU 385050000000 2 ((leaves.drop 21116).take 84) 387150000000 2 = true :=
    take_step (n := 2) (t := 84) (b := 21118) rfl rfl ArealUCore.ArealUK.chunk_10558 s59
  have s57 : leavesOK ctxLitU 385000000000 2 ((leaves.drop 21114).take 86) 387150000000 2 = true :=
    take_step (n := 2) (t := 86) (b := 21116) rfl rfl ArealUCore.ArealUK.chunk_10557 s58
  have s56 : leavesOK ctxLitU 384950000000 2 ((leaves.drop 21112).take 88) 387150000000 2 = true :=
    take_step (n := 2) (t := 88) (b := 21114) rfl rfl ArealUCore.ArealUK.chunk_10556 s57
  have s55 : leavesOK ctxLitU 384900000000 2 ((leaves.drop 21110).take 90) 387150000000 2 = true :=
    take_step (n := 2) (t := 90) (b := 21112) rfl rfl ArealUCore.ArealUK.chunk_10555 s56
  have s54 : leavesOK ctxLitU 384850000000 2 ((leaves.drop 21108).take 92) 387150000000 2 = true :=
    take_step (n := 2) (t := 92) (b := 21110) rfl rfl ArealUCore.ArealUK.chunk_10554 s55
  have s53 : leavesOK ctxLitU 384800000000 2 ((leaves.drop 21106).take 94) 387150000000 2 = true :=
    take_step (n := 2) (t := 94) (b := 21108) rfl rfl ArealUCore.ArealUK.chunk_10553 s54
  have s52 : leavesOK ctxLitU 384750000000 2 ((leaves.drop 21104).take 96) 387150000000 2 = true :=
    take_step (n := 2) (t := 96) (b := 21106) rfl rfl ArealUCore.ArealUK.chunk_10552 s53
  have s51 : leavesOK ctxLitU 384700000000 2 ((leaves.drop 21102).take 98) 387150000000 2 = true :=
    take_step (n := 2) (t := 98) (b := 21104) rfl rfl ArealUCore.ArealUK.chunk_10551 s52
  have s50 : leavesOK ctxLitU 384650000000 2 ((leaves.drop 21100).take 100) 387150000000 2 = true :=
    take_step (n := 2) (t := 100) (b := 21102) rfl rfl ArealUCore.ArealUK.chunk_10550 s51
  have s49 : leavesOK ctxLitU 384600000000 2 ((leaves.drop 21098).take 102) 387150000000 2 = true :=
    take_step (n := 2) (t := 102) (b := 21100) rfl rfl ArealUCore.ArealUK.chunk_10549 s50
  have s48 : leavesOK ctxLitU 384550000000 2 ((leaves.drop 21096).take 104) 387150000000 2 = true :=
    take_step (n := 2) (t := 104) (b := 21098) rfl rfl ArealUCore.ArealUK.chunk_10548 s49
  have s47 : leavesOK ctxLitU 384500000000 2 ((leaves.drop 21094).take 106) 387150000000 2 = true :=
    take_step (n := 2) (t := 106) (b := 21096) rfl rfl ArealUCore.ArealUK.chunk_10547 s48
  have s46 : leavesOK ctxLitU 384450000000 2 ((leaves.drop 21092).take 108) 387150000000 2 = true :=
    take_step (n := 2) (t := 108) (b := 21094) rfl rfl ArealUCore.ArealUK.chunk_10546 s47
  have s45 : leavesOK ctxLitU 384400000000 2 ((leaves.drop 21090).take 110) 387150000000 2 = true :=
    take_step (n := 2) (t := 110) (b := 21092) rfl rfl ArealUCore.ArealUK.chunk_10545 s46
  have s44 : leavesOK ctxLitU 384350000000 2 ((leaves.drop 21088).take 112) 387150000000 2 = true :=
    take_step (n := 2) (t := 112) (b := 21090) rfl rfl ArealUCore.ArealUK.chunk_10544 s45
  have s43 : leavesOK ctxLitU 384300000000 2 ((leaves.drop 21086).take 114) 387150000000 2 = true :=
    take_step (n := 2) (t := 114) (b := 21088) rfl rfl ArealUCore.ArealUK.chunk_10543 s44
  have s42 : leavesOK ctxLitU 384250000000 2 ((leaves.drop 21084).take 116) 387150000000 2 = true :=
    take_step (n := 2) (t := 116) (b := 21086) rfl rfl ArealUCore.ArealUK.chunk_10542 s43
  have s41 : leavesOK ctxLitU 384200000000 2 ((leaves.drop 21082).take 118) 387150000000 2 = true :=
    take_step (n := 2) (t := 118) (b := 21084) rfl rfl ArealUCore.ArealUK.chunk_10541 s42
  have s40 : leavesOK ctxLitU 384150000000 2 ((leaves.drop 21080).take 120) 387150000000 2 = true :=
    take_step (n := 2) (t := 120) (b := 21082) rfl rfl ArealUCore.ArealUK.chunk_10540 s41
  have s39 : leavesOK ctxLitU 384100000000 2 ((leaves.drop 21078).take 122) 387150000000 2 = true :=
    take_step (n := 2) (t := 122) (b := 21080) rfl rfl ArealUCore.ArealUK.chunk_10539 s40
  have s38 : leavesOK ctxLitU 384050000000 2 ((leaves.drop 21076).take 124) 387150000000 2 = true :=
    take_step (n := 2) (t := 124) (b := 21078) rfl rfl ArealUCore.ArealUK.chunk_10538 s39
  have s37 : leavesOK ctxLitU 384000000000 2 ((leaves.drop 21074).take 126) 387150000000 2 = true :=
    take_step (n := 2) (t := 126) (b := 21076) rfl rfl ArealUCore.ArealUK.chunk_10537 s38
  have s36 : leavesOK ctxLitU 383950000000 2 ((leaves.drop 21072).take 128) 387150000000 2 = true :=
    take_step (n := 2) (t := 128) (b := 21074) rfl rfl ArealUCore.ArealUK.chunk_10536 s37
  have s35 : leavesOK ctxLitU 383900000000 2 ((leaves.drop 21070).take 130) 387150000000 2 = true :=
    take_step (n := 2) (t := 130) (b := 21072) rfl rfl ArealUCore.ArealUK.chunk_10535 s36
  have s34 : leavesOK ctxLitU 383850000000 2 ((leaves.drop 21068).take 132) 387150000000 2 = true :=
    take_step (n := 2) (t := 132) (b := 21070) rfl rfl ArealUCore.ArealUK.chunk_10534 s35
  have s33 : leavesOK ctxLitU 383800000000 2 ((leaves.drop 21066).take 134) 387150000000 2 = true :=
    take_step (n := 2) (t := 134) (b := 21068) rfl rfl ArealUCore.ArealUK.chunk_10533 s34
  have s32 : leavesOK ctxLitU 383750000000 2 ((leaves.drop 21064).take 136) 387150000000 2 = true :=
    take_step (n := 2) (t := 136) (b := 21066) rfl rfl ArealUCore.ArealUK.chunk_10532 s33
  have s31 : leavesOK ctxLitU 383700000000 2 ((leaves.drop 21062).take 138) 387150000000 2 = true :=
    take_step (n := 2) (t := 138) (b := 21064) rfl rfl ArealUCore.ArealUK.chunk_10531 s32
  have s30 : leavesOK ctxLitU 383650000000 2 ((leaves.drop 21060).take 140) 387150000000 2 = true :=
    take_step (n := 2) (t := 140) (b := 21062) rfl rfl ArealUCore.ArealUK.chunk_10530 s31
  have s29 : leavesOK ctxLitU 383600000000 2 ((leaves.drop 21058).take 142) 387150000000 2 = true :=
    take_step (n := 2) (t := 142) (b := 21060) rfl rfl ArealUCore.ArealUK.chunk_10529 s30
  have s28 : leavesOK ctxLitU 383550000000 2 ((leaves.drop 21056).take 144) 387150000000 2 = true :=
    take_step (n := 2) (t := 144) (b := 21058) rfl rfl ArealUCore.ArealUK.chunk_10528 s29
  have s27 : leavesOK ctxLitU 383500000000 2 ((leaves.drop 21054).take 146) 387150000000 2 = true :=
    take_step (n := 2) (t := 146) (b := 21056) rfl rfl ArealUCore.ArealUK.chunk_10527 s28
  have s26 : leavesOK ctxLitU 383450000000 2 ((leaves.drop 21052).take 148) 387150000000 2 = true :=
    take_step (n := 2) (t := 148) (b := 21054) rfl rfl ArealUCore.ArealUK.chunk_10526 s27
  have s25 : leavesOK ctxLitU 383400000000 2 ((leaves.drop 21050).take 150) 387150000000 2 = true :=
    take_step (n := 2) (t := 150) (b := 21052) rfl rfl ArealUCore.ArealUK.chunk_10525 s26
  have s24 : leavesOK ctxLitU 383350000000 2 ((leaves.drop 21048).take 152) 387150000000 2 = true :=
    take_step (n := 2) (t := 152) (b := 21050) rfl rfl ArealUCore.ArealUK.chunk_10524 s25
  have s23 : leavesOK ctxLitU 383300000000 2 ((leaves.drop 21046).take 154) 387150000000 2 = true :=
    take_step (n := 2) (t := 154) (b := 21048) rfl rfl ArealUCore.ArealUK.chunk_10523 s24
  have s22 : leavesOK ctxLitU 383250000000 2 ((leaves.drop 21044).take 156) 387150000000 2 = true :=
    take_step (n := 2) (t := 156) (b := 21046) rfl rfl ArealUCore.ArealUK.chunk_10522 s23
  have s21 : leavesOK ctxLitU 383200000000 2 ((leaves.drop 21042).take 158) 387150000000 2 = true :=
    take_step (n := 2) (t := 158) (b := 21044) rfl rfl ArealUCore.ArealUK.chunk_10521 s22
  have s20 : leavesOK ctxLitU 383150000000 2 ((leaves.drop 21040).take 160) 387150000000 2 = true :=
    take_step (n := 2) (t := 160) (b := 21042) rfl rfl ArealUCore.ArealUK.chunk_10520 s21
  have s19 : leavesOK ctxLitU 383100000000 2 ((leaves.drop 21038).take 162) 387150000000 2 = true :=
    take_step (n := 2) (t := 162) (b := 21040) rfl rfl ArealUCore.ArealUK.chunk_10519 s20
  have s18 : leavesOK ctxLitU 383050000000 2 ((leaves.drop 21036).take 164) 387150000000 2 = true :=
    take_step (n := 2) (t := 164) (b := 21038) rfl rfl ArealUCore.ArealUK.chunk_10518 s19
  have s17 : leavesOK ctxLitU 383000000000 2 ((leaves.drop 21034).take 166) 387150000000 2 = true :=
    take_step (n := 2) (t := 166) (b := 21036) rfl rfl ArealUCore.ArealUK.chunk_10517 s18
  have s16 : leavesOK ctxLitU 382950000000 2 ((leaves.drop 21032).take 168) 387150000000 2 = true :=
    take_step (n := 2) (t := 168) (b := 21034) rfl rfl ArealUCore.ArealUK.chunk_10516 s17
  have s15 : leavesOK ctxLitU 382900000000 2 ((leaves.drop 21030).take 170) 387150000000 2 = true :=
    take_step (n := 2) (t := 170) (b := 21032) rfl rfl ArealUCore.ArealUK.chunk_10515 s16
  have s14 : leavesOK ctxLitU 382850000000 2 ((leaves.drop 21028).take 172) 387150000000 2 = true :=
    take_step (n := 2) (t := 172) (b := 21030) rfl rfl ArealUCore.ArealUK.chunk_10514 s15
  have s13 : leavesOK ctxLitU 382800000000 2 ((leaves.drop 21026).take 174) 387150000000 2 = true :=
    take_step (n := 2) (t := 174) (b := 21028) rfl rfl ArealUCore.ArealUK.chunk_10513 s14
  have s12 : leavesOK ctxLitU 382750000000 2 ((leaves.drop 21024).take 176) 387150000000 2 = true :=
    take_step (n := 2) (t := 176) (b := 21026) rfl rfl ArealUCore.ArealUK.chunk_10512 s13
  have s11 : leavesOK ctxLitU 382700000000 2 ((leaves.drop 21022).take 178) 387150000000 2 = true :=
    take_step (n := 2) (t := 178) (b := 21024) rfl rfl ArealUCore.ArealUK.chunk_10511 s12
  have s10 : leavesOK ctxLitU 382650000000 2 ((leaves.drop 21020).take 180) 387150000000 2 = true :=
    take_step (n := 2) (t := 180) (b := 21022) rfl rfl ArealUCore.ArealUK.chunk_10510 s11
  have s9 : leavesOK ctxLitU 382600000000 2 ((leaves.drop 21018).take 182) 387150000000 2 = true :=
    take_step (n := 2) (t := 182) (b := 21020) rfl rfl ArealUCore.ArealUK.chunk_10509 s10
  have s8 : leavesOK ctxLitU 382550000000 2 ((leaves.drop 21016).take 184) 387150000000 2 = true :=
    take_step (n := 2) (t := 184) (b := 21018) rfl rfl ArealUCore.ArealUK.chunk_10508 s9
  have s7 : leavesOK ctxLitU 382500000000 2 ((leaves.drop 21014).take 186) 387150000000 2 = true :=
    take_step (n := 2) (t := 186) (b := 21016) rfl rfl ArealUCore.ArealUK.chunk_10507 s8
  have s6 : leavesOK ctxLitU 382450000000 2 ((leaves.drop 21012).take 188) 387150000000 2 = true :=
    take_step (n := 2) (t := 188) (b := 21014) rfl rfl ArealUCore.ArealUK.chunk_10506 s7
  have s5 : leavesOK ctxLitU 382400000000 2 ((leaves.drop 21010).take 190) 387150000000 2 = true :=
    take_step (n := 2) (t := 190) (b := 21012) rfl rfl ArealUCore.ArealUK.chunk_10505 s6
  have s4 : leavesOK ctxLitU 382350000000 2 ((leaves.drop 21008).take 192) 387150000000 2 = true :=
    take_step (n := 2) (t := 192) (b := 21010) rfl rfl ArealUCore.ArealUK.chunk_10504 s5
  have s3 : leavesOK ctxLitU 382300000000 2 ((leaves.drop 21006).take 194) 387150000000 2 = true :=
    take_step (n := 2) (t := 194) (b := 21008) rfl rfl ArealUCore.ArealUK.chunk_10503 s4
  have s2 : leavesOK ctxLitU 382250000000 2 ((leaves.drop 21004).take 196) 387150000000 2 = true :=
    take_step (n := 2) (t := 196) (b := 21006) rfl rfl ArealUCore.ArealUK.chunk_10502 s3
  have s1 : leavesOK ctxLitU 382200000000 2 ((leaves.drop 21002).take 198) 387150000000 2 = true :=
    take_step (n := 2) (t := 198) (b := 21004) rfl rfl ArealUCore.ArealUK.chunk_10501 s2
  have s0 : leavesOK ctxLitU 382150000000 2 ((leaves.drop 21000).take 200) 387150000000 2 = true :=
    take_step (n := 2) (t := 200) (b := 21002) rfl rfl ArealUCore.ArealUK.chunk_10500 s1
  exact s0

end Areal.UCert

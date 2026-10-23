import ArealUK.Chunk16500
import ArealUK.Chunk16501
import ArealUK.Chunk16502
import ArealUK.Chunk16503
import ArealUK.Chunk16504
import ArealUK.Chunk16505
import ArealUK.Chunk16506
import ArealUK.Chunk16507
import ArealUK.Chunk16508
import ArealUK.Chunk16509
import ArealUK.Chunk16510
import ArealUK.Chunk16511
import ArealUK.Chunk16512
import ArealUK.Chunk16513
import ArealUK.Chunk16514
import ArealUK.Chunk16515
import ArealUK.Chunk16516
import ArealUK.Chunk16517
import ArealUK.Chunk16518
import ArealUK.Chunk16519
import ArealUK.Chunk16520
import ArealUK.Chunk16521
import ArealUK.Chunk16522
import ArealUK.Chunk16523
import ArealUK.Chunk16524
import ArealUK.Chunk16525
import ArealUK.Chunk16526
import ArealUK.Chunk16527
import ArealUK.Chunk16528
import ArealUK.Chunk16529
import ArealUK.Chunk16530
import ArealUK.Chunk16531
import ArealUK.Chunk16532
import ArealUK.Chunk16533
import ArealUK.Chunk16534
import ArealUK.Chunk16535
import ArealUK.Chunk16536
import ArealUK.Chunk16537
import ArealUK.Chunk16538
import ArealUK.Chunk16539
import ArealUK.Chunk16540
import ArealUK.Chunk16541
import ArealUK.Chunk16542
import ArealUK.Chunk16543
import ArealUK.Chunk16544
import ArealUK.Chunk16545
import ArealUK.Chunk16546
import ArealUK.Chunk16547
import ArealUK.Chunk16548
import ArealUK.Chunk16549
import ArealUK.Chunk16550
import ArealUK.Chunk16551
import ArealUK.Chunk16552
import ArealUK.Chunk16553
import ArealUK.Chunk16554
import ArealUK.Chunk16555
import ArealUK.Chunk16556
import ArealUK.Chunk16557
import ArealUK.Chunk16558
import ArealUK.Chunk16559
import ArealUK.Chunk16560
import ArealUK.Chunk16561
import ArealUK.Chunk16562
import ArealUK.Chunk16563
import ArealUK.Chunk16564
import ArealUK.Chunk16565
import ArealUK.Chunk16566
import ArealUK.Chunk16567
import ArealUK.Chunk16568
import ArealUK.Chunk16569
import ArealUK.Chunk16570
import ArealUK.Chunk16571
import ArealUK.Chunk16572
import ArealUK.Chunk16573
import ArealUK.Chunk16574
import ArealUK.Chunk16575
import ArealUK.Chunk16576
import ArealUK.Chunk16577
import ArealUK.Chunk16578
import ArealUK.Chunk16579
import ArealUK.Chunk16580
import ArealUK.Chunk16581
import ArealUK.Chunk16582
import ArealUK.Chunk16583
import ArealUK.Chunk16584
import ArealUK.Chunk16585
import ArealUK.Chunk16586
import ArealUK.Chunk16587
import ArealUK.Chunk16588
import ArealUK.Chunk16589
import ArealUK.Chunk16590
import ArealUK.Chunk16591
import ArealUK.Chunk16592
import ArealUK.Chunk16593
import ArealUK.Chunk16594
import ArealUK.Chunk16595
import ArealUK.Chunk16596
import ArealUK.Chunk16597
import ArealUK.Chunk16598
import ArealUK.Chunk16599
import Areal.UCert.LeavesKGen

/-! Group 165 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_165 : leavesOK ctxLitU 188300000000 0 ((leaves.drop 33000).take 200) 193300000000 0 = true := by
  have s99 := ArealUCore.ArealUK.chunk_16599
  have s98 : leavesOK ctxLitU 193200000000 0 ((leaves.drop 33196).take 4) 193300000000 0 = true :=
    take_step (n := 2) (t := 4) (b := 33198) rfl rfl ArealUCore.ArealUK.chunk_16598 s99
  have s97 : leavesOK ctxLitU 193150000000 0 ((leaves.drop 33194).take 6) 193300000000 0 = true :=
    take_step (n := 2) (t := 6) (b := 33196) rfl rfl ArealUCore.ArealUK.chunk_16597 s98
  have s96 : leavesOK ctxLitU 193100000000 0 ((leaves.drop 33192).take 8) 193300000000 0 = true :=
    take_step (n := 2) (t := 8) (b := 33194) rfl rfl ArealUCore.ArealUK.chunk_16596 s97
  have s95 : leavesOK ctxLitU 193050000000 0 ((leaves.drop 33190).take 10) 193300000000 0 = true :=
    take_step (n := 2) (t := 10) (b := 33192) rfl rfl ArealUCore.ArealUK.chunk_16595 s96
  have s94 : leavesOK ctxLitU 193000000000 0 ((leaves.drop 33188).take 12) 193300000000 0 = true :=
    take_step (n := 2) (t := 12) (b := 33190) rfl rfl ArealUCore.ArealUK.chunk_16594 s95
  have s93 : leavesOK ctxLitU 192950000000 0 ((leaves.drop 33186).take 14) 193300000000 0 = true :=
    take_step (n := 2) (t := 14) (b := 33188) rfl rfl ArealUCore.ArealUK.chunk_16593 s94
  have s92 : leavesOK ctxLitU 192900000000 0 ((leaves.drop 33184).take 16) 193300000000 0 = true :=
    take_step (n := 2) (t := 16) (b := 33186) rfl rfl ArealUCore.ArealUK.chunk_16592 s93
  have s91 : leavesOK ctxLitU 192850000000 0 ((leaves.drop 33182).take 18) 193300000000 0 = true :=
    take_step (n := 2) (t := 18) (b := 33184) rfl rfl ArealUCore.ArealUK.chunk_16591 s92
  have s90 : leavesOK ctxLitU 192800000000 0 ((leaves.drop 33180).take 20) 193300000000 0 = true :=
    take_step (n := 2) (t := 20) (b := 33182) rfl rfl ArealUCore.ArealUK.chunk_16590 s91
  have s89 : leavesOK ctxLitU 192750000000 0 ((leaves.drop 33178).take 22) 193300000000 0 = true :=
    take_step (n := 2) (t := 22) (b := 33180) rfl rfl ArealUCore.ArealUK.chunk_16589 s90
  have s88 : leavesOK ctxLitU 192700000000 0 ((leaves.drop 33176).take 24) 193300000000 0 = true :=
    take_step (n := 2) (t := 24) (b := 33178) rfl rfl ArealUCore.ArealUK.chunk_16588 s89
  have s87 : leavesOK ctxLitU 192650000000 0 ((leaves.drop 33174).take 26) 193300000000 0 = true :=
    take_step (n := 2) (t := 26) (b := 33176) rfl rfl ArealUCore.ArealUK.chunk_16587 s88
  have s86 : leavesOK ctxLitU 192600000000 0 ((leaves.drop 33172).take 28) 193300000000 0 = true :=
    take_step (n := 2) (t := 28) (b := 33174) rfl rfl ArealUCore.ArealUK.chunk_16586 s87
  have s85 : leavesOK ctxLitU 192550000000 0 ((leaves.drop 33170).take 30) 193300000000 0 = true :=
    take_step (n := 2) (t := 30) (b := 33172) rfl rfl ArealUCore.ArealUK.chunk_16585 s86
  have s84 : leavesOK ctxLitU 192500000000 0 ((leaves.drop 33168).take 32) 193300000000 0 = true :=
    take_step (n := 2) (t := 32) (b := 33170) rfl rfl ArealUCore.ArealUK.chunk_16584 s85
  have s83 : leavesOK ctxLitU 192450000000 0 ((leaves.drop 33166).take 34) 193300000000 0 = true :=
    take_step (n := 2) (t := 34) (b := 33168) rfl rfl ArealUCore.ArealUK.chunk_16583 s84
  have s82 : leavesOK ctxLitU 192400000000 0 ((leaves.drop 33164).take 36) 193300000000 0 = true :=
    take_step (n := 2) (t := 36) (b := 33166) rfl rfl ArealUCore.ArealUK.chunk_16582 s83
  have s81 : leavesOK ctxLitU 192350000000 0 ((leaves.drop 33162).take 38) 193300000000 0 = true :=
    take_step (n := 2) (t := 38) (b := 33164) rfl rfl ArealUCore.ArealUK.chunk_16581 s82
  have s80 : leavesOK ctxLitU 192300000000 0 ((leaves.drop 33160).take 40) 193300000000 0 = true :=
    take_step (n := 2) (t := 40) (b := 33162) rfl rfl ArealUCore.ArealUK.chunk_16580 s81
  have s79 : leavesOK ctxLitU 192250000000 0 ((leaves.drop 33158).take 42) 193300000000 0 = true :=
    take_step (n := 2) (t := 42) (b := 33160) rfl rfl ArealUCore.ArealUK.chunk_16579 s80
  have s78 : leavesOK ctxLitU 192200000000 0 ((leaves.drop 33156).take 44) 193300000000 0 = true :=
    take_step (n := 2) (t := 44) (b := 33158) rfl rfl ArealUCore.ArealUK.chunk_16578 s79
  have s77 : leavesOK ctxLitU 192150000000 0 ((leaves.drop 33154).take 46) 193300000000 0 = true :=
    take_step (n := 2) (t := 46) (b := 33156) rfl rfl ArealUCore.ArealUK.chunk_16577 s78
  have s76 : leavesOK ctxLitU 192100000000 0 ((leaves.drop 33152).take 48) 193300000000 0 = true :=
    take_step (n := 2) (t := 48) (b := 33154) rfl rfl ArealUCore.ArealUK.chunk_16576 s77
  have s75 : leavesOK ctxLitU 192050000000 0 ((leaves.drop 33150).take 50) 193300000000 0 = true :=
    take_step (n := 2) (t := 50) (b := 33152) rfl rfl ArealUCore.ArealUK.chunk_16575 s76
  have s74 : leavesOK ctxLitU 192000000000 0 ((leaves.drop 33148).take 52) 193300000000 0 = true :=
    take_step (n := 2) (t := 52) (b := 33150) rfl rfl ArealUCore.ArealUK.chunk_16574 s75
  have s73 : leavesOK ctxLitU 191950000000 0 ((leaves.drop 33146).take 54) 193300000000 0 = true :=
    take_step (n := 2) (t := 54) (b := 33148) rfl rfl ArealUCore.ArealUK.chunk_16573 s74
  have s72 : leavesOK ctxLitU 191900000000 0 ((leaves.drop 33144).take 56) 193300000000 0 = true :=
    take_step (n := 2) (t := 56) (b := 33146) rfl rfl ArealUCore.ArealUK.chunk_16572 s73
  have s71 : leavesOK ctxLitU 191850000000 0 ((leaves.drop 33142).take 58) 193300000000 0 = true :=
    take_step (n := 2) (t := 58) (b := 33144) rfl rfl ArealUCore.ArealUK.chunk_16571 s72
  have s70 : leavesOK ctxLitU 191800000000 0 ((leaves.drop 33140).take 60) 193300000000 0 = true :=
    take_step (n := 2) (t := 60) (b := 33142) rfl rfl ArealUCore.ArealUK.chunk_16570 s71
  have s69 : leavesOK ctxLitU 191750000000 0 ((leaves.drop 33138).take 62) 193300000000 0 = true :=
    take_step (n := 2) (t := 62) (b := 33140) rfl rfl ArealUCore.ArealUK.chunk_16569 s70
  have s68 : leavesOK ctxLitU 191700000000 0 ((leaves.drop 33136).take 64) 193300000000 0 = true :=
    take_step (n := 2) (t := 64) (b := 33138) rfl rfl ArealUCore.ArealUK.chunk_16568 s69
  have s67 : leavesOK ctxLitU 191650000000 0 ((leaves.drop 33134).take 66) 193300000000 0 = true :=
    take_step (n := 2) (t := 66) (b := 33136) rfl rfl ArealUCore.ArealUK.chunk_16567 s68
  have s66 : leavesOK ctxLitU 191600000000 0 ((leaves.drop 33132).take 68) 193300000000 0 = true :=
    take_step (n := 2) (t := 68) (b := 33134) rfl rfl ArealUCore.ArealUK.chunk_16566 s67
  have s65 : leavesOK ctxLitU 191550000000 0 ((leaves.drop 33130).take 70) 193300000000 0 = true :=
    take_step (n := 2) (t := 70) (b := 33132) rfl rfl ArealUCore.ArealUK.chunk_16565 s66
  have s64 : leavesOK ctxLitU 191500000000 0 ((leaves.drop 33128).take 72) 193300000000 0 = true :=
    take_step (n := 2) (t := 72) (b := 33130) rfl rfl ArealUCore.ArealUK.chunk_16564 s65
  have s63 : leavesOK ctxLitU 191450000000 0 ((leaves.drop 33126).take 74) 193300000000 0 = true :=
    take_step (n := 2) (t := 74) (b := 33128) rfl rfl ArealUCore.ArealUK.chunk_16563 s64
  have s62 : leavesOK ctxLitU 191400000000 0 ((leaves.drop 33124).take 76) 193300000000 0 = true :=
    take_step (n := 2) (t := 76) (b := 33126) rfl rfl ArealUCore.ArealUK.chunk_16562 s63
  have s61 : leavesOK ctxLitU 191350000000 0 ((leaves.drop 33122).take 78) 193300000000 0 = true :=
    take_step (n := 2) (t := 78) (b := 33124) rfl rfl ArealUCore.ArealUK.chunk_16561 s62
  have s60 : leavesOK ctxLitU 191300000000 0 ((leaves.drop 33120).take 80) 193300000000 0 = true :=
    take_step (n := 2) (t := 80) (b := 33122) rfl rfl ArealUCore.ArealUK.chunk_16560 s61
  have s59 : leavesOK ctxLitU 191250000000 0 ((leaves.drop 33118).take 82) 193300000000 0 = true :=
    take_step (n := 2) (t := 82) (b := 33120) rfl rfl ArealUCore.ArealUK.chunk_16559 s60
  have s58 : leavesOK ctxLitU 191200000000 0 ((leaves.drop 33116).take 84) 193300000000 0 = true :=
    take_step (n := 2) (t := 84) (b := 33118) rfl rfl ArealUCore.ArealUK.chunk_16558 s59
  have s57 : leavesOK ctxLitU 191150000000 0 ((leaves.drop 33114).take 86) 193300000000 0 = true :=
    take_step (n := 2) (t := 86) (b := 33116) rfl rfl ArealUCore.ArealUK.chunk_16557 s58
  have s56 : leavesOK ctxLitU 191100000000 0 ((leaves.drop 33112).take 88) 193300000000 0 = true :=
    take_step (n := 2) (t := 88) (b := 33114) rfl rfl ArealUCore.ArealUK.chunk_16556 s57
  have s55 : leavesOK ctxLitU 191050000000 0 ((leaves.drop 33110).take 90) 193300000000 0 = true :=
    take_step (n := 2) (t := 90) (b := 33112) rfl rfl ArealUCore.ArealUK.chunk_16555 s56
  have s54 : leavesOK ctxLitU 191000000000 0 ((leaves.drop 33108).take 92) 193300000000 0 = true :=
    take_step (n := 2) (t := 92) (b := 33110) rfl rfl ArealUCore.ArealUK.chunk_16554 s55
  have s53 : leavesOK ctxLitU 190950000000 0 ((leaves.drop 33106).take 94) 193300000000 0 = true :=
    take_step (n := 2) (t := 94) (b := 33108) rfl rfl ArealUCore.ArealUK.chunk_16553 s54
  have s52 : leavesOK ctxLitU 190900000000 0 ((leaves.drop 33104).take 96) 193300000000 0 = true :=
    take_step (n := 2) (t := 96) (b := 33106) rfl rfl ArealUCore.ArealUK.chunk_16552 s53
  have s51 : leavesOK ctxLitU 190850000000 0 ((leaves.drop 33102).take 98) 193300000000 0 = true :=
    take_step (n := 2) (t := 98) (b := 33104) rfl rfl ArealUCore.ArealUK.chunk_16551 s52
  have s50 : leavesOK ctxLitU 190800000000 0 ((leaves.drop 33100).take 100) 193300000000 0 = true :=
    take_step (n := 2) (t := 100) (b := 33102) rfl rfl ArealUCore.ArealUK.chunk_16550 s51
  have s49 : leavesOK ctxLitU 190750000000 0 ((leaves.drop 33098).take 102) 193300000000 0 = true :=
    take_step (n := 2) (t := 102) (b := 33100) rfl rfl ArealUCore.ArealUK.chunk_16549 s50
  have s48 : leavesOK ctxLitU 190700000000 0 ((leaves.drop 33096).take 104) 193300000000 0 = true :=
    take_step (n := 2) (t := 104) (b := 33098) rfl rfl ArealUCore.ArealUK.chunk_16548 s49
  have s47 : leavesOK ctxLitU 190650000000 0 ((leaves.drop 33094).take 106) 193300000000 0 = true :=
    take_step (n := 2) (t := 106) (b := 33096) rfl rfl ArealUCore.ArealUK.chunk_16547 s48
  have s46 : leavesOK ctxLitU 190600000000 0 ((leaves.drop 33092).take 108) 193300000000 0 = true :=
    take_step (n := 2) (t := 108) (b := 33094) rfl rfl ArealUCore.ArealUK.chunk_16546 s47
  have s45 : leavesOK ctxLitU 190550000000 0 ((leaves.drop 33090).take 110) 193300000000 0 = true :=
    take_step (n := 2) (t := 110) (b := 33092) rfl rfl ArealUCore.ArealUK.chunk_16545 s46
  have s44 : leavesOK ctxLitU 190500000000 0 ((leaves.drop 33088).take 112) 193300000000 0 = true :=
    take_step (n := 2) (t := 112) (b := 33090) rfl rfl ArealUCore.ArealUK.chunk_16544 s45
  have s43 : leavesOK ctxLitU 190450000000 0 ((leaves.drop 33086).take 114) 193300000000 0 = true :=
    take_step (n := 2) (t := 114) (b := 33088) rfl rfl ArealUCore.ArealUK.chunk_16543 s44
  have s42 : leavesOK ctxLitU 190400000000 0 ((leaves.drop 33084).take 116) 193300000000 0 = true :=
    take_step (n := 2) (t := 116) (b := 33086) rfl rfl ArealUCore.ArealUK.chunk_16542 s43
  have s41 : leavesOK ctxLitU 190350000000 0 ((leaves.drop 33082).take 118) 193300000000 0 = true :=
    take_step (n := 2) (t := 118) (b := 33084) rfl rfl ArealUCore.ArealUK.chunk_16541 s42
  have s40 : leavesOK ctxLitU 190300000000 0 ((leaves.drop 33080).take 120) 193300000000 0 = true :=
    take_step (n := 2) (t := 120) (b := 33082) rfl rfl ArealUCore.ArealUK.chunk_16540 s41
  have s39 : leavesOK ctxLitU 190250000000 0 ((leaves.drop 33078).take 122) 193300000000 0 = true :=
    take_step (n := 2) (t := 122) (b := 33080) rfl rfl ArealUCore.ArealUK.chunk_16539 s40
  have s38 : leavesOK ctxLitU 190200000000 0 ((leaves.drop 33076).take 124) 193300000000 0 = true :=
    take_step (n := 2) (t := 124) (b := 33078) rfl rfl ArealUCore.ArealUK.chunk_16538 s39
  have s37 : leavesOK ctxLitU 190150000000 0 ((leaves.drop 33074).take 126) 193300000000 0 = true :=
    take_step (n := 2) (t := 126) (b := 33076) rfl rfl ArealUCore.ArealUK.chunk_16537 s38
  have s36 : leavesOK ctxLitU 190100000000 0 ((leaves.drop 33072).take 128) 193300000000 0 = true :=
    take_step (n := 2) (t := 128) (b := 33074) rfl rfl ArealUCore.ArealUK.chunk_16536 s37
  have s35 : leavesOK ctxLitU 190050000000 0 ((leaves.drop 33070).take 130) 193300000000 0 = true :=
    take_step (n := 2) (t := 130) (b := 33072) rfl rfl ArealUCore.ArealUK.chunk_16535 s36
  have s34 : leavesOK ctxLitU 190000000000 0 ((leaves.drop 33068).take 132) 193300000000 0 = true :=
    take_step (n := 2) (t := 132) (b := 33070) rfl rfl ArealUCore.ArealUK.chunk_16534 s35
  have s33 : leavesOK ctxLitU 189950000000 0 ((leaves.drop 33066).take 134) 193300000000 0 = true :=
    take_step (n := 2) (t := 134) (b := 33068) rfl rfl ArealUCore.ArealUK.chunk_16533 s34
  have s32 : leavesOK ctxLitU 189900000000 0 ((leaves.drop 33064).take 136) 193300000000 0 = true :=
    take_step (n := 2) (t := 136) (b := 33066) rfl rfl ArealUCore.ArealUK.chunk_16532 s33
  have s31 : leavesOK ctxLitU 189850000000 0 ((leaves.drop 33062).take 138) 193300000000 0 = true :=
    take_step (n := 2) (t := 138) (b := 33064) rfl rfl ArealUCore.ArealUK.chunk_16531 s32
  have s30 : leavesOK ctxLitU 189800000000 0 ((leaves.drop 33060).take 140) 193300000000 0 = true :=
    take_step (n := 2) (t := 140) (b := 33062) rfl rfl ArealUCore.ArealUK.chunk_16530 s31
  have s29 : leavesOK ctxLitU 189750000000 0 ((leaves.drop 33058).take 142) 193300000000 0 = true :=
    take_step (n := 2) (t := 142) (b := 33060) rfl rfl ArealUCore.ArealUK.chunk_16529 s30
  have s28 : leavesOK ctxLitU 189700000000 0 ((leaves.drop 33056).take 144) 193300000000 0 = true :=
    take_step (n := 2) (t := 144) (b := 33058) rfl rfl ArealUCore.ArealUK.chunk_16528 s29
  have s27 : leavesOK ctxLitU 189650000000 0 ((leaves.drop 33054).take 146) 193300000000 0 = true :=
    take_step (n := 2) (t := 146) (b := 33056) rfl rfl ArealUCore.ArealUK.chunk_16527 s28
  have s26 : leavesOK ctxLitU 189600000000 0 ((leaves.drop 33052).take 148) 193300000000 0 = true :=
    take_step (n := 2) (t := 148) (b := 33054) rfl rfl ArealUCore.ArealUK.chunk_16526 s27
  have s25 : leavesOK ctxLitU 189550000000 0 ((leaves.drop 33050).take 150) 193300000000 0 = true :=
    take_step (n := 2) (t := 150) (b := 33052) rfl rfl ArealUCore.ArealUK.chunk_16525 s26
  have s24 : leavesOK ctxLitU 189500000000 0 ((leaves.drop 33048).take 152) 193300000000 0 = true :=
    take_step (n := 2) (t := 152) (b := 33050) rfl rfl ArealUCore.ArealUK.chunk_16524 s25
  have s23 : leavesOK ctxLitU 189450000000 0 ((leaves.drop 33046).take 154) 193300000000 0 = true :=
    take_step (n := 2) (t := 154) (b := 33048) rfl rfl ArealUCore.ArealUK.chunk_16523 s24
  have s22 : leavesOK ctxLitU 189400000000 0 ((leaves.drop 33044).take 156) 193300000000 0 = true :=
    take_step (n := 2) (t := 156) (b := 33046) rfl rfl ArealUCore.ArealUK.chunk_16522 s23
  have s21 : leavesOK ctxLitU 189350000000 0 ((leaves.drop 33042).take 158) 193300000000 0 = true :=
    take_step (n := 2) (t := 158) (b := 33044) rfl rfl ArealUCore.ArealUK.chunk_16521 s22
  have s20 : leavesOK ctxLitU 189300000000 0 ((leaves.drop 33040).take 160) 193300000000 0 = true :=
    take_step (n := 2) (t := 160) (b := 33042) rfl rfl ArealUCore.ArealUK.chunk_16520 s21
  have s19 : leavesOK ctxLitU 189250000000 0 ((leaves.drop 33038).take 162) 193300000000 0 = true :=
    take_step (n := 2) (t := 162) (b := 33040) rfl rfl ArealUCore.ArealUK.chunk_16519 s20
  have s18 : leavesOK ctxLitU 189200000000 0 ((leaves.drop 33036).take 164) 193300000000 0 = true :=
    take_step (n := 2) (t := 164) (b := 33038) rfl rfl ArealUCore.ArealUK.chunk_16518 s19
  have s17 : leavesOK ctxLitU 189150000000 0 ((leaves.drop 33034).take 166) 193300000000 0 = true :=
    take_step (n := 2) (t := 166) (b := 33036) rfl rfl ArealUCore.ArealUK.chunk_16517 s18
  have s16 : leavesOK ctxLitU 189100000000 0 ((leaves.drop 33032).take 168) 193300000000 0 = true :=
    take_step (n := 2) (t := 168) (b := 33034) rfl rfl ArealUCore.ArealUK.chunk_16516 s17
  have s15 : leavesOK ctxLitU 189050000000 0 ((leaves.drop 33030).take 170) 193300000000 0 = true :=
    take_step (n := 2) (t := 170) (b := 33032) rfl rfl ArealUCore.ArealUK.chunk_16515 s16
  have s14 : leavesOK ctxLitU 189000000000 0 ((leaves.drop 33028).take 172) 193300000000 0 = true :=
    take_step (n := 2) (t := 172) (b := 33030) rfl rfl ArealUCore.ArealUK.chunk_16514 s15
  have s13 : leavesOK ctxLitU 188950000000 0 ((leaves.drop 33026).take 174) 193300000000 0 = true :=
    take_step (n := 2) (t := 174) (b := 33028) rfl rfl ArealUCore.ArealUK.chunk_16513 s14
  have s12 : leavesOK ctxLitU 188900000000 0 ((leaves.drop 33024).take 176) 193300000000 0 = true :=
    take_step (n := 2) (t := 176) (b := 33026) rfl rfl ArealUCore.ArealUK.chunk_16512 s13
  have s11 : leavesOK ctxLitU 188850000000 0 ((leaves.drop 33022).take 178) 193300000000 0 = true :=
    take_step (n := 2) (t := 178) (b := 33024) rfl rfl ArealUCore.ArealUK.chunk_16511 s12
  have s10 : leavesOK ctxLitU 188800000000 0 ((leaves.drop 33020).take 180) 193300000000 0 = true :=
    take_step (n := 2) (t := 180) (b := 33022) rfl rfl ArealUCore.ArealUK.chunk_16510 s11
  have s9 : leavesOK ctxLitU 188750000000 0 ((leaves.drop 33018).take 182) 193300000000 0 = true :=
    take_step (n := 2) (t := 182) (b := 33020) rfl rfl ArealUCore.ArealUK.chunk_16509 s10
  have s8 : leavesOK ctxLitU 188700000000 0 ((leaves.drop 33016).take 184) 193300000000 0 = true :=
    take_step (n := 2) (t := 184) (b := 33018) rfl rfl ArealUCore.ArealUK.chunk_16508 s9
  have s7 : leavesOK ctxLitU 188650000000 0 ((leaves.drop 33014).take 186) 193300000000 0 = true :=
    take_step (n := 2) (t := 186) (b := 33016) rfl rfl ArealUCore.ArealUK.chunk_16507 s8
  have s6 : leavesOK ctxLitU 188600000000 0 ((leaves.drop 33012).take 188) 193300000000 0 = true :=
    take_step (n := 2) (t := 188) (b := 33014) rfl rfl ArealUCore.ArealUK.chunk_16506 s7
  have s5 : leavesOK ctxLitU 188550000000 0 ((leaves.drop 33010).take 190) 193300000000 0 = true :=
    take_step (n := 2) (t := 190) (b := 33012) rfl rfl ArealUCore.ArealUK.chunk_16505 s6
  have s4 : leavesOK ctxLitU 188500000000 0 ((leaves.drop 33008).take 192) 193300000000 0 = true :=
    take_step (n := 2) (t := 192) (b := 33010) rfl rfl ArealUCore.ArealUK.chunk_16504 s5
  have s3 : leavesOK ctxLitU 188450000000 0 ((leaves.drop 33006).take 194) 193300000000 0 = true :=
    take_step (n := 2) (t := 194) (b := 33008) rfl rfl ArealUCore.ArealUK.chunk_16503 s4
  have s2 : leavesOK ctxLitU 188400000000 0 ((leaves.drop 33004).take 196) 193300000000 0 = true :=
    take_step (n := 2) (t := 196) (b := 33006) rfl rfl ArealUCore.ArealUK.chunk_16502 s3
  have s1 : leavesOK ctxLitU 188350000000 0 ((leaves.drop 33002).take 198) 193300000000 0 = true :=
    take_step (n := 2) (t := 198) (b := 33004) rfl rfl ArealUCore.ArealUK.chunk_16501 s2
  have s0 : leavesOK ctxLitU 188300000000 0 ((leaves.drop 33000).take 200) 193300000000 0 = true :=
    take_step (n := 2) (t := 200) (b := 33002) rfl rfl ArealUCore.ArealUK.chunk_16500 s1
  exact s0

end Areal.UCert

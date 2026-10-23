import ArealUK.Chunk6500
import ArealUK.Chunk6501
import ArealUK.Chunk6502
import ArealUK.Chunk6503
import ArealUK.Chunk6504
import ArealUK.Chunk6505
import ArealUK.Chunk6506
import ArealUK.Chunk6507
import ArealUK.Chunk6508
import ArealUK.Chunk6509
import ArealUK.Chunk6510
import ArealUK.Chunk6511
import ArealUK.Chunk6512
import ArealUK.Chunk6513
import ArealUK.Chunk6514
import ArealUK.Chunk6515
import ArealUK.Chunk6516
import ArealUK.Chunk6517
import ArealUK.Chunk6518
import ArealUK.Chunk6519
import ArealUK.Chunk6520
import ArealUK.Chunk6521
import ArealUK.Chunk6522
import ArealUK.Chunk6523
import ArealUK.Chunk6524
import ArealUK.Chunk6525
import ArealUK.Chunk6526
import ArealUK.Chunk6527
import ArealUK.Chunk6528
import ArealUK.Chunk6529
import ArealUK.Chunk6530
import ArealUK.Chunk6531
import ArealUK.Chunk6532
import ArealUK.Chunk6533
import ArealUK.Chunk6534
import ArealUK.Chunk6535
import ArealUK.Chunk6536
import ArealUK.Chunk6537
import ArealUK.Chunk6538
import ArealUK.Chunk6539
import ArealUK.Chunk6540
import ArealUK.Chunk6541
import ArealUK.Chunk6542
import ArealUK.Chunk6543
import ArealUK.Chunk6544
import ArealUK.Chunk6545
import ArealUK.Chunk6546
import ArealUK.Chunk6547
import ArealUK.Chunk6548
import ArealUK.Chunk6549
import ArealUK.Chunk6550
import ArealUK.Chunk6551
import ArealUK.Chunk6552
import ArealUK.Chunk6553
import ArealUK.Chunk6554
import ArealUK.Chunk6555
import ArealUK.Chunk6556
import ArealUK.Chunk6557
import ArealUK.Chunk6558
import ArealUK.Chunk6559
import ArealUK.Chunk6560
import ArealUK.Chunk6561
import ArealUK.Chunk6562
import ArealUK.Chunk6563
import ArealUK.Chunk6564
import ArealUK.Chunk6565
import ArealUK.Chunk6566
import ArealUK.Chunk6567
import ArealUK.Chunk6568
import ArealUK.Chunk6569
import ArealUK.Chunk6570
import ArealUK.Chunk6571
import ArealUK.Chunk6572
import ArealUK.Chunk6573
import ArealUK.Chunk6574
import ArealUK.Chunk6575
import ArealUK.Chunk6576
import ArealUK.Chunk6577
import ArealUK.Chunk6578
import ArealUK.Chunk6579
import ArealUK.Chunk6580
import ArealUK.Chunk6581
import ArealUK.Chunk6582
import ArealUK.Chunk6583
import ArealUK.Chunk6584
import ArealUK.Chunk6585
import ArealUK.Chunk6586
import ArealUK.Chunk6587
import ArealUK.Chunk6588
import ArealUK.Chunk6589
import ArealUK.Chunk6590
import ArealUK.Chunk6591
import ArealUK.Chunk6592
import ArealUK.Chunk6593
import ArealUK.Chunk6594
import ArealUK.Chunk6595
import ArealUK.Chunk6596
import ArealUK.Chunk6597
import ArealUK.Chunk6598
import ArealUK.Chunk6599
import Areal.UCert.LeavesKGen

/-! Group 65 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_65 : leavesOK ctxLitU 169762500000 2 ((leaves.drop 13000).take 200) 46425000000 0 = true := by
  have s99 := ArealUCore.ArealUK.chunk_6599
  have s98 : leavesOK ctxLitU 46325000000 0 ((leaves.drop 13196).take 4) 46425000000 0 = true :=
    take_step (n := 2) (t := 4) (b := 13198) rfl rfl ArealUCore.ArealUK.chunk_6598 s99
  have s97 : leavesOK ctxLitU 46275000000 0 ((leaves.drop 13194).take 6) 46425000000 0 = true :=
    take_step (n := 2) (t := 6) (b := 13196) rfl rfl ArealUCore.ArealUK.chunk_6597 s98
  have s96 : leavesOK ctxLitU 46225000000 0 ((leaves.drop 13192).take 8) 46425000000 0 = true :=
    take_step (n := 2) (t := 8) (b := 13194) rfl rfl ArealUCore.ArealUK.chunk_6596 s97
  have s95 : leavesOK ctxLitU 46175000000 0 ((leaves.drop 13190).take 10) 46425000000 0 = true :=
    take_step (n := 2) (t := 10) (b := 13192) rfl rfl ArealUCore.ArealUK.chunk_6595 s96
  have s94 : leavesOK ctxLitU 46125000000 0 ((leaves.drop 13188).take 12) 46425000000 0 = true :=
    take_step (n := 2) (t := 12) (b := 13190) rfl rfl ArealUCore.ArealUK.chunk_6594 s95
  have s93 : leavesOK ctxLitU 46075000000 0 ((leaves.drop 13186).take 14) 46425000000 0 = true :=
    take_step (n := 2) (t := 14) (b := 13188) rfl rfl ArealUCore.ArealUK.chunk_6593 s94
  have s92 : leavesOK ctxLitU 46025000000 0 ((leaves.drop 13184).take 16) 46425000000 0 = true :=
    take_step (n := 2) (t := 16) (b := 13186) rfl rfl ArealUCore.ArealUK.chunk_6592 s93
  have s91 : leavesOK ctxLitU 45975000000 0 ((leaves.drop 13182).take 18) 46425000000 0 = true :=
    take_step (n := 2) (t := 18) (b := 13184) rfl rfl ArealUCore.ArealUK.chunk_6591 s92
  have s90 : leavesOK ctxLitU 45925000000 0 ((leaves.drop 13180).take 20) 46425000000 0 = true :=
    take_step (n := 2) (t := 20) (b := 13182) rfl rfl ArealUCore.ArealUK.chunk_6590 s91
  have s89 : leavesOK ctxLitU 45875000000 0 ((leaves.drop 13178).take 22) 46425000000 0 = true :=
    take_step (n := 2) (t := 22) (b := 13180) rfl rfl ArealUCore.ArealUK.chunk_6589 s90
  have s88 : leavesOK ctxLitU 45825000000 0 ((leaves.drop 13176).take 24) 46425000000 0 = true :=
    take_step (n := 2) (t := 24) (b := 13178) rfl rfl ArealUCore.ArealUK.chunk_6588 s89
  have s87 : leavesOK ctxLitU 45775000000 0 ((leaves.drop 13174).take 26) 46425000000 0 = true :=
    take_step (n := 2) (t := 26) (b := 13176) rfl rfl ArealUCore.ArealUK.chunk_6587 s88
  have s86 : leavesOK ctxLitU 45725000000 0 ((leaves.drop 13172).take 28) 46425000000 0 = true :=
    take_step (n := 2) (t := 28) (b := 13174) rfl rfl ArealUCore.ArealUK.chunk_6586 s87
  have s85 : leavesOK ctxLitU 45675000000 0 ((leaves.drop 13170).take 30) 46425000000 0 = true :=
    take_step (n := 2) (t := 30) (b := 13172) rfl rfl ArealUCore.ArealUK.chunk_6585 s86
  have s84 : leavesOK ctxLitU 45625000000 0 ((leaves.drop 13168).take 32) 46425000000 0 = true :=
    take_step (n := 2) (t := 32) (b := 13170) rfl rfl ArealUCore.ArealUK.chunk_6584 s85
  have s83 : leavesOK ctxLitU 45575000000 0 ((leaves.drop 13166).take 34) 46425000000 0 = true :=
    take_step (n := 2) (t := 34) (b := 13168) rfl rfl ArealUCore.ArealUK.chunk_6583 s84
  have s82 : leavesOK ctxLitU 45525000000 0 ((leaves.drop 13164).take 36) 46425000000 0 = true :=
    take_step (n := 2) (t := 36) (b := 13166) rfl rfl ArealUCore.ArealUK.chunk_6582 s83
  have s81 : leavesOK ctxLitU 45475000000 0 ((leaves.drop 13162).take 38) 46425000000 0 = true :=
    take_step (n := 2) (t := 38) (b := 13164) rfl rfl ArealUCore.ArealUK.chunk_6581 s82
  have s80 : leavesOK ctxLitU 45425000000 0 ((leaves.drop 13160).take 40) 46425000000 0 = true :=
    take_step (n := 2) (t := 40) (b := 13162) rfl rfl ArealUCore.ArealUK.chunk_6580 s81
  have s79 : leavesOK ctxLitU 45375000000 0 ((leaves.drop 13158).take 42) 46425000000 0 = true :=
    take_step (n := 2) (t := 42) (b := 13160) rfl rfl ArealUCore.ArealUK.chunk_6579 s80
  have s78 : leavesOK ctxLitU 45325000000 0 ((leaves.drop 13156).take 44) 46425000000 0 = true :=
    take_step (n := 2) (t := 44) (b := 13158) rfl rfl ArealUCore.ArealUK.chunk_6578 s79
  have s77 : leavesOK ctxLitU 45275000000 0 ((leaves.drop 13154).take 46) 46425000000 0 = true :=
    take_step (n := 2) (t := 46) (b := 13156) rfl rfl ArealUCore.ArealUK.chunk_6577 s78
  have s76 : leavesOK ctxLitU 45225000000 0 ((leaves.drop 13152).take 48) 46425000000 0 = true :=
    take_step (n := 2) (t := 48) (b := 13154) rfl rfl ArealUCore.ArealUK.chunk_6576 s77
  have s75 : leavesOK ctxLitU 45175000000 0 ((leaves.drop 13150).take 50) 46425000000 0 = true :=
    take_step (n := 2) (t := 50) (b := 13152) rfl rfl ArealUCore.ArealUK.chunk_6575 s76
  have s74 : leavesOK ctxLitU 45125000000 0 ((leaves.drop 13148).take 52) 46425000000 0 = true :=
    take_step (n := 2) (t := 52) (b := 13150) rfl rfl ArealUCore.ArealUK.chunk_6574 s75
  have s73 : leavesOK ctxLitU 45075000000 0 ((leaves.drop 13146).take 54) 46425000000 0 = true :=
    take_step (n := 2) (t := 54) (b := 13148) rfl rfl ArealUCore.ArealUK.chunk_6573 s74
  have s72 : leavesOK ctxLitU 45025000000 0 ((leaves.drop 13144).take 56) 46425000000 0 = true :=
    take_step (n := 2) (t := 56) (b := 13146) rfl rfl ArealUCore.ArealUK.chunk_6572 s73
  have s71 : leavesOK ctxLitU 44975000000 0 ((leaves.drop 13142).take 58) 46425000000 0 = true :=
    take_step (n := 2) (t := 58) (b := 13144) rfl rfl ArealUCore.ArealUK.chunk_6571 s72
  have s70 : leavesOK ctxLitU 44925000000 0 ((leaves.drop 13140).take 60) 46425000000 0 = true :=
    take_step (n := 2) (t := 60) (b := 13142) rfl rfl ArealUCore.ArealUK.chunk_6570 s71
  have s69 : leavesOK ctxLitU 44875000000 0 ((leaves.drop 13138).take 62) 46425000000 0 = true :=
    take_step (n := 2) (t := 62) (b := 13140) rfl rfl ArealUCore.ArealUK.chunk_6569 s70
  have s68 : leavesOK ctxLitU 44825000000 0 ((leaves.drop 13136).take 64) 46425000000 0 = true :=
    take_step (n := 2) (t := 64) (b := 13138) rfl rfl ArealUCore.ArealUK.chunk_6568 s69
  have s67 : leavesOK ctxLitU 44775000000 0 ((leaves.drop 13134).take 66) 46425000000 0 = true :=
    take_step (n := 2) (t := 66) (b := 13136) rfl rfl ArealUCore.ArealUK.chunk_6567 s68
  have s66 : leavesOK ctxLitU 44725000000 0 ((leaves.drop 13132).take 68) 46425000000 0 = true :=
    take_step (n := 2) (t := 68) (b := 13134) rfl rfl ArealUCore.ArealUK.chunk_6566 s67
  have s65 : leavesOK ctxLitU 44675000000 0 ((leaves.drop 13130).take 70) 46425000000 0 = true :=
    take_step (n := 2) (t := 70) (b := 13132) rfl rfl ArealUCore.ArealUK.chunk_6565 s66
  have s64 : leavesOK ctxLitU 44625000000 0 ((leaves.drop 13128).take 72) 46425000000 0 = true :=
    take_step (n := 2) (t := 72) (b := 13130) rfl rfl ArealUCore.ArealUK.chunk_6564 s65
  have s63 : leavesOK ctxLitU 44575000000 0 ((leaves.drop 13126).take 74) 46425000000 0 = true :=
    take_step (n := 2) (t := 74) (b := 13128) rfl rfl ArealUCore.ArealUK.chunk_6563 s64
  have s62 : leavesOK ctxLitU 44525000000 0 ((leaves.drop 13124).take 76) 46425000000 0 = true :=
    take_step (n := 2) (t := 76) (b := 13126) rfl rfl ArealUCore.ArealUK.chunk_6562 s63
  have s61 : leavesOK ctxLitU 44475000000 0 ((leaves.drop 13122).take 78) 46425000000 0 = true :=
    take_step (n := 2) (t := 78) (b := 13124) rfl rfl ArealUCore.ArealUK.chunk_6561 s62
  have s60 : leavesOK ctxLitU 44425000000 0 ((leaves.drop 13120).take 80) 46425000000 0 = true :=
    take_step (n := 2) (t := 80) (b := 13122) rfl rfl ArealUCore.ArealUK.chunk_6560 s61
  have s59 : leavesOK ctxLitU 44375000000 0 ((leaves.drop 13118).take 82) 46425000000 0 = true :=
    take_step (n := 2) (t := 82) (b := 13120) rfl rfl ArealUCore.ArealUK.chunk_6559 s60
  have s58 : leavesOK ctxLitU 44325000000 0 ((leaves.drop 13116).take 84) 46425000000 0 = true :=
    take_step (n := 2) (t := 84) (b := 13118) rfl rfl ArealUCore.ArealUK.chunk_6558 s59
  have s57 : leavesOK ctxLitU 44275000000 0 ((leaves.drop 13114).take 86) 46425000000 0 = true :=
    take_step (n := 2) (t := 86) (b := 13116) rfl rfl ArealUCore.ArealUK.chunk_6557 s58
  have s56 : leavesOK ctxLitU 44250000000 0 ((leaves.drop 13112).take 88) 46425000000 0 = true :=
    take_step (n := 2) (t := 88) (b := 13114) rfl rfl ArealUCore.ArealUK.chunk_6556 s57
  have s55 : leavesOK ctxLitU 44237500000 0 ((leaves.drop 13110).take 90) 46425000000 0 = true :=
    take_step (n := 2) (t := 90) (b := 13112) rfl rfl ArealUCore.ArealUK.chunk_6555 s56
  have s54 : leavesOK ctxLitU 44225000000 0 ((leaves.drop 13108).take 92) 46425000000 0 = true :=
    take_step (n := 2) (t := 92) (b := 13110) rfl rfl ArealUCore.ArealUK.chunk_6554 s55
  have s53 : leavesOK ctxLitU 44200000000 0 ((leaves.drop 13106).take 94) 46425000000 0 = true :=
    take_step (n := 2) (t := 94) (b := 13108) rfl rfl ArealUCore.ArealUK.chunk_6553 s54
  have s52 : leavesOK ctxLitU 44150000000 0 ((leaves.drop 13104).take 96) 46425000000 0 = true :=
    take_step (n := 2) (t := 96) (b := 13106) rfl rfl ArealUCore.ArealUK.chunk_6552 s53
  have s51 : leavesOK ctxLitU 44100000000 0 ((leaves.drop 13102).take 98) 46425000000 0 = true :=
    take_step (n := 2) (t := 98) (b := 13104) rfl rfl ArealUCore.ArealUK.chunk_6551 s52
  have s50 : leavesOK ctxLitU 44050000000 0 ((leaves.drop 13100).take 100) 46425000000 0 = true :=
    take_step (n := 2) (t := 100) (b := 13102) rfl rfl ArealUCore.ArealUK.chunk_6550 s51
  have s49 : leavesOK ctxLitU 44000000000 0 ((leaves.drop 13098).take 102) 46425000000 0 = true :=
    take_step (n := 2) (t := 102) (b := 13100) rfl rfl ArealUCore.ArealUK.chunk_6549 s50
  have s48 : leavesOK ctxLitU 43950000000 0 ((leaves.drop 13096).take 104) 46425000000 0 = true :=
    take_step (n := 2) (t := 104) (b := 13098) rfl rfl ArealUCore.ArealUK.chunk_6548 s49
  have s47 : leavesOK ctxLitU 179824921989757 12 ((leaves.drop 13094).take 106) 46425000000 0 = true :=
    take_step (n := 2) (t := 106) (b := 13096) rfl rfl ArealUCore.ArealUK.chunk_6547 s48
  have s46 : leavesOK ctxLitU 179814400000000 12 ((leaves.drop 13092).take 108) 46425000000 0 = true :=
    take_step (n := 2) (t := 108) (b := 13094) rfl rfl ArealUCore.ArealUK.chunk_6546 s47
  have s45 : leavesOK ctxLitU 43850000000 0 ((leaves.drop 13090).take 110) 46425000000 0 = true :=
    take_step (n := 2) (t := 110) (b := 13092) rfl rfl ArealUCore.ArealUK.chunk_6545 s46
  have s44 : leavesOK ctxLitU 43800000000 0 ((leaves.drop 13088).take 112) 46425000000 0 = true :=
    take_step (n := 2) (t := 112) (b := 13090) rfl rfl ArealUCore.ArealUK.chunk_6544 s45
  have s43 : leavesOK ctxLitU 43750000000 0 ((leaves.drop 13086).take 114) 46425000000 0 = true :=
    take_step (n := 2) (t := 114) (b := 13088) rfl rfl ArealUCore.ArealUK.chunk_6543 s44
  have s42 : leavesOK ctxLitU 43700000000 0 ((leaves.drop 13084).take 116) 46425000000 0 = true :=
    take_step (n := 2) (t := 116) (b := 13086) rfl rfl ArealUCore.ArealUK.chunk_6542 s43
  have s41 : leavesOK ctxLitU 43650000000 0 ((leaves.drop 13082).take 118) 46425000000 0 = true :=
    take_step (n := 2) (t := 118) (b := 13084) rfl rfl ArealUCore.ArealUK.chunk_6541 s42
  have s40 : leavesOK ctxLitU 43625000000 0 ((leaves.drop 13080).take 120) 46425000000 0 = true :=
    take_step (n := 2) (t := 120) (b := 13082) rfl rfl ArealUCore.ArealUK.chunk_6540 s41
  have s39 : leavesOK ctxLitU 43612500000 0 ((leaves.drop 13078).take 122) 46425000000 0 = true :=
    take_step (n := 2) (t := 122) (b := 13080) rfl rfl ArealUCore.ArealUK.chunk_6539 s40
  have s38 : leavesOK ctxLitU 43600000000 0 ((leaves.drop 13076).take 124) 46425000000 0 = true :=
    take_step (n := 2) (t := 124) (b := 13078) rfl rfl ArealUCore.ArealUK.chunk_6538 s39
  have s37 : leavesOK ctxLitU 43575000000 0 ((leaves.drop 13074).take 126) 46425000000 0 = true :=
    take_step (n := 2) (t := 126) (b := 13076) rfl rfl ArealUCore.ArealUK.chunk_6537 s38
  have s36 : leavesOK ctxLitU 43525000000 0 ((leaves.drop 13072).take 128) 46425000000 0 = true :=
    take_step (n := 2) (t := 128) (b := 13074) rfl rfl ArealUCore.ArealUK.chunk_6536 s37
  have s35 : leavesOK ctxLitU 43475000000 0 ((leaves.drop 13070).take 130) 46425000000 0 = true :=
    take_step (n := 2) (t := 130) (b := 13072) rfl rfl ArealUCore.ArealUK.chunk_6535 s36
  have s34 : leavesOK ctxLitU 43425000000 0 ((leaves.drop 13068).take 132) 46425000000 0 = true :=
    take_step (n := 2) (t := 132) (b := 13070) rfl rfl ArealUCore.ArealUK.chunk_6534 s35
  have s33 : leavesOK ctxLitU 43375000000 0 ((leaves.drop 13066).take 134) 46425000000 0 = true :=
    take_step (n := 2) (t := 134) (b := 13068) rfl rfl ArealUCore.ArealUK.chunk_6533 s34
  have s32 : leavesOK ctxLitU 43325000000 0 ((leaves.drop 13064).take 136) 46425000000 0 = true :=
    take_step (n := 2) (t := 136) (b := 13066) rfl rfl ArealUCore.ArealUK.chunk_6532 s33
  have s31 : leavesOK ctxLitU 43275000000 0 ((leaves.drop 13062).take 138) 46425000000 0 = true :=
    take_step (n := 2) (t := 138) (b := 13064) rfl rfl ArealUCore.ArealUK.chunk_6531 s32
  have s30 : leavesOK ctxLitU 43225000000 0 ((leaves.drop 13060).take 140) 46425000000 0 = true :=
    take_step (n := 2) (t := 140) (b := 13062) rfl rfl ArealUCore.ArealUK.chunk_6530 s31
  have s29 : leavesOK ctxLitU 43175000000 0 ((leaves.drop 13058).take 142) 46425000000 0 = true :=
    take_step (n := 2) (t := 142) (b := 13060) rfl rfl ArealUCore.ArealUK.chunk_6529 s30
  have s28 : leavesOK ctxLitU 43125000000 0 ((leaves.drop 13056).take 144) 46425000000 0 = true :=
    take_step (n := 2) (t := 144) (b := 13058) rfl rfl ArealUCore.ArealUK.chunk_6528 s29
  have s27 : leavesOK ctxLitU 43075000000 0 ((leaves.drop 13054).take 146) 46425000000 0 = true :=
    take_step (n := 2) (t := 146) (b := 13056) rfl rfl ArealUCore.ArealUK.chunk_6527 s28
  have s26 : leavesOK ctxLitU 43025000000 0 ((leaves.drop 13052).take 148) 46425000000 0 = true :=
    take_step (n := 2) (t := 148) (b := 13054) rfl rfl ArealUCore.ArealUK.chunk_6526 s27
  have s25 : leavesOK ctxLitU 42975000000 0 ((leaves.drop 13050).take 150) 46425000000 0 = true :=
    take_step (n := 2) (t := 150) (b := 13052) rfl rfl ArealUCore.ArealUK.chunk_6525 s26
  have s24 : leavesOK ctxLitU 42925000000 0 ((leaves.drop 13048).take 152) 46425000000 0 = true :=
    take_step (n := 2) (t := 152) (b := 13050) rfl rfl ArealUCore.ArealUK.chunk_6524 s25
  have s23 : leavesOK ctxLitU 42875000000 0 ((leaves.drop 13046).take 154) 46425000000 0 = true :=
    take_step (n := 2) (t := 154) (b := 13048) rfl rfl ArealUCore.ArealUK.chunk_6523 s24
  have s22 : leavesOK ctxLitU 42825000000 0 ((leaves.drop 13044).take 156) 46425000000 0 = true :=
    take_step (n := 2) (t := 156) (b := 13046) rfl rfl ArealUCore.ArealUK.chunk_6522 s23
  have s21 : leavesOK ctxLitU 42775000000 0 ((leaves.drop 13042).take 158) 46425000000 0 = true :=
    take_step (n := 2) (t := 158) (b := 13044) rfl rfl ArealUCore.ArealUK.chunk_6521 s22
  have s20 : leavesOK ctxLitU 42725000000 0 ((leaves.drop 13040).take 160) 46425000000 0 = true :=
    take_step (n := 2) (t := 160) (b := 13042) rfl rfl ArealUCore.ArealUK.chunk_6520 s21
  have s19 : leavesOK ctxLitU 42675000000 0 ((leaves.drop 13038).take 162) 46425000000 0 = true :=
    take_step (n := 2) (t := 162) (b := 13040) rfl rfl ArealUCore.ArealUK.chunk_6519 s20
  have s18 : leavesOK ctxLitU 42625000000 0 ((leaves.drop 13036).take 164) 46425000000 0 = true :=
    take_step (n := 2) (t := 164) (b := 13038) rfl rfl ArealUCore.ArealUK.chunk_6518 s19
  have s17 : leavesOK ctxLitU 42575000000 0 ((leaves.drop 13034).take 166) 46425000000 0 = true :=
    take_step (n := 2) (t := 166) (b := 13036) rfl rfl ArealUCore.ArealUK.chunk_6517 s18
  have s16 : leavesOK ctxLitU 42537500000 0 ((leaves.drop 13032).take 168) 46425000000 0 = true :=
    take_step (n := 2) (t := 168) (b := 13034) rfl rfl ArealUCore.ArealUK.chunk_6516 s17
  have s15 : leavesOK ctxLitU 42518750000 0 ((leaves.drop 13030).take 170) 46425000000 0 = true :=
    take_step (n := 2) (t := 170) (b := 13032) rfl rfl ArealUCore.ArealUK.chunk_6515 s16
  have s14 : leavesOK ctxLitU 42506250000 0 ((leaves.drop 13028).take 172) 46425000000 0 = true :=
    take_step (n := 2) (t := 172) (b := 13030) rfl rfl ArealUCore.ArealUK.chunk_6514 s15
  have s13 : leavesOK ctxLitU 84993750000 1 ((leaves.drop 13026).take 174) 46425000000 0 = true :=
    take_step (n := 2) (t := 174) (b := 13028) rfl rfl ArealUCore.ArealUK.chunk_6513 s14
  have s12 : leavesOK ctxLitU 169975000000 2 ((leaves.drop 13024).take 176) 46425000000 0 = true :=
    take_step (n := 2) (t := 176) (b := 13026) rfl rfl ArealUCore.ArealUK.chunk_6512 s13
  have s11 : leavesOK ctxLitU 339937500000 3 ((leaves.drop 13022).take 178) 46425000000 0 = true :=
    take_step (n := 2) (t := 178) (b := 13024) rfl rfl ArealUCore.ArealUK.chunk_6511 s12
  have s10 : leavesOK ctxLitU 169956250000 2 ((leaves.drop 13020).take 180) 46425000000 0 = true :=
    take_step (n := 2) (t := 180) (b := 13022) rfl rfl ArealUCore.ArealUK.chunk_6510 s11
  have s9 : leavesOK ctxLitU 84968750000 1 ((leaves.drop 13018).take 182) 46425000000 0 = true :=
    take_step (n := 2) (t := 182) (b := 13020) rfl rfl ArealUCore.ArealUK.chunk_6509 s10
  have s8 : leavesOK ctxLitU 169918750000 2 ((leaves.drop 13016).take 184) 46425000000 0 = true :=
    take_step (n := 2) (t := 184) (b := 13018) rfl rfl ArealUCore.ArealUK.chunk_6508 s9
  have s7 : leavesOK ctxLitU 84950000000 1 ((leaves.drop 13014).take 186) 46425000000 0 = true :=
    take_step (n := 2) (t := 186) (b := 13016) rfl rfl ArealUCore.ArealUK.chunk_6507 s8
  have s6 : leavesOK ctxLitU 84937500000 1 ((leaves.drop 13012).take 188) 46425000000 0 = true :=
    take_step (n := 2) (t := 188) (b := 13014) rfl rfl ArealUCore.ArealUK.chunk_6506 s7
  have s5 : leavesOK ctxLitU 84925000000 1 ((leaves.drop 13010).take 190) 46425000000 0 = true :=
    take_step (n := 2) (t := 190) (b := 13012) rfl rfl ArealUCore.ArealUK.chunk_6505 s6
  have s4 : leavesOK ctxLitU 169837500000 2 ((leaves.drop 13008).take 192) 46425000000 0 = true :=
    take_step (n := 2) (t := 192) (b := 13010) rfl rfl ArealUCore.ArealUK.chunk_6504 s5
  have s3 : leavesOK ctxLitU 84906250000 1 ((leaves.drop 13006).take 194) 46425000000 0 = true :=
    take_step (n := 2) (t := 194) (b := 13008) rfl rfl ArealUCore.ArealUK.chunk_6503 s4
  have s2 : leavesOK ctxLitU 169800000000 2 ((leaves.drop 13004).take 196) 46425000000 0 = true :=
    take_step (n := 2) (t := 196) (b := 13006) rfl rfl ArealUCore.ArealUK.chunk_6502 s3
  have s1 : leavesOK ctxLitU 339575000000 3 ((leaves.drop 13002).take 198) 46425000000 0 = true :=
    take_step (n := 2) (t := 198) (b := 13004) rfl rfl ArealUCore.ArealUK.chunk_6501 s2
  have s0 : leavesOK ctxLitU 169762500000 2 ((leaves.drop 13000).take 200) 46425000000 0 = true :=
    take_step (n := 2) (t := 200) (b := 13002) rfl rfl ArealUCore.ArealUK.chunk_6500 s1
  exact s0

end Areal.UCert

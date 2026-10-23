import ArealUK.Chunk0500
import ArealUK.Chunk0501
import ArealUK.Chunk0502
import ArealUK.Chunk0503
import ArealUK.Chunk0504
import ArealUK.Chunk0505
import ArealUK.Chunk0506
import ArealUK.Chunk0507
import ArealUK.Chunk0508
import ArealUK.Chunk0509
import ArealUK.Chunk0510
import ArealUK.Chunk0511
import ArealUK.Chunk0512
import ArealUK.Chunk0513
import ArealUK.Chunk0514
import ArealUK.Chunk0515
import ArealUK.Chunk0516
import ArealUK.Chunk0517
import ArealUK.Chunk0518
import ArealUK.Chunk0519
import ArealUK.Chunk0520
import ArealUK.Chunk0521
import ArealUK.Chunk0522
import ArealUK.Chunk0523
import ArealUK.Chunk0524
import ArealUK.Chunk0525
import ArealUK.Chunk0526
import ArealUK.Chunk0527
import ArealUK.Chunk0528
import ArealUK.Chunk0529
import ArealUK.Chunk0530
import ArealUK.Chunk0531
import ArealUK.Chunk0532
import ArealUK.Chunk0533
import ArealUK.Chunk0534
import ArealUK.Chunk0535
import ArealUK.Chunk0536
import ArealUK.Chunk0537
import ArealUK.Chunk0538
import ArealUK.Chunk0539
import ArealUK.Chunk0540
import ArealUK.Chunk0541
import ArealUK.Chunk0542
import ArealUK.Chunk0543
import ArealUK.Chunk0544
import ArealUK.Chunk0545
import ArealUK.Chunk0546
import ArealUK.Chunk0547
import ArealUK.Chunk0548
import ArealUK.Chunk0549
import ArealUK.Chunk0550
import ArealUK.Chunk0551
import ArealUK.Chunk0552
import ArealUK.Chunk0553
import ArealUK.Chunk0554
import ArealUK.Chunk0555
import ArealUK.Chunk0556
import ArealUK.Chunk0557
import ArealUK.Chunk0558
import ArealUK.Chunk0559
import ArealUK.Chunk0560
import ArealUK.Chunk0561
import ArealUK.Chunk0562
import ArealUK.Chunk0563
import ArealUK.Chunk0564
import ArealUK.Chunk0565
import ArealUK.Chunk0566
import ArealUK.Chunk0567
import ArealUK.Chunk0568
import ArealUK.Chunk0569
import ArealUK.Chunk0570
import ArealUK.Chunk0571
import ArealUK.Chunk0572
import ArealUK.Chunk0573
import ArealUK.Chunk0574
import ArealUK.Chunk0575
import ArealUK.Chunk0576
import ArealUK.Chunk0577
import ArealUK.Chunk0578
import ArealUK.Chunk0579
import ArealUK.Chunk0580
import ArealUK.Chunk0581
import ArealUK.Chunk0582
import ArealUK.Chunk0583
import ArealUK.Chunk0584
import ArealUK.Chunk0585
import ArealUK.Chunk0586
import ArealUK.Chunk0587
import ArealUK.Chunk0588
import ArealUK.Chunk0589
import ArealUK.Chunk0590
import ArealUK.Chunk0591
import ArealUK.Chunk0592
import ArealUK.Chunk0593
import ArealUK.Chunk0594
import ArealUK.Chunk0595
import ArealUK.Chunk0596
import ArealUK.Chunk0597
import ArealUK.Chunk0598
import ArealUK.Chunk0599
import Areal.UCert.LeavesKGen

/-! Group 5 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_05 : leavesOK ctxLitU 21543750000 3 ((leaves.drop 1000).take 200) 2962500000 0 = true := by
  have s99 := ArealUCore.ArealUK.chunk_0599
  have s98 : leavesOK ctxLitU 2937500000 0 ((leaves.drop 1196).take 4) 2962500000 0 = true :=
    take_step (n := 2) (t := 4) (b := 1198) rfl rfl ArealUCore.ArealUK.chunk_0598 s99
  have s97 : leavesOK ctxLitU 11731250000 2 ((leaves.drop 1194).take 6) 2962500000 0 = true :=
    take_step (n := 2) (t := 6) (b := 1196) rfl rfl ArealUCore.ArealUK.chunk_0597 s98
  have s96 : leavesOK ctxLitU 23443750000 3 ((leaves.drop 1192).take 8) 2962500000 0 = true :=
    take_step (n := 2) (t := 8) (b := 1194) rfl rfl ArealUCore.ArealUK.chunk_0596 s97
  have s95 : leavesOK ctxLitU 23431250000 3 ((leaves.drop 1190).take 10) 2962500000 0 = true :=
    take_step (n := 2) (t := 10) (b := 1192) rfl rfl ArealUCore.ArealUK.chunk_0595 s96
  have s94 : leavesOK ctxLitU 46843750000 4 ((leaves.drop 1188).take 12) 2962500000 0 = true :=
    take_step (n := 2) (t := 12) (b := 1190) rfl rfl ArealUCore.ArealUK.chunk_0594 s95
  have s93 : leavesOK ctxLitU 46831250000 4 ((leaves.drop 1186).take 14) 2962500000 0 = true :=
    take_step (n := 2) (t := 14) (b := 1188) rfl rfl ArealUCore.ArealUK.chunk_0593 s94
  have s92 : leavesOK ctxLitU 23406250000 3 ((leaves.drop 1184).take 16) 2962500000 0 = true :=
    take_step (n := 2) (t := 16) (b := 1186) rfl rfl ArealUCore.ArealUK.chunk_0592 s93
  have s91 : leavesOK ctxLitU 23387500000 3 ((leaves.drop 1182).take 18) 2962500000 0 = true :=
    take_step (n := 2) (t := 18) (b := 1184) rfl rfl ArealUCore.ArealUK.chunk_0591 s92
  have s90 : leavesOK ctxLitU 46737500000 4 ((leaves.drop 1180).take 20) 2962500000 0 = true :=
    take_step (n := 2) (t := 20) (b := 1182) rfl rfl ArealUCore.ArealUK.chunk_0590 s91
  have s89 : leavesOK ctxLitU 46712500000 4 ((leaves.drop 1178).take 22) 2962500000 0 = true :=
    take_step (n := 2) (t := 22) (b := 1180) rfl rfl ArealUCore.ArealUK.chunk_0589 s90
  have s88 : leavesOK ctxLitU 46687500000 4 ((leaves.drop 1176).take 24) 2962500000 0 = true :=
    take_step (n := 2) (t := 24) (b := 1178) rfl rfl ArealUCore.ArealUK.chunk_0588 s89
  have s87 : leavesOK ctxLitU 23325000000 3 ((leaves.drop 1174).take 26) 2962500000 0 = true :=
    take_step (n := 2) (t := 26) (b := 1176) rfl rfl ArealUCore.ArealUK.chunk_0587 s88
  have s86 : leavesOK ctxLitU 23300000000 3 ((leaves.drop 1172).take 28) 2962500000 0 = true :=
    take_step (n := 2) (t := 28) (b := 1174) rfl rfl ArealUCore.ArealUK.chunk_0586 s87
  have s85 : leavesOK ctxLitU 23262500000 3 ((leaves.drop 1170).take 30) 2962500000 0 = true :=
    take_step (n := 2) (t := 30) (b := 1172) rfl rfl ArealUCore.ArealUK.chunk_0585 s86
  have s84 : leavesOK ctxLitU 23237500000 3 ((leaves.drop 1168).take 32) 2962500000 0 = true :=
    take_step (n := 2) (t := 32) (b := 1170) rfl rfl ArealUCore.ArealUK.chunk_0584 s85
  have s83 : leavesOK ctxLitU 46437500000 4 ((leaves.drop 1166).take 34) 2962500000 0 = true :=
    take_step (n := 2) (t := 34) (b := 1168) rfl rfl ArealUCore.ArealUK.chunk_0583 s84
  have s82 : leavesOK ctxLitU 46412500000 4 ((leaves.drop 1164).take 36) 2962500000 0 = true :=
    take_step (n := 2) (t := 36) (b := 1166) rfl rfl ArealUCore.ArealUK.chunk_0582 s83
  have s81 : leavesOK ctxLitU 189964600109215 16 ((leaves.drop 1162).take 38) 2962500000 0 = true :=
    take_step (n := 2) (t := 38) (b := 1164) rfl rfl ArealUCore.ArealUK.chunk_0581 s82
  have s80 : leavesOK ctxLitU 189785000327645 16 ((leaves.drop 1160).take 40) 2962500000 0 = true :=
    take_step (n := 2) (t := 40) (b := 1162) rfl rfl ArealUCore.ArealUK.chunk_0580 s81
  have s79 : leavesOK ctxLitU 94757800327645 15 ((leaves.drop 1158).take 42) 2962500000 0 = true :=
    take_step (n := 2) (t := 42) (b := 1160) rfl rfl ArealUCore.ArealUK.chunk_0579 s80
  have s78 : leavesOK ctxLitU 94578200546075 15 ((leaves.drop 1156).take 44) 2962500000 0 = true :=
    take_step (n := 2) (t := 44) (b := 1158) rfl rfl ArealUCore.ArealUK.chunk_0578 s79
  have s77 : leavesOK ctxLitU 47154400436860 14 ((leaves.drop 1154).take 46) 2962500000 0 = true :=
    take_step (n := 2) (t := 46) (b := 1156) rfl rfl ArealUCore.ArealUK.chunk_0577 s78
  have s76 : leavesOK ctxLitU 11776000000000 12 ((leaves.drop 1152).take 48) 2962500000 0 = true :=
    take_step (n := 2) (t := 48) (b := 1154) rfl rfl ArealUCore.ArealUK.chunk_0576 s77
  have s75 : leavesOK ctxLitU 22950000000 3 ((leaves.drop 1150).take 50) 2962500000 0 = true :=
    take_step (n := 2) (t := 50) (b := 1152) rfl rfl ArealUCore.ArealUK.chunk_0575 s76
  have s74 : leavesOK ctxLitU 45825000000 4 ((leaves.drop 1148).take 52) 2962500000 0 = true :=
    take_step (n := 2) (t := 52) (b := 1150) rfl rfl ArealUCore.ArealUK.chunk_0574 s75
  have s73 : leavesOK ctxLitU 91600000000 5 ((leaves.drop 1146).take 54) 2962500000 0 = true :=
    take_step (n := 2) (t := 54) (b := 1148) rfl rfl ArealUCore.ArealUK.chunk_0573 s74
  have s72 : leavesOK ctxLitU 91550000000 5 ((leaves.drop 1144).take 56) 2962500000 0 = true :=
    take_step (n := 2) (t := 56) (b := 1146) rfl rfl ArealUCore.ArealUK.chunk_0572 s73
  have s71 : leavesOK ctxLitU 45725000000 4 ((leaves.drop 1142).take 58) 2962500000 0 = true :=
    take_step (n := 2) (t := 58) (b := 1144) rfl rfl ArealUCore.ArealUK.chunk_0571 s72
  have s70 : leavesOK ctxLitU 22825000000 3 ((leaves.drop 1140).take 60) 2962500000 0 = true :=
    take_step (n := 2) (t := 60) (b := 1142) rfl rfl ArealUCore.ArealUK.chunk_0570 s71
  have s69 : leavesOK ctxLitU 46593598434435 14 ((leaves.drop 1138).take 62) 2962500000 0 = true :=
    take_step (n := 2) (t := 62) (b := 1140) rfl rfl ArealUCore.ArealUK.chunk_0569 s70
  have s68 : leavesOK ctxLitU 23145596868870 13 ((leaves.drop 1136).take 64) 2962500000 0 = true :=
    take_step (n := 2) (t := 64) (b := 1138) rfl rfl ArealUCore.ArealUK.chunk_0568 s69
  have s67 : leavesOK ctxLitU 11571200000000 12 ((leaves.drop 1134).take 66) 2962500000 0 = true :=
    take_step (n := 2) (t := 66) (b := 1136) rfl rfl ArealUCore.ArealUK.chunk_0567 s68
  have s66 : leavesOK ctxLitU 23083008057404 13 ((leaves.drop 1132).take 68) 2962500000 0 = true :=
    take_step (n := 2) (t := 68) (b := 1134) rfl rfl ArealUCore.ArealUK.chunk_0566 s67
  have s65 : leavesOK ctxLitU 11520000000000 12 ((leaves.drop 1130).take 70) 2962500000 0 = true :=
    take_step (n := 2) (t := 70) (b := 1132) rfl rfl ArealUCore.ArealUK.chunk_0565 s66
  have s64 : leavesOK ctxLitU 22475000000 3 ((leaves.drop 1128).take 72) 2962500000 0 = true :=
    take_step (n := 2) (t := 72) (b := 1130) rfl rfl ArealUCore.ArealUK.chunk_0564 s65
  have s63 : leavesOK ctxLitU 44925000000 4 ((leaves.drop 1126).take 74) 2962500000 0 = true :=
    take_step (n := 2) (t := 74) (b := 1128) rfl rfl ArealUCore.ArealUK.chunk_0563 s64
  have s62 : leavesOK ctxLitU 89825000000 5 ((leaves.drop 1124).take 76) 2962500000 0 = true :=
    take_step (n := 2) (t := 76) (b := 1126) rfl rfl ArealUCore.ArealUK.chunk_0562 s63
  have s61 : leavesOK ctxLitU 89800000000 5 ((leaves.drop 1122).take 78) 2962500000 0 = true :=
    take_step (n := 2) (t := 78) (b := 1124) rfl rfl ArealUCore.ArealUK.chunk_0561 s62
  have s60 : leavesOK ctxLitU 22425000000 3 ((leaves.drop 1120).take 80) 2962500000 0 = true :=
    take_step (n := 2) (t := 80) (b := 1122) rfl rfl ArealUCore.ArealUK.chunk_0560 s61
  have s59 : leavesOK ctxLitU 11450829707786 12 ((leaves.drop 1118).take 82) 2962500000 0 = true :=
    take_step (n := 2) (t := 82) (b := 1120) rfl rfl ArealUCore.ArealUK.chunk_0559 s60
  have s58 : leavesOK ctxLitU 11443200000000 12 ((leaves.drop 1116).take 84) 2962500000 0 = true :=
    take_step (n := 2) (t := 84) (b := 1118) rfl rfl ArealUCore.ArealUK.chunk_0558 s59
  have s57 : leavesOK ctxLitU 22337500000 3 ((leaves.drop 1114).take 86) 2962500000 0 = true :=
    take_step (n := 2) (t := 86) (b := 1116) rfl rfl ArealUCore.ArealUK.chunk_0557 s58
  have s56 : leavesOK ctxLitU 22325000000 3 ((leaves.drop 1112).take 88) 2962500000 0 = true :=
    take_step (n := 2) (t := 88) (b := 1114) rfl rfl ArealUCore.ArealUK.chunk_0556 s57
  have s55 : leavesOK ctxLitU 89281250000 5 ((leaves.drop 1110).take 90) 2962500000 0 = true :=
    take_step (n := 2) (t := 90) (b := 1112) rfl rfl ArealUCore.ArealUK.chunk_0555 s56
  have s54 : leavesOK ctxLitU 22312500000 3 ((leaves.drop 1108).take 92) 2962500000 0 = true :=
    take_step (n := 2) (t := 92) (b := 1110) rfl rfl ArealUCore.ArealUK.chunk_0554 s55
  have s53 : leavesOK ctxLitU 11143750000 2 ((leaves.drop 1106).take 94) 2962500000 0 = true :=
    take_step (n := 2) (t := 94) (b := 1108) rfl rfl ArealUCore.ArealUK.chunk_0553 s54
  have s52 : leavesOK ctxLitU 11131250000 2 ((leaves.drop 1104).take 96) 2962500000 0 = true :=
    take_step (n := 2) (t := 96) (b := 1106) rfl rfl ArealUCore.ArealUK.chunk_0552 s53
  have s51 : leavesOK ctxLitU 22250000000 3 ((leaves.drop 1102).take 98) 2962500000 0 = true :=
    take_step (n := 2) (t := 98) (b := 1104) rfl rfl ArealUCore.ArealUK.chunk_0551 s52
  have s50 : leavesOK ctxLitU 22237500000 3 ((leaves.drop 1100).take 100) 2962500000 0 = true :=
    take_step (n := 2) (t := 100) (b := 1102) rfl rfl ArealUCore.ArealUK.chunk_0550 s51
  have s49 : leavesOK ctxLitU 44462500000 4 ((leaves.drop 1098).take 102) 2962500000 0 = true :=
    take_step (n := 2) (t := 102) (b := 1100) rfl rfl ArealUCore.ArealUK.chunk_0549 s50
  have s48 : leavesOK ctxLitU 44450000000 4 ((leaves.drop 1096).take 104) 2962500000 0 = true :=
    take_step (n := 2) (t := 104) (b := 1098) rfl rfl ArealUCore.ArealUK.chunk_0548 s49
  have s47 : leavesOK ctxLitU 22212500000 3 ((leaves.drop 1094).take 106) 2962500000 0 = true :=
    take_step (n := 2) (t := 106) (b := 1096) rfl rfl ArealUCore.ArealUK.chunk_0547 s48
  have s46 : leavesOK ctxLitU 22200000000 3 ((leaves.drop 1092).take 108) 2962500000 0 = true :=
    take_step (n := 2) (t := 108) (b := 1094) rfl rfl ArealUCore.ArealUK.chunk_0546 s47
  have s45 : leavesOK ctxLitU 22187500000 3 ((leaves.drop 1090).take 110) 2962500000 0 = true :=
    take_step (n := 2) (t := 110) (b := 1092) rfl rfl ArealUCore.ArealUK.chunk_0545 s46
  have s44 : leavesOK ctxLitU 22175000000 3 ((leaves.drop 1088).take 112) 2962500000 0 = true :=
    take_step (n := 2) (t := 112) (b := 1090) rfl rfl ArealUCore.ArealUK.chunk_0544 s45
  have s43 : leavesOK ctxLitU 22162500000 3 ((leaves.drop 1086).take 114) 2962500000 0 = true :=
    take_step (n := 2) (t := 114) (b := 1088) rfl rfl ArealUCore.ArealUK.chunk_0543 s44
  have s42 : leavesOK ctxLitU 44312500000 4 ((leaves.drop 1084).take 116) 2962500000 0 = true :=
    take_step (n := 2) (t := 116) (b := 1086) rfl rfl ArealUCore.ArealUK.chunk_0542 s43
  have s41 : leavesOK ctxLitU 44300000000 4 ((leaves.drop 1082).take 118) 2962500000 0 = true :=
    take_step (n := 2) (t := 118) (b := 1084) rfl rfl ArealUCore.ArealUK.chunk_0541 s42
  have s40 : leavesOK ctxLitU 44287500000 4 ((leaves.drop 1080).take 120) 2962500000 0 = true :=
    take_step (n := 2) (t := 120) (b := 1082) rfl rfl ArealUCore.ArealUK.chunk_0540 s41
  have s39 : leavesOK ctxLitU 44275000000 4 ((leaves.drop 1078).take 122) 2962500000 0 = true :=
    take_step (n := 2) (t := 122) (b := 1080) rfl rfl ArealUCore.ArealUK.chunk_0539 s40
  have s38 : leavesOK ctxLitU 22125000000 3 ((leaves.drop 1076).take 124) 2962500000 0 = true :=
    take_step (n := 2) (t := 124) (b := 1078) rfl rfl ArealUCore.ArealUK.chunk_0538 s39
  have s37 : leavesOK ctxLitU 22112500000 3 ((leaves.drop 1074).take 126) 2962500000 0 = true :=
    take_step (n := 2) (t := 126) (b := 1076) rfl rfl ArealUCore.ArealUK.chunk_0537 s38
  have s36 : leavesOK ctxLitU 22100000000 3 ((leaves.drop 1072).take 128) 2962500000 0 = true :=
    take_step (n := 2) (t := 128) (b := 1074) rfl rfl ArealUCore.ArealUK.chunk_0536 s37
  have s35 : leavesOK ctxLitU 22087500000 3 ((leaves.drop 1070).take 130) 2962500000 0 = true :=
    take_step (n := 2) (t := 130) (b := 1072) rfl rfl ArealUCore.ArealUK.chunk_0535 s36
  have s34 : leavesOK ctxLitU 44156250000 4 ((leaves.drop 1068).take 132) 2962500000 0 = true :=
    take_step (n := 2) (t := 132) (b := 1070) rfl rfl ArealUCore.ArealUK.chunk_0534 s35
  have s33 : leavesOK ctxLitU 44143750000 4 ((leaves.drop 1066).take 134) 2962500000 0 = true :=
    take_step (n := 2) (t := 134) (b := 1068) rfl rfl ArealUCore.ArealUK.chunk_0533 s34
  have s32 : leavesOK ctxLitU 44131250000 4 ((leaves.drop 1064).take 136) 2962500000 0 = true :=
    take_step (n := 2) (t := 136) (b := 1066) rfl rfl ArealUCore.ArealUK.chunk_0532 s33
  have s31 : leavesOK ctxLitU 22056250000 3 ((leaves.drop 1062).take 138) 2962500000 0 = true :=
    take_step (n := 2) (t := 138) (b := 1064) rfl rfl ArealUCore.ArealUK.chunk_0531 s32
  have s30 : leavesOK ctxLitU 11018750000 2 ((leaves.drop 1060).take 140) 2962500000 0 = true :=
    take_step (n := 2) (t := 140) (b := 1062) rfl rfl ArealUCore.ArealUK.chunk_0530 s31
  have s29 : leavesOK ctxLitU 11006250000 2 ((leaves.drop 1058).take 142) 2962500000 0 = true :=
    take_step (n := 2) (t := 142) (b := 1060) rfl rfl ArealUCore.ArealUK.chunk_0529 s30
  have s28 : leavesOK ctxLitU 10993750000 2 ((leaves.drop 1056).take 144) 2962500000 0 = true :=
    take_step (n := 2) (t := 144) (b := 1058) rfl rfl ArealUCore.ArealUK.chunk_0528 s29
  have s27 : leavesOK ctxLitU 87918750000 5 ((leaves.drop 1054).take 146) 2962500000 0 = true :=
    take_step (n := 2) (t := 146) (b := 1056) rfl rfl ArealUCore.ArealUK.chunk_0527 s28
  have s26 : leavesOK ctxLitU 43950000000 4 ((leaves.drop 1052).take 148) 2962500000 0 = true :=
    take_step (n := 2) (t := 148) (b := 1054) rfl rfl ArealUCore.ArealUK.chunk_0526 s27
  have s25 : leavesOK ctxLitU 21962500000 3 ((leaves.drop 1050).take 150) 2962500000 0 = true :=
    take_step (n := 2) (t := 150) (b := 1052) rfl rfl ArealUCore.ArealUK.chunk_0525 s26
  have s24 : leavesOK ctxLitU 11229225136221 12 ((leaves.drop 1048).take 152) 2962500000 0 = true :=
    take_step (n := 2) (t := 152) (b := 1050) rfl rfl ArealUCore.ArealUK.chunk_0524 s25
  have s23 : leavesOK ctxLitU 22442025136218 13 ((leaves.drop 1046).take 154) 2962500000 0 = true :=
    take_step (n := 2) (t := 154) (b := 1048) rfl rfl ArealUCore.ArealUK.chunk_0523 s24
  have s22 : leavesOK ctxLitU 89718825136218 15 ((leaves.drop 1044).take 156) 2962500000 0 = true :=
    take_step (n := 2) (t := 156) (b := 1046) rfl rfl ArealUCore.ArealUK.chunk_0522 s23
  have s21 : leavesOK ctxLitU 179404800000000 16 ((leaves.drop 1042).take 158) 2962500000 0 = true :=
    take_step (n := 2) (t := 158) (b := 1044) rfl rfl ArealUCore.ArealUK.chunk_0521 s22
  have s20 : leavesOK ctxLitU 350387500000 7 ((leaves.drop 1040).take 160) 2962500000 0 = true :=
    take_step (n := 2) (t := 160) (b := 1042) rfl rfl ArealUCore.ArealUK.chunk_0520 s21
  have s19 : leavesOK ctxLitU 87587500000 5 ((leaves.drop 1038).take 162) 2962500000 0 = true :=
    take_step (n := 2) (t := 162) (b := 1040) rfl rfl ArealUCore.ArealUK.chunk_0519 s20
  have s18 : leavesOK ctxLitU 21887500000 3 ((leaves.drop 1036).take 164) 2962500000 0 = true :=
    take_step (n := 2) (t := 164) (b := 1038) rfl rfl ArealUCore.ArealUK.chunk_0518 s19
  have s17 : leavesOK ctxLitU 5462500000 1 ((leaves.drop 1034).take 166) 2962500000 0 = true :=
    take_step (n := 2) (t := 166) (b := 1036) rfl rfl ArealUCore.ArealUK.chunk_0517 s18
  have s16 : leavesOK ctxLitU 11148573195703 12 ((leaves.drop 1032).take 168) 2962500000 0 = true :=
    take_step (n := 2) (t := 168) (b := 1034) rfl rfl ArealUCore.ArealUK.chunk_0516 s17
  have s15 : leavesOK ctxLitU 11136000000000 12 ((leaves.drop 1030).take 170) 2962500000 0 = true :=
    take_step (n := 2) (t := 170) (b := 1032) rfl rfl ArealUCore.ArealUK.chunk_0515 s16
  have s14 : leavesOK ctxLitU 5425000000 1 ((leaves.drop 1028).take 172) 2962500000 0 = true :=
    take_step (n := 2) (t := 172) (b := 1030) rfl rfl ArealUCore.ArealUK.chunk_0514 s15
  have s13 : leavesOK ctxLitU 21687500000 3 ((leaves.drop 1026).take 174) 2962500000 0 = true :=
    take_step (n := 2) (t := 174) (b := 1028) rfl rfl ArealUCore.ArealUK.chunk_0513 s14
  have s12 : leavesOK ctxLitU 21668750000 3 ((leaves.drop 1024).take 176) 2962500000 0 = true :=
    take_step (n := 2) (t := 176) (b := 1026) rfl rfl ArealUCore.ArealUK.chunk_0512 s13
  have s11 : leavesOK ctxLitU 43325000000 4 ((leaves.drop 1022).take 178) 2962500000 0 = true :=
    take_step (n := 2) (t := 178) (b := 1024) rfl rfl ArealUCore.ArealUK.chunk_0511 s12
  have s10 : leavesOK ctxLitU 43312500000 4 ((leaves.drop 1020).take 180) 2962500000 0 = true :=
    take_step (n := 2) (t := 180) (b := 1022) rfl rfl ArealUCore.ArealUK.chunk_0510 s11
  have s9 : leavesOK ctxLitU 21643750000 3 ((leaves.drop 1018).take 182) 2962500000 0 = true :=
    take_step (n := 2) (t := 182) (b := 1020) rfl rfl ArealUCore.ArealUK.chunk_0509 s10
  have s8 : leavesOK ctxLitU 43268750000 4 ((leaves.drop 1016).take 184) 2962500000 0 = true :=
    take_step (n := 2) (t := 184) (b := 1018) rfl rfl ArealUCore.ArealUK.chunk_0508 s9
  have s7 : leavesOK ctxLitU 43256250000 4 ((leaves.drop 1014).take 186) 2962500000 0 = true :=
    take_step (n := 2) (t := 186) (b := 1016) rfl rfl ArealUCore.ArealUK.chunk_0507 s8
  have s6 : leavesOK ctxLitU 21618750000 3 ((leaves.drop 1012).take 188) 2962500000 0 = true :=
    take_step (n := 2) (t := 188) (b := 1014) rfl rfl ArealUCore.ArealUK.chunk_0506 s7
  have s5 : leavesOK ctxLitU 10800000000 2 ((leaves.drop 1010).take 190) 2962500000 0 = true :=
    take_step (n := 2) (t := 190) (b := 1012) rfl rfl ArealUCore.ArealUK.chunk_0505 s6
  have s4 : leavesOK ctxLitU 21581250000 3 ((leaves.drop 1008).take 192) 2962500000 0 = true :=
    take_step (n := 2) (t := 192) (b := 1010) rfl rfl ArealUCore.ArealUK.chunk_0504 s5
  have s3 : leavesOK ctxLitU 21568750000 3 ((leaves.drop 1006).take 194) 2962500000 0 = true :=
    take_step (n := 2) (t := 194) (b := 1008) rfl rfl ArealUCore.ArealUK.chunk_0503 s4
  have s2 : leavesOK ctxLitU 43125000000 4 ((leaves.drop 1004).take 196) 2962500000 0 = true :=
    take_step (n := 2) (t := 196) (b := 1006) rfl rfl ArealUCore.ArealUK.chunk_0502 s3
  have s1 : leavesOK ctxLitU 43112500000 4 ((leaves.drop 1002).take 198) 2962500000 0 = true :=
    take_step (n := 2) (t := 198) (b := 1004) rfl rfl ArealUCore.ArealUK.chunk_0501 s2
  have s0 : leavesOK ctxLitU 21543750000 3 ((leaves.drop 1000).take 200) 2962500000 0 = true :=
    take_step (n := 2) (t := 200) (b := 1002) rfl rfl ArealUCore.ArealUK.chunk_0500 s1
  exact s0

end Areal.UCert

import ArealUK.Chunk0600
import ArealUK.Chunk0601
import ArealUK.Chunk0602
import ArealUK.Chunk0603
import ArealUK.Chunk0604
import ArealUK.Chunk0605
import ArealUK.Chunk0606
import ArealUK.Chunk0607
import ArealUK.Chunk0608
import ArealUK.Chunk0609
import ArealUK.Chunk0610
import ArealUK.Chunk0611
import ArealUK.Chunk0612
import ArealUK.Chunk0613
import ArealUK.Chunk0614
import ArealUK.Chunk0615
import ArealUK.Chunk0616
import ArealUK.Chunk0617
import ArealUK.Chunk0618
import ArealUK.Chunk0619
import ArealUK.Chunk0620
import ArealUK.Chunk0621
import ArealUK.Chunk0622
import ArealUK.Chunk0623
import ArealUK.Chunk0624
import ArealUK.Chunk0625
import ArealUK.Chunk0626
import ArealUK.Chunk0627
import ArealUK.Chunk0628
import ArealUK.Chunk0629
import ArealUK.Chunk0630
import ArealUK.Chunk0631
import ArealUK.Chunk0632
import ArealUK.Chunk0633
import ArealUK.Chunk0634
import ArealUK.Chunk0635
import ArealUK.Chunk0636
import ArealUK.Chunk0637
import ArealUK.Chunk0638
import ArealUK.Chunk0639
import ArealUK.Chunk0640
import ArealUK.Chunk0641
import ArealUK.Chunk0642
import ArealUK.Chunk0643
import ArealUK.Chunk0644
import ArealUK.Chunk0645
import ArealUK.Chunk0646
import ArealUK.Chunk0647
import ArealUK.Chunk0648
import ArealUK.Chunk0649
import ArealUK.Chunk0650
import ArealUK.Chunk0651
import ArealUK.Chunk0652
import ArealUK.Chunk0653
import ArealUK.Chunk0654
import ArealUK.Chunk0655
import ArealUK.Chunk0656
import ArealUK.Chunk0657
import ArealUK.Chunk0658
import ArealUK.Chunk0659
import ArealUK.Chunk0660
import ArealUK.Chunk0661
import ArealUK.Chunk0662
import ArealUK.Chunk0663
import ArealUK.Chunk0664
import ArealUK.Chunk0665
import ArealUK.Chunk0666
import ArealUK.Chunk0667
import ArealUK.Chunk0668
import ArealUK.Chunk0669
import ArealUK.Chunk0670
import ArealUK.Chunk0671
import ArealUK.Chunk0672
import ArealUK.Chunk0673
import ArealUK.Chunk0674
import ArealUK.Chunk0675
import ArealUK.Chunk0676
import ArealUK.Chunk0677
import ArealUK.Chunk0678
import ArealUK.Chunk0679
import ArealUK.Chunk0680
import ArealUK.Chunk0681
import ArealUK.Chunk0682
import ArealUK.Chunk0683
import ArealUK.Chunk0684
import ArealUK.Chunk0685
import ArealUK.Chunk0686
import ArealUK.Chunk0687
import ArealUK.Chunk0688
import ArealUK.Chunk0689
import ArealUK.Chunk0690
import ArealUK.Chunk0691
import ArealUK.Chunk0692
import ArealUK.Chunk0693
import ArealUK.Chunk0694
import ArealUK.Chunk0695
import ArealUK.Chunk0696
import ArealUK.Chunk0697
import ArealUK.Chunk0698
import ArealUK.Chunk0699
import Areal.UCert.LeavesKGen

/-! Group 6 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_06 : leavesOK ctxLitU 2962500000 0 ((leaves.drop 1200).take 200) 28325000000 3 = true := by
  have s99 := ArealUCore.ArealUK.chunk_0699
  have s98 : leavesOK ctxLitU 28300000000 3 ((leaves.drop 1396).take 4) 28325000000 3 = true :=
    take_step (n := 2) (t := 4) (b := 1398) rfl rfl ArealUCore.ArealUK.chunk_0698 s99
  have s97 : leavesOK ctxLitU 28287500000 3 ((leaves.drop 1394).take 6) 28325000000 3 = true :=
    take_step (n := 2) (t := 6) (b := 1396) rfl rfl ArealUCore.ArealUK.chunk_0697 s98
  have s96 : leavesOK ctxLitU 28275000000 3 ((leaves.drop 1392).take 8) 28325000000 3 = true :=
    take_step (n := 2) (t := 8) (b := 1394) rfl rfl ArealUCore.ArealUK.chunk_0696 s97
  have s95 : leavesOK ctxLitU 28262500000 3 ((leaves.drop 1390).take 10) 28325000000 3 = true :=
    take_step (n := 2) (t := 10) (b := 1392) rfl rfl ArealUCore.ArealUK.chunk_0695 s96
  have s94 : leavesOK ctxLitU 28250000000 3 ((leaves.drop 1388).take 12) 28325000000 3 = true :=
    take_step (n := 2) (t := 12) (b := 1390) rfl rfl ArealUCore.ArealUK.chunk_0694 s95
  have s93 : leavesOK ctxLitU 28237500000 3 ((leaves.drop 1386).take 14) 28325000000 3 = true :=
    take_step (n := 2) (t := 14) (b := 1388) rfl rfl ArealUCore.ArealUK.chunk_0693 s94
  have s92 : leavesOK ctxLitU 28225000000 3 ((leaves.drop 1384).take 16) 28325000000 3 = true :=
    take_step (n := 2) (t := 16) (b := 1386) rfl rfl ArealUCore.ArealUK.chunk_0692 s93
  have s91 : leavesOK ctxLitU 28212500000 3 ((leaves.drop 1382).take 18) 28325000000 3 = true :=
    take_step (n := 2) (t := 18) (b := 1384) rfl rfl ArealUCore.ArealUK.chunk_0691 s92
  have s90 : leavesOK ctxLitU 28200000000 3 ((leaves.drop 1380).take 20) 28325000000 3 = true :=
    take_step (n := 2) (t := 20) (b := 1382) rfl rfl ArealUCore.ArealUK.chunk_0690 s91
  have s89 : leavesOK ctxLitU 28187500000 3 ((leaves.drop 1378).take 22) 28325000000 3 = true :=
    take_step (n := 2) (t := 22) (b := 1380) rfl rfl ArealUCore.ArealUK.chunk_0689 s90
  have s88 : leavesOK ctxLitU 28175000000 3 ((leaves.drop 1376).take 24) 28325000000 3 = true :=
    take_step (n := 2) (t := 24) (b := 1378) rfl rfl ArealUCore.ArealUK.chunk_0688 s89
  have s87 : leavesOK ctxLitU 14075000000 2 ((leaves.drop 1374).take 26) 28325000000 3 = true :=
    take_step (n := 2) (t := 26) (b := 1376) rfl rfl ArealUCore.ArealUK.chunk_0687 s88
  have s86 : leavesOK ctxLitU 28137500000 3 ((leaves.drop 1372).take 28) 28325000000 3 = true :=
    take_step (n := 2) (t := 28) (b := 1374) rfl rfl ArealUCore.ArealUK.chunk_0686 s87
  have s85 : leavesOK ctxLitU 28125000000 3 ((leaves.drop 1370).take 30) 28325000000 3 = true :=
    take_step (n := 2) (t := 30) (b := 1372) rfl rfl ArealUCore.ArealUK.chunk_0685 s86
  have s84 : leavesOK ctxLitU 28112500000 3 ((leaves.drop 1368).take 32) 28325000000 3 = true :=
    take_step (n := 2) (t := 32) (b := 1370) rfl rfl ArealUCore.ArealUK.chunk_0684 s85
  have s83 : leavesOK ctxLitU 56206250000 4 ((leaves.drop 1366).take 34) 28325000000 3 = true :=
    take_step (n := 2) (t := 34) (b := 1368) rfl rfl ArealUCore.ArealUK.chunk_0683 s84
  have s82 : leavesOK ctxLitU 14043750000 2 ((leaves.drop 1364).take 36) 28325000000 3 = true :=
    take_step (n := 2) (t := 36) (b := 1366) rfl rfl ArealUCore.ArealUK.chunk_0682 s83
  have s81 : leavesOK ctxLitU 7012500000 1 ((leaves.drop 1362).take 38) 28325000000 3 = true :=
    take_step (n := 2) (t := 38) (b := 1364) rfl rfl ArealUCore.ArealUK.chunk_0681 s82
  have s80 : leavesOK ctxLitU 28018750000 3 ((leaves.drop 1360).take 40) 28325000000 3 = true :=
    take_step (n := 2) (t := 40) (b := 1362) rfl rfl ArealUCore.ArealUK.chunk_0680 s81
  have s79 : leavesOK ctxLitU 56025000000 4 ((leaves.drop 1358).take 42) 28325000000 3 = true :=
    take_step (n := 2) (t := 42) (b := 1360) rfl rfl ArealUCore.ArealUK.chunk_0679 s80
  have s78 : leavesOK ctxLitU 56006250000 4 ((leaves.drop 1356).take 44) 28325000000 3 = true :=
    take_step (n := 2) (t := 44) (b := 1358) rfl rfl ArealUCore.ArealUK.chunk_0678 s79
  have s77 : leavesOK ctxLitU 57310114396327 14 ((leaves.drop 1354).take 46) 28325000000 3 = true :=
    take_step (n := 2) (t := 46) (b := 1356) rfl rfl ArealUCore.ArealUK.chunk_0677 s78
  have s76 : leavesOK ctxLitU 28604228792654 13 ((leaves.drop 1352).take 48) 28325000000 3 = true :=
    take_step (n := 2) (t := 48) (b := 1354) rfl rfl ArealUCore.ArealUK.chunk_0676 s77
  have s75 : leavesOK ctxLitU 14284800000000 12 ((leaves.drop 1350).take 50) 28325000000 3 = true :=
    take_step (n := 2) (t := 50) (b := 1352) rfl rfl ArealUCore.ArealUK.chunk_0675 s76
  have s74 : leavesOK ctxLitU 27875000000 3 ((leaves.drop 1348).take 52) 28325000000 3 = true :=
    take_step (n := 2) (t := 52) (b := 1350) rfl rfl ArealUCore.ArealUK.chunk_0674 s75
  have s73 : leavesOK ctxLitU 55712500000 4 ((leaves.drop 1346).take 54) 28325000000 3 = true :=
    take_step (n := 2) (t := 54) (b := 1348) rfl rfl ArealUCore.ArealUK.chunk_0673 s74
  have s72 : leavesOK ctxLitU 111400000000 5 ((leaves.drop 1344).take 56) 28325000000 3 = true :=
    take_step (n := 2) (t := 56) (b := 1346) rfl rfl ArealUCore.ArealUK.chunk_0672 s73
  have s71 : leavesOK ctxLitU 27825000000 3 ((leaves.drop 1342).take 58) 28325000000 3 = true :=
    take_step (n := 2) (t := 58) (b := 1344) rfl rfl ArealUCore.ArealUK.chunk_0671 s72
  have s70 : leavesOK ctxLitU 13875000000 2 ((leaves.drop 1340).take 60) 28325000000 3 = true :=
    take_step (n := 2) (t := 60) (b := 1342) rfl rfl ArealUCore.ArealUK.chunk_0670 s71
  have s69 : leavesOK ctxLitU 27700000000 3 ((leaves.drop 1338).take 62) 28325000000 3 = true :=
    take_step (n := 2) (t := 62) (b := 1340) rfl rfl ArealUCore.ArealUK.chunk_0669 s70
  have s68 : leavesOK ctxLitU 55325000000 4 ((leaves.drop 1336).take 64) 28325000000 3 = true :=
    take_step (n := 2) (t := 64) (b := 1338) rfl rfl ArealUCore.ArealUK.chunk_0668 s69
  have s67 : leavesOK ctxLitU 110600000000 5 ((leaves.drop 1334).take 66) 28325000000 3 = true :=
    take_step (n := 2) (t := 66) (b := 1336) rfl rfl ArealUCore.ArealUK.chunk_0667 s68
  have s66 : leavesOK ctxLitU 55250000000 4 ((leaves.drop 1332).take 68) 28325000000 3 = true :=
    take_step (n := 2) (t := 68) (b := 1334) rfl rfl ArealUCore.ArealUK.chunk_0666 s67
  have s65 : leavesOK ctxLitU 55200000000 4 ((leaves.drop 1330).take 70) 28325000000 3 = true :=
    take_step (n := 2) (t := 70) (b := 1332) rfl rfl ArealUCore.ArealUK.chunk_0665 s66
  have s64 : leavesOK ctxLitU 56377548681316 14 ((leaves.drop 1328).take 72) 28325000000 3 = true :=
    take_step (n := 2) (t := 72) (b := 1330) rfl rfl ArealUCore.ArealUK.chunk_0664 s65
  have s63 : leavesOK ctxLitU 14057574340655 12 ((leaves.drop 1326).take 74) 28325000000 3 = true :=
    take_step (n := 2) (t := 74) (b := 1328) rfl rfl ArealUCore.ArealUK.chunk_0663 s64
  have s62 : leavesOK ctxLitU 13675000000 2 ((leaves.drop 1324).take 76) 28325000000 3 = true :=
    take_step (n := 2) (t := 76) (b := 1326) rfl rfl ArealUCore.ArealUK.chunk_0662 s63
  have s61 : leavesOK ctxLitU 27300000000 3 ((leaves.drop 1322).take 78) 28325000000 3 = true :=
    take_step (n := 2) (t := 78) (b := 1324) rfl rfl ArealUCore.ArealUK.chunk_0661 s62
  have s60 : leavesOK ctxLitU 54550000000 4 ((leaves.drop 1320).take 80) 28325000000 3 = true :=
    take_step (n := 2) (t := 80) (b := 1322) rfl rfl ArealUCore.ArealUK.chunk_0660 s61
  have s59 : leavesOK ctxLitU 218125000000 6 ((leaves.drop 1318).take 82) 28325000000 3 = true :=
    take_step (n := 2) (t := 82) (b := 1320) rfl rfl ArealUCore.ArealUK.chunk_0659 s60
  have s58 : leavesOK ctxLitU 109025000000 5 ((leaves.drop 1316).take 84) 28325000000 3 = true :=
    take_step (n := 2) (t := 84) (b := 1318) rfl rfl ArealUCore.ArealUK.chunk_0658 s59
  have s57 : leavesOK ctxLitU 54475000000 4 ((leaves.drop 1314).take 86) 28325000000 3 = true :=
    take_step (n := 2) (t := 86) (b := 1316) rfl rfl ArealUCore.ArealUK.chunk_0657 s58
  have s56 : leavesOK ctxLitU 27200000000 3 ((leaves.drop 1312).take 88) 28325000000 3 = true :=
    take_step (n := 2) (t := 88) (b := 1314) rfl rfl ArealUCore.ArealUK.chunk_0656 s57
  have s55 : leavesOK ctxLitU 27727614132298 13 ((leaves.drop 1310).take 90) 28325000000 3 = true :=
    take_step (n := 2) (t := 90) (b := 1312) rfl rfl ArealUCore.ArealUK.chunk_0655 s56
  have s54 : leavesOK ctxLitU 13824000000000 12 ((leaves.drop 1308).take 92) 28325000000 3 = true :=
    take_step (n := 2) (t := 92) (b := 1310) rfl rfl ArealUCore.ArealUK.chunk_0654 s55
  have s53 : leavesOK ctxLitU 26925000000 3 ((leaves.drop 1306).take 94) 28325000000 3 = true :=
    take_step (n := 2) (t := 94) (b := 1308) rfl rfl ArealUCore.ArealUK.chunk_0653 s54
  have s52 : leavesOK ctxLitU 107625000000 5 ((leaves.drop 1304).take 96) 28325000000 3 = true :=
    take_step (n := 2) (t := 96) (b := 1306) rfl rfl ArealUCore.ArealUK.chunk_0652 s53
  have s51 : leavesOK ctxLitU 215200000000 6 ((leaves.drop 1302).take 98) 28325000000 3 = true :=
    take_step (n := 2) (t := 98) (b := 1304) rfl rfl ArealUCore.ArealUK.chunk_0651 s52
  have s50 : leavesOK ctxLitU 53750000000 4 ((leaves.drop 1300).take 100) 28325000000 3 = true :=
    take_step (n := 2) (t := 100) (b := 1302) rfl rfl ArealUCore.ArealUK.chunk_0650 s51
  have s49 : leavesOK ctxLitU 13400000000 2 ((leaves.drop 1298).take 102) 28325000000 3 = true :=
    take_step (n := 2) (t := 102) (b := 1300) rfl rfl ArealUCore.ArealUK.chunk_0649 s50
  have s48 : leavesOK ctxLitU 13680865026009 12 ((leaves.drop 1296).take 104) 28325000000 3 = true :=
    take_step (n := 2) (t := 104) (b := 1298) rfl rfl ArealUCore.ArealUK.chunk_0648 s49
  have s47 : leavesOK ctxLitU 27238400000000 13 ((leaves.drop 1294).take 106) 28325000000 3 = true :=
    take_step (n := 2) (t := 106) (b := 1296) rfl rfl ArealUCore.ArealUK.chunk_0647 s48
  have s46 : leavesOK ctxLitU 26550000000 3 ((leaves.drop 1292).take 108) 28325000000 3 = true :=
    take_step (n := 2) (t := 108) (b := 1294) rfl rfl ArealUCore.ArealUK.chunk_0646 s47
  have s45 : leavesOK ctxLitU 53050000000 4 ((leaves.drop 1290).take 110) 28325000000 3 = true :=
    take_step (n := 2) (t := 110) (b := 1292) rfl rfl ArealUCore.ArealUK.chunk_0645 s46
  have s44 : leavesOK ctxLitU 106050000000 5 ((leaves.drop 1288).take 112) 28325000000 3 = true :=
    take_step (n := 2) (t := 112) (b := 1290) rfl rfl ArealUCore.ArealUK.chunk_0644 s45
  have s43 : leavesOK ctxLitU 52975000000 4 ((leaves.drop 1286).take 114) 28325000000 3 = true :=
    take_step (n := 2) (t := 114) (b := 1288) rfl rfl ArealUCore.ArealUK.chunk_0643 s44
  have s42 : leavesOK ctxLitU 26450000000 3 ((leaves.drop 1284).take 116) 28325000000 3 = true :=
    take_step (n := 2) (t := 116) (b := 1286) rfl rfl ArealUCore.ArealUK.chunk_0642 s43
  have s41 : leavesOK ctxLitU 26400000000 3 ((leaves.drop 1282).take 118) 28325000000 3 = true :=
    take_step (n := 2) (t := 118) (b := 1284) rfl rfl ArealUCore.ArealUK.chunk_0641 s42
  have s40 : leavesOK ctxLitU 13175000000 2 ((leaves.drop 1280).take 120) 28325000000 3 = true :=
    take_step (n := 2) (t := 120) (b := 1282) rfl rfl ArealUCore.ArealUK.chunk_0640 s41
  have s39 : leavesOK ctxLitU 13150000000 2 ((leaves.drop 1278).take 122) 28325000000 3 = true :=
    take_step (n := 2) (t := 122) (b := 1280) rfl rfl ArealUCore.ArealUK.chunk_0639 s40
  have s38 : leavesOK ctxLitU 215194858071195 16 ((leaves.drop 1276).take 124) 28325000000 3 = true :=
    take_step (n := 2) (t := 124) (b := 1278) rfl rfl ArealUCore.ArealUK.chunk_0638 s39
  have s37 : leavesOK ctxLitU 430287819370868 17 ((leaves.drop 1274).take 126) 28325000000 3 = true :=
    take_step (n := 2) (t := 126) (b := 1276) rfl rfl ArealUCore.ArealUK.chunk_0637 s38
  have s36 : leavesOK ctxLitU 215042012913912 16 ((leaves.drop 1272).take 128) 28325000000 3 = true :=
    take_step (n := 2) (t := 128) (b := 1274) rfl rfl ArealUCore.ArealUK.chunk_0636 s37
  have s35 : leavesOK ctxLitU 53658606456956 14 ((leaves.drop 1270).take 130) 28325000000 3 = true :=
    take_step (n := 2) (t := 130) (b := 1272) rfl rfl ArealUCore.ArealUK.chunk_0635 s36
  have s34 : leavesOK ctxLitU 13414400000000 12 ((leaves.drop 1268).take 132) 28325000000 3 = true :=
    take_step (n := 2) (t := 132) (b := 1270) rfl rfl ArealUCore.ArealUK.chunk_0634 s35
  have s33 : leavesOK ctxLitU 13087500000 2 ((leaves.drop 1266).take 134) 28325000000 3 = true :=
    take_step (n := 2) (t := 134) (b := 1268) rfl rfl ArealUCore.ArealUK.chunk_0633 s34
  have s32 : leavesOK ctxLitU 13068750000 2 ((leaves.drop 1264).take 136) 28325000000 3 = true :=
    take_step (n := 2) (t := 136) (b := 1266) rfl rfl ArealUCore.ArealUK.chunk_0632 s33
  have s31 : leavesOK ctxLitU 52256250000 4 ((leaves.drop 1262).take 138) 28325000000 3 = true :=
    take_step (n := 2) (t := 138) (b := 1264) rfl rfl ArealUCore.ArealUK.chunk_0631 s32
  have s30 : leavesOK ctxLitU 26118750000 3 ((leaves.drop 1260).take 140) 28325000000 3 = true :=
    take_step (n := 2) (t := 140) (b := 1262) rfl rfl ArealUCore.ArealUK.chunk_0630 s31
  have s29 : leavesOK ctxLitU 13050000000 2 ((leaves.drop 1258).take 142) 28325000000 3 = true :=
    take_step (n := 2) (t := 142) (b := 1260) rfl rfl ArealUCore.ArealUK.chunk_0629 s30
  have s28 : leavesOK ctxLitU 13037500000 2 ((leaves.drop 1256).take 144) 28325000000 3 = true :=
    take_step (n := 2) (t := 144) (b := 1258) rfl rfl ArealUCore.ArealUK.chunk_0628 s29
  have s27 : leavesOK ctxLitU 13025000000 2 ((leaves.drop 1254).take 146) 28325000000 3 = true :=
    take_step (n := 2) (t := 146) (b := 1256) rfl rfl ArealUCore.ArealUK.chunk_0627 s28
  have s26 : leavesOK ctxLitU 26031250000 3 ((leaves.drop 1252).take 148) 28325000000 3 = true :=
    take_step (n := 2) (t := 148) (b := 1254) rfl rfl ArealUCore.ArealUK.chunk_0626 s27
  have s25 : leavesOK ctxLitU 26018750000 3 ((leaves.drop 1250).take 150) 28325000000 3 = true :=
    take_step (n := 2) (t := 150) (b := 1252) rfl rfl ArealUCore.ArealUK.chunk_0625 s26
  have s24 : leavesOK ctxLitU 13000000000 2 ((leaves.drop 1248).take 152) 28325000000 3 = true :=
    take_step (n := 2) (t := 152) (b := 1250) rfl rfl ArealUCore.ArealUK.chunk_0624 s25
  have s23 : leavesOK ctxLitU 12987500000 2 ((leaves.drop 1246).take 154) 28325000000 3 = true :=
    take_step (n := 2) (t := 154) (b := 1248) rfl rfl ArealUCore.ArealUK.chunk_0623 s24
  have s22 : leavesOK ctxLitU 12975000000 2 ((leaves.drop 1244).take 156) 28325000000 3 = true :=
    take_step (n := 2) (t := 156) (b := 1246) rfl rfl ArealUCore.ArealUK.chunk_0622 s23
  have s21 : leavesOK ctxLitU 25937500000 3 ((leaves.drop 1242).take 158) 28325000000 3 = true :=
    take_step (n := 2) (t := 158) (b := 1244) rfl rfl ArealUCore.ArealUK.chunk_0621 s22
  have s20 : leavesOK ctxLitU 51862500000 4 ((leaves.drop 1240).take 160) 28325000000 3 = true :=
    take_step (n := 2) (t := 160) (b := 1242) rfl rfl ArealUCore.ArealUK.chunk_0620 s21
  have s19 : leavesOK ctxLitU 51850000000 4 ((leaves.drop 1238).take 162) 28325000000 3 = true :=
    take_step (n := 2) (t := 162) (b := 1240) rfl rfl ArealUCore.ArealUK.chunk_0619 s20
  have s18 : leavesOK ctxLitU 25912500000 3 ((leaves.drop 1236).take 164) 28325000000 3 = true :=
    take_step (n := 2) (t := 164) (b := 1238) rfl rfl ArealUCore.ArealUK.chunk_0618 s19
  have s17 : leavesOK ctxLitU 25900000000 3 ((leaves.drop 1234).take 166) 28325000000 3 = true :=
    take_step (n := 2) (t := 166) (b := 1236) rfl rfl ArealUCore.ArealUK.chunk_0617 s18
  have s16 : leavesOK ctxLitU 12937500000 2 ((leaves.drop 1232).take 168) 28325000000 3 = true :=
    take_step (n := 2) (t := 168) (b := 1234) rfl rfl ArealUCore.ArealUK.chunk_0616 s17
  have s15 : leavesOK ctxLitU 3225000000 0 ((leaves.drop 1230).take 170) 28325000000 3 = true :=
    take_step (n := 2) (t := 170) (b := 1232) rfl rfl ArealUCore.ArealUK.chunk_0615 s16
  have s14 : leavesOK ctxLitU 3212500000 0 ((leaves.drop 1228).take 172) 28325000000 3 = true :=
    take_step (n := 2) (t := 172) (b := 1230) rfl rfl ArealUCore.ArealUK.chunk_0614 s15
  have s13 : leavesOK ctxLitU 13142894873821 12 ((leaves.drop 1226).take 174) 28325000000 3 = true :=
    take_step (n := 2) (t := 174) (b := 1228) rfl rfl ArealUCore.ArealUK.chunk_0613 s14
  have s12 : leavesOK ctxLitU 3200000000 0 ((leaves.drop 1224).take 176) 28325000000 3 = true :=
    take_step (n := 2) (t := 176) (b := 1226) rfl rfl ArealUCore.ArealUK.chunk_0612 s13
  have s11 : leavesOK ctxLitU 3187500000 0 ((leaves.drop 1222).take 178) 28325000000 3 = true :=
    take_step (n := 2) (t := 178) (b := 1224) rfl rfl ArealUCore.ArealUK.chunk_0611 s12
  have s10 : leavesOK ctxLitU 3175000000 0 ((leaves.drop 1220).take 180) 28325000000 3 = true :=
    take_step (n := 2) (t := 180) (b := 1222) rfl rfl ArealUCore.ArealUK.chunk_0610 s11
  have s9 : leavesOK ctxLitU 3162500000 0 ((leaves.drop 1218).take 182) 28325000000 3 = true :=
    take_step (n := 2) (t := 182) (b := 1220) rfl rfl ArealUCore.ArealUK.chunk_0609 s10
  have s8 : leavesOK ctxLitU 3150000000 0 ((leaves.drop 1216).take 184) 28325000000 3 = true :=
    take_step (n := 2) (t := 184) (b := 1218) rfl rfl ArealUCore.ArealUK.chunk_0608 s9
  have s7 : leavesOK ctxLitU 3125000000 0 ((leaves.drop 1214).take 186) 28325000000 3 = true :=
    take_step (n := 2) (t := 186) (b := 1216) rfl rfl ArealUCore.ArealUK.chunk_0607 s8
  have s6 : leavesOK ctxLitU 12614800522033 12 ((leaves.drop 1212).take 188) 28325000000 3 = true :=
    take_step (n := 2) (t := 188) (b := 1214) rfl rfl ArealUCore.ArealUK.chunk_0606 s7
  have s5 : leavesOK ctxLitU 12595200000000 12 ((leaves.drop 1210).take 190) 28325000000 3 = true :=
    take_step (n := 2) (t := 190) (b := 1212) rfl rfl ArealUCore.ArealUK.chunk_0605 s6
  have s4 : leavesOK ctxLitU 3025000000 0 ((leaves.drop 1208).take 192) 28325000000 3 = true :=
    take_step (n := 2) (t := 192) (b := 1210) rfl rfl ArealUCore.ArealUK.chunk_0604 s5
  have s3 : leavesOK ctxLitU 3000000000 0 ((leaves.drop 1206).take 194) 28325000000 3 = true :=
    take_step (n := 2) (t := 194) (b := 1208) rfl rfl ArealUCore.ArealUK.chunk_0603 s4
  have s2 : leavesOK ctxLitU 2987500000 0 ((leaves.drop 1204).take 196) 28325000000 3 = true :=
    take_step (n := 2) (t := 196) (b := 1206) rfl rfl ArealUCore.ArealUK.chunk_0602 s3
  have s1 : leavesOK ctxLitU 2975000000 0 ((leaves.drop 1202).take 198) 28325000000 3 = true :=
    take_step (n := 2) (t := 198) (b := 1204) rfl rfl ArealUCore.ArealUK.chunk_0601 s2
  have s0 : leavesOK ctxLitU 2962500000 0 ((leaves.drop 1200).take 200) 28325000000 3 = true :=
    take_step (n := 2) (t := 200) (b := 1202) rfl rfl ArealUCore.ArealUK.chunk_0600 s1
  exact s0

end Areal.UCert

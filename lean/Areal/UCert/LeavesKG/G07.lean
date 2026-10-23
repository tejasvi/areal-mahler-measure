import ArealUK.Chunk0700
import ArealUK.Chunk0701
import ArealUK.Chunk0702
import ArealUK.Chunk0703
import ArealUK.Chunk0704
import ArealUK.Chunk0705
import ArealUK.Chunk0706
import ArealUK.Chunk0707
import ArealUK.Chunk0708
import ArealUK.Chunk0709
import ArealUK.Chunk0710
import ArealUK.Chunk0711
import ArealUK.Chunk0712
import ArealUK.Chunk0713
import ArealUK.Chunk0714
import ArealUK.Chunk0715
import ArealUK.Chunk0716
import ArealUK.Chunk0717
import ArealUK.Chunk0718
import ArealUK.Chunk0719
import ArealUK.Chunk0720
import ArealUK.Chunk0721
import ArealUK.Chunk0722
import ArealUK.Chunk0723
import ArealUK.Chunk0724
import ArealUK.Chunk0725
import ArealUK.Chunk0726
import ArealUK.Chunk0727
import ArealUK.Chunk0728
import ArealUK.Chunk0729
import ArealUK.Chunk0730
import ArealUK.Chunk0731
import ArealUK.Chunk0732
import ArealUK.Chunk0733
import ArealUK.Chunk0734
import ArealUK.Chunk0735
import ArealUK.Chunk0736
import ArealUK.Chunk0737
import ArealUK.Chunk0738
import ArealUK.Chunk0739
import ArealUK.Chunk0740
import ArealUK.Chunk0741
import ArealUK.Chunk0742
import ArealUK.Chunk0743
import ArealUK.Chunk0744
import ArealUK.Chunk0745
import ArealUK.Chunk0746
import ArealUK.Chunk0747
import ArealUK.Chunk0748
import ArealUK.Chunk0749
import ArealUK.Chunk0750
import ArealUK.Chunk0751
import ArealUK.Chunk0752
import ArealUK.Chunk0753
import ArealUK.Chunk0754
import ArealUK.Chunk0755
import ArealUK.Chunk0756
import ArealUK.Chunk0757
import ArealUK.Chunk0758
import ArealUK.Chunk0759
import ArealUK.Chunk0760
import ArealUK.Chunk0761
import ArealUK.Chunk0762
import ArealUK.Chunk0763
import ArealUK.Chunk0764
import ArealUK.Chunk0765
import ArealUK.Chunk0766
import ArealUK.Chunk0767
import ArealUK.Chunk0768
import ArealUK.Chunk0769
import ArealUK.Chunk0770
import ArealUK.Chunk0771
import ArealUK.Chunk0772
import ArealUK.Chunk0773
import ArealUK.Chunk0774
import ArealUK.Chunk0775
import ArealUK.Chunk0776
import ArealUK.Chunk0777
import ArealUK.Chunk0778
import ArealUK.Chunk0779
import ArealUK.Chunk0780
import ArealUK.Chunk0781
import ArealUK.Chunk0782
import ArealUK.Chunk0783
import ArealUK.Chunk0784
import ArealUK.Chunk0785
import ArealUK.Chunk0786
import ArealUK.Chunk0787
import ArealUK.Chunk0788
import ArealUK.Chunk0789
import ArealUK.Chunk0790
import ArealUK.Chunk0791
import ArealUK.Chunk0792
import ArealUK.Chunk0793
import ArealUK.Chunk0794
import ArealUK.Chunk0795
import ArealUK.Chunk0796
import ArealUK.Chunk0797
import ArealUK.Chunk0798
import ArealUK.Chunk0799
import Areal.UCert.LeavesKGen

/-! Group 7 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_07 : leavesOK ctxLitU 28325000000 3 ((leaves.drop 1400).take 200) 34187500000 3 = true := by
  have s99 := ArealUCore.ArealUK.chunk_0799
  have s98 : leavesOK ctxLitU 136681250000 5 ((leaves.drop 1596).take 4) 34187500000 3 = true :=
    take_step (n := 2) (t := 4) (b := 1598) rfl rfl ArealUCore.ArealUK.chunk_0798 s99
  have s97 : leavesOK ctxLitU 68331250000 4 ((leaves.drop 1594).take 6) 34187500000 3 = true :=
    take_step (n := 2) (t := 6) (b := 1596) rfl rfl ArealUCore.ArealUK.chunk_0797 s98
  have s96 : leavesOK ctxLitU 17075000000 2 ((leaves.drop 1592).take 8) 34187500000 3 = true :=
    take_step (n := 2) (t := 8) (b := 1594) rfl rfl ArealUCore.ArealUK.chunk_0796 s97
  have s95 : leavesOK ctxLitU 17062500000 2 ((leaves.drop 1590).take 10) 34187500000 3 = true :=
    take_step (n := 2) (t := 10) (b := 1592) rfl rfl ArealUCore.ArealUK.chunk_0795 s96
  have s94 : leavesOK ctxLitU 17050000000 2 ((leaves.drop 1588).take 12) 34187500000 3 = true :=
    take_step (n := 2) (t := 12) (b := 1590) rfl rfl ArealUCore.ArealUK.chunk_0794 s95
  have s93 : leavesOK ctxLitU 34081250000 3 ((leaves.drop 1586).take 14) 34187500000 3 = true :=
    take_step (n := 2) (t := 14) (b := 1588) rfl rfl ArealUCore.ArealUK.chunk_0793 s94
  have s92 : leavesOK ctxLitU 68150000000 4 ((leaves.drop 1584).take 16) 34187500000 3 = true :=
    take_step (n := 2) (t := 16) (b := 1586) rfl rfl ArealUCore.ArealUK.chunk_0792 s93
  have s91 : leavesOK ctxLitU 68137500000 4 ((leaves.drop 1582).take 18) 34187500000 3 = true :=
    take_step (n := 2) (t := 18) (b := 1584) rfl rfl ArealUCore.ArealUK.chunk_0791 s92
  have s90 : leavesOK ctxLitU 34056250000 3 ((leaves.drop 1580).take 20) 34187500000 3 = true :=
    take_step (n := 2) (t := 20) (b := 1582) rfl rfl ArealUCore.ArealUK.chunk_0790 s91
  have s89 : leavesOK ctxLitU 17018750000 2 ((leaves.drop 1578).take 22) 34187500000 3 = true :=
    take_step (n := 2) (t := 22) (b := 1580) rfl rfl ArealUCore.ArealUK.chunk_0789 s90
  have s88 : leavesOK ctxLitU 8500000000 1 ((leaves.drop 1576).take 24) 34187500000 3 = true :=
    take_step (n := 2) (t := 24) (b := 1578) rfl rfl ArealUCore.ArealUK.chunk_0788 s89
  have s87 : leavesOK ctxLitU 17367301232809 12 ((leaves.drop 1574).take 26) 34187500000 3 = true :=
    take_step (n := 2) (t := 26) (b := 1576) rfl rfl ArealUCore.ArealUK.chunk_0787 s88
  have s86 : leavesOK ctxLitU 8462500000 1 ((leaves.drop 1572).take 28) 34187500000 3 = true :=
    take_step (n := 2) (t := 28) (b := 1574) rfl rfl ArealUCore.ArealUK.chunk_0786 s87
  have s85 : leavesOK ctxLitU 33775000000 3 ((leaves.drop 1570).take 30) 34187500000 3 = true :=
    take_step (n := 2) (t := 30) (b := 1572) rfl rfl ArealUCore.ArealUK.chunk_0785 s86
  have s84 : leavesOK ctxLitU 33725000000 3 ((leaves.drop 1568).take 32) 34187500000 3 = true :=
    take_step (n := 2) (t := 32) (b := 1570) rfl rfl ArealUCore.ArealUK.chunk_0784 s85
  have s83 : leavesOK ctxLitU 67375000000 4 ((leaves.drop 1566).take 34) 34187500000 3 = true :=
    take_step (n := 2) (t := 34) (b := 1568) rfl rfl ArealUCore.ArealUK.chunk_0783 s84
  have s82 : leavesOK ctxLitU 134675000000 5 ((leaves.drop 1564).take 36) 34187500000 3 = true :=
    take_step (n := 2) (t := 36) (b := 1566) rfl rfl ArealUCore.ArealUK.chunk_0782 s83
  have s81 : leavesOK ctxLitU 134625000000 5 ((leaves.drop 1562).take 38) 34187500000 3 = true :=
    take_step (n := 2) (t := 38) (b := 1564) rfl rfl ArealUCore.ArealUK.chunk_0781 s82
  have s80 : leavesOK ctxLitU 67275000000 4 ((leaves.drop 1560).take 40) 34187500000 3 = true :=
    take_step (n := 2) (t := 40) (b := 1562) rfl rfl ArealUCore.ArealUK.chunk_0780 s81
  have s79 : leavesOK ctxLitU 33600000000 3 ((leaves.drop 1558).take 42) 34187500000 3 = true :=
    take_step (n := 2) (t := 42) (b := 1560) rfl rfl ArealUCore.ArealUK.chunk_0779 s80
  have s78 : leavesOK ctxLitU 33550000000 3 ((leaves.drop 1556).take 44) 34187500000 3 = true :=
    take_step (n := 2) (t := 44) (b := 1558) rfl rfl ArealUCore.ArealUK.chunk_0778 s79
  have s77 : leavesOK ctxLitU 33500000000 3 ((leaves.drop 1554).take 46) 34187500000 3 = true :=
    take_step (n := 2) (t := 46) (b := 1556) rfl rfl ArealUCore.ArealUK.chunk_0777 s78
  have s76 : leavesOK ctxLitU 33450000000 3 ((leaves.drop 1552).take 48) 34187500000 3 = true :=
    take_step (n := 2) (t := 48) (b := 1554) rfl rfl ArealUCore.ArealUK.chunk_0776 s77
  have s75 : leavesOK ctxLitU 33400000000 3 ((leaves.drop 1550).take 50) 34187500000 3 = true :=
    take_step (n := 2) (t := 50) (b := 1552) rfl rfl ArealUCore.ArealUK.chunk_0775 s76
  have s74 : leavesOK ctxLitU 33350000000 3 ((leaves.drop 1548).take 52) 34187500000 3 = true :=
    take_step (n := 2) (t := 52) (b := 1550) rfl rfl ArealUCore.ArealUK.chunk_0774 s75
  have s73 : leavesOK ctxLitU 66650000000 4 ((leaves.drop 1546).take 54) 34187500000 3 = true :=
    take_step (n := 2) (t := 54) (b := 1548) rfl rfl ArealUCore.ArealUK.chunk_0773 s74
  have s72 : leavesOK ctxLitU 133250000000 5 ((leaves.drop 1544).take 56) 34187500000 3 = true :=
    take_step (n := 2) (t := 56) (b := 1546) rfl rfl ArealUCore.ArealUK.chunk_0772 s73
  have s71 : leavesOK ctxLitU 133200000000 5 ((leaves.drop 1542).take 58) 34187500000 3 = true :=
    take_step (n := 2) (t := 58) (b := 1544) rfl rfl ArealUCore.ArealUK.chunk_0771 s72
  have s70 : leavesOK ctxLitU 66550000000 4 ((leaves.drop 1540).take 60) 34187500000 3 = true :=
    take_step (n := 2) (t := 60) (b := 1542) rfl rfl ArealUCore.ArealUK.chunk_0770 s71
  have s69 : leavesOK ctxLitU 33225000000 3 ((leaves.drop 1538).take 62) 34187500000 3 = true :=
    take_step (n := 2) (t := 62) (b := 1540) rfl rfl ArealUCore.ArealUK.chunk_0769 s70
  have s68 : leavesOK ctxLitU 16962306458910 12 ((leaves.drop 1536).take 64) 34187500000 3 = true :=
    take_step (n := 2) (t := 64) (b := 1538) rfl rfl ArealUCore.ArealUK.chunk_0768 s69
  have s67 : leavesOK ctxLitU 33858306458907 13 ((leaves.drop 1534).take 66) 34187500000 3 = true :=
    take_step (n := 2) (t := 66) (b := 1536) rfl rfl ArealUCore.ArealUK.chunk_0767 s68
  have s66 : leavesOK ctxLitU 135234306458907 15 ((leaves.drop 1532).take 68) 34187500000 3 = true :=
    take_step (n := 2) (t := 68) (b := 1534) rfl rfl ArealUCore.ArealUK.chunk_0766 s67
  have s65 : leavesOK ctxLitU 1081542919376721 18 ((leaves.drop 1530).take 70) 34187500000 3 = true :=
    take_step (n := 2) (t := 70) (b := 1532) rfl rfl ArealUCore.ArealUK.chunk_0765 s66
  have s64 : leavesOK ctxLitU 1081410306458907 18 ((leaves.drop 1528).take 72) 34187500000 3 = true :=
    take_step (n := 2) (t := 72) (b := 1530) rfl rfl ArealUCore.ArealUK.chunk_0764 s65
  have s63 : leavesOK ctxLitU 16886427626985 12 ((leaves.drop 1526).take 74) 34187500000 3 = true :=
    take_step (n := 2) (t := 74) (b := 1528) rfl rfl ArealUCore.ArealUK.chunk_0763 s64
  have s62 : leavesOK ctxLitU 67504082880946 14 ((leaves.drop 1524).take 76) 34187500000 3 = true :=
    take_step (n := 2) (t := 76) (b := 1526) rfl rfl ArealUCore.ArealUK.chunk_0762 s63
  have s61 : leavesOK ctxLitU 269891448642838 16 ((leaves.drop 1522).take 78) 34187500000 3 = true :=
    take_step (n := 2) (t := 78) (b := 1524) rfl rfl ArealUCore.ArealUK.chunk_0761 s62
  have s60 : leavesOK ctxLitU 134883282880946 15 ((leaves.drop 1520).take 80) 34187500000 3 = true :=
    take_step (n := 2) (t := 80) (b := 1522) rfl rfl ArealUCore.ArealUK.chunk_0760 s61
  have s59 : leavesOK ctxLitU 67379200000000 14 ((leaves.drop 1518).take 82) 34187500000 3 = true :=
    take_step (n := 2) (t := 82) (b := 1520) rfl rfl ArealUCore.ArealUK.chunk_0759 s60
  have s58 : leavesOK ctxLitU 16425000000 2 ((leaves.drop 1516).take 84) 34187500000 3 = true :=
    take_step (n := 2) (t := 84) (b := 1518) rfl rfl ArealUCore.ArealUK.chunk_0758 s59
  have s57 : leavesOK ctxLitU 32825000000 3 ((leaves.drop 1514).take 86) 34187500000 3 = true :=
    take_step (n := 2) (t := 86) (b := 1516) rfl rfl ArealUCore.ArealUK.chunk_0757 s58
  have s56 : leavesOK ctxLitU 65612500000 4 ((leaves.drop 1512).take 88) 34187500000 3 = true :=
    take_step (n := 2) (t := 88) (b := 1514) rfl rfl ArealUCore.ArealUK.chunk_0756 s57
  have s55 : leavesOK ctxLitU 65593750000 4 ((leaves.drop 1510).take 90) 34187500000 3 = true :=
    take_step (n := 2) (t := 90) (b := 1512) rfl rfl ArealUCore.ArealUK.chunk_0755 s56
  have s54 : leavesOK ctxLitU 32787500000 3 ((leaves.drop 1508).take 92) 34187500000 3 = true :=
    take_step (n := 2) (t := 92) (b := 1510) rfl rfl ArealUCore.ArealUK.chunk_0754 s55
  have s53 : leavesOK ctxLitU 32775000000 3 ((leaves.drop 1506).take 94) 34187500000 3 = true :=
    take_step (n := 2) (t := 94) (b := 1508) rfl rfl ArealUCore.ArealUK.chunk_0753 s54
  have s52 : leavesOK ctxLitU 16375000000 2 ((leaves.drop 1504).take 96) 34187500000 3 = true :=
    take_step (n := 2) (t := 96) (b := 1506) rfl rfl ArealUCore.ArealUK.chunk_0752 s53
  have s51 : leavesOK ctxLitU 16362500000 2 ((leaves.drop 1502).take 98) 34187500000 3 = true :=
    take_step (n := 2) (t := 98) (b := 1504) rfl rfl ArealUCore.ArealUK.chunk_0751 s52
  have s50 : leavesOK ctxLitU 16350000000 2 ((leaves.drop 1500).take 100) 34187500000 3 = true :=
    take_step (n := 2) (t := 100) (b := 1502) rfl rfl ArealUCore.ArealUK.chunk_0750 s51
  have s49 : leavesOK ctxLitU 32687500000 3 ((leaves.drop 1498).take 102) 34187500000 3 = true :=
    take_step (n := 2) (t := 102) (b := 1500) rfl rfl ArealUCore.ArealUK.chunk_0749 s50
  have s48 : leavesOK ctxLitU 32675000000 3 ((leaves.drop 1496).take 104) 34187500000 3 = true :=
    take_step (n := 2) (t := 104) (b := 1498) rfl rfl ArealUCore.ArealUK.chunk_0748 s49
  have s47 : leavesOK ctxLitU 32662500000 3 ((leaves.drop 1494).take 106) 34187500000 3 = true :=
    take_step (n := 2) (t := 106) (b := 1496) rfl rfl ArealUCore.ArealUK.chunk_0747 s48
  have s46 : leavesOK ctxLitU 16318750000 2 ((leaves.drop 1492).take 108) 34187500000 3 = true :=
    take_step (n := 2) (t := 108) (b := 1494) rfl rfl ArealUCore.ArealUK.chunk_0746 s47
  have s45 : leavesOK ctxLitU 16306250000 2 ((leaves.drop 1490).take 110) 34187500000 3 = true :=
    take_step (n := 2) (t := 110) (b := 1492) rfl rfl ArealUCore.ArealUK.chunk_0745 s46
  have s44 : leavesOK ctxLitU 32593750000 3 ((leaves.drop 1488).take 112) 34187500000 3 = true :=
    take_step (n := 2) (t := 112) (b := 1490) rfl rfl ArealUCore.ArealUK.chunk_0744 s45
  have s43 : leavesOK ctxLitU 65175000000 4 ((leaves.drop 1486).take 114) 34187500000 3 = true :=
    take_step (n := 2) (t := 114) (b := 1488) rfl rfl ArealUCore.ArealUK.chunk_0743 s44
  have s42 : leavesOK ctxLitU 65162500000 4 ((leaves.drop 1484).take 116) 34187500000 3 = true :=
    take_step (n := 2) (t := 116) (b := 1486) rfl rfl ArealUCore.ArealUK.chunk_0742 s43
  have s41 : leavesOK ctxLitU 32568750000 3 ((leaves.drop 1482).take 118) 34187500000 3 = true :=
    take_step (n := 2) (t := 118) (b := 1484) rfl rfl ArealUCore.ArealUK.chunk_0741 s42
  have s40 : leavesOK ctxLitU 32556250000 3 ((leaves.drop 1480).take 120) 34187500000 3 = true :=
    take_step (n := 2) (t := 120) (b := 1482) rfl rfl ArealUCore.ArealUK.chunk_0740 s41
  have s39 : leavesOK ctxLitU 16268750000 2 ((leaves.drop 1478).take 122) 34187500000 3 = true :=
    take_step (n := 2) (t := 122) (b := 1480) rfl rfl ArealUCore.ArealUK.chunk_0739 s40
  have s38 : leavesOK ctxLitU 8125000000 1 ((leaves.drop 1476).take 124) 34187500000 3 = true :=
    take_step (n := 2) (t := 124) (b := 1478) rfl rfl ArealUCore.ArealUK.chunk_0738 s39
  have s37 : leavesOK ctxLitU 4050000000 0 ((leaves.drop 1474).take 126) 34187500000 3 = true :=
    take_step (n := 2) (t := 126) (b := 1476) rfl rfl ArealUCore.ArealUK.chunk_0737 s38
  have s36 : leavesOK ctxLitU 4037500000 0 ((leaves.drop 1472).take 128) 34187500000 3 = true :=
    take_step (n := 2) (t := 128) (b := 1474) rfl rfl ArealUCore.ArealUK.chunk_0736 s37
  have s35 : leavesOK ctxLitU 4025000000 0 ((leaves.drop 1470).take 130) 34187500000 3 = true :=
    take_step (n := 2) (t := 130) (b := 1472) rfl rfl ArealUCore.ArealUK.chunk_0735 s36
  have s34 : leavesOK ctxLitU 4012500000 0 ((leaves.drop 1468).take 132) 34187500000 3 = true :=
    take_step (n := 2) (t := 132) (b := 1470) rfl rfl ArealUCore.ArealUK.chunk_0734 s35
  have s33 : leavesOK ctxLitU 4000000000 0 ((leaves.drop 1466).take 134) 34187500000 3 = true :=
    take_step (n := 2) (t := 134) (b := 1468) rfl rfl ArealUCore.ArealUK.chunk_0733 s34
  have s32 : leavesOK ctxLitU 3987500000 0 ((leaves.drop 1464).take 136) 34187500000 3 = true :=
    take_step (n := 2) (t := 136) (b := 1466) rfl rfl ArealUCore.ArealUK.chunk_0732 s33
  have s31 : leavesOK ctxLitU 3975000000 0 ((leaves.drop 1462).take 138) 34187500000 3 = true :=
    take_step (n := 2) (t := 138) (b := 1464) rfl rfl ArealUCore.ArealUK.chunk_0731 s32
  have s30 : leavesOK ctxLitU 3950000000 0 ((leaves.drop 1460).take 140) 34187500000 3 = true :=
    take_step (n := 2) (t := 140) (b := 1462) rfl rfl ArealUCore.ArealUK.chunk_0730 s31
  have s29 : leavesOK ctxLitU 16163563595157 12 ((leaves.drop 1458).take 142) 34187500000 3 = true :=
    take_step (n := 2) (t := 142) (b := 1460) rfl rfl ArealUCore.ArealUK.chunk_0729 s30
  have s28 : leavesOK ctxLitU 3900000000 0 ((leaves.drop 1456).take 144) 34187500000 3 = true :=
    take_step (n := 2) (t := 144) (b := 1458) rfl rfl ArealUCore.ArealUK.chunk_0728 s29
  have s27 : leavesOK ctxLitU 3850000000 0 ((leaves.drop 1454).take 146) 34187500000 3 = true :=
    take_step (n := 2) (t := 146) (b := 1456) rfl rfl ArealUCore.ArealUK.chunk_0727 s28
  have s26 : leavesOK ctxLitU 15645327820806 12 ((leaves.drop 1452).take 148) 34187500000 3 = true :=
    take_step (n := 2) (t := 148) (b := 1454) rfl rfl ArealUCore.ArealUK.chunk_0726 s27
  have s25 : leavesOK ctxLitU 15564800000000 12 ((leaves.drop 1450).take 150) 34187500000 3 = true :=
    take_step (n := 2) (t := 150) (b := 1452) rfl rfl ArealUCore.ArealUK.chunk_0725 s26
  have s24 : leavesOK ctxLitU 3750000000 0 ((leaves.drop 1448).take 152) 34187500000 3 = true :=
    take_step (n := 2) (t := 152) (b := 1450) rfl rfl ArealUCore.ArealUK.chunk_0724 s25
  have s23 : leavesOK ctxLitU 3700000000 0 ((leaves.drop 1446).take 154) 34187500000 3 = true :=
    take_step (n := 2) (t := 154) (b := 1448) rfl rfl ArealUCore.ArealUK.chunk_0723 s24
  have s22 : leavesOK ctxLitU 3662500000 0 ((leaves.drop 1444).take 156) 34187500000 3 = true :=
    take_step (n := 2) (t := 156) (b := 1446) rfl rfl ArealUCore.ArealUK.chunk_0722 s23
  have s21 : leavesOK ctxLitU 3643750000 0 ((leaves.drop 1442).take 158) 34187500000 3 = true :=
    take_step (n := 2) (t := 158) (b := 1444) rfl rfl ArealUCore.ArealUK.chunk_0721 s22
  have s20 : leavesOK ctxLitU 3631250000 0 ((leaves.drop 1440).take 160) 34187500000 3 = true :=
    take_step (n := 2) (t := 160) (b := 1442) rfl rfl ArealUCore.ArealUK.chunk_0720 s21
  have s19 : leavesOK ctxLitU 3618750000 0 ((leaves.drop 1438).take 162) 34187500000 3 = true :=
    take_step (n := 2) (t := 162) (b := 1440) rfl rfl ArealUCore.ArealUK.chunk_0719 s20
  have s18 : leavesOK ctxLitU 3606250000 0 ((leaves.drop 1436).take 164) 34187500000 3 = true :=
    take_step (n := 2) (t := 164) (b := 1438) rfl rfl ArealUCore.ArealUK.chunk_0718 s19
  have s17 : leavesOK ctxLitU 3593750000 0 ((leaves.drop 1434).take 166) 34187500000 3 = true :=
    take_step (n := 2) (t := 166) (b := 1436) rfl rfl ArealUCore.ArealUK.chunk_0717 s18
  have s16 : leavesOK ctxLitU 3581250000 0 ((leaves.drop 1432).take 168) 34187500000 3 = true :=
    take_step (n := 2) (t := 168) (b := 1434) rfl rfl ArealUCore.ArealUK.chunk_0716 s17
  have s15 : leavesOK ctxLitU 7150000000 1 ((leaves.drop 1430).take 170) 34187500000 3 = true :=
    take_step (n := 2) (t := 170) (b := 1432) rfl rfl ArealUCore.ArealUK.chunk_0715 s16
  have s14 : leavesOK ctxLitU 28575000000 3 ((leaves.drop 1428).take 172) 34187500000 3 = true :=
    take_step (n := 2) (t := 172) (b := 1430) rfl rfl ArealUCore.ArealUK.chunk_0714 s15
  have s13 : leavesOK ctxLitU 28550000000 3 ((leaves.drop 1426).take 174) 34187500000 3 = true :=
    take_step (n := 2) (t := 174) (b := 1428) rfl rfl ArealUCore.ArealUK.chunk_0713 s14
  have s12 : leavesOK ctxLitU 57062500000 4 ((leaves.drop 1424).take 176) 34187500000 3 = true :=
    take_step (n := 2) (t := 176) (b := 1426) rfl rfl ArealUCore.ArealUK.chunk_0712 s13
  have s11 : leavesOK ctxLitU 57037500000 4 ((leaves.drop 1422).take 178) 34187500000 3 = true :=
    take_step (n := 2) (t := 178) (b := 1424) rfl rfl ArealUCore.ArealUK.chunk_0711 s12
  have s10 : leavesOK ctxLitU 28500000000 3 ((leaves.drop 1420).take 180) 34187500000 3 = true :=
    take_step (n := 2) (t := 180) (b := 1422) rfl rfl ArealUCore.ArealUK.chunk_0710 s11
  have s9 : leavesOK ctxLitU 28475000000 3 ((leaves.drop 1418).take 182) 34187500000 3 = true :=
    take_step (n := 2) (t := 182) (b := 1420) rfl rfl ArealUCore.ArealUK.chunk_0709 s10
  have s8 : leavesOK ctxLitU 28450000000 3 ((leaves.drop 1416).take 184) 34187500000 3 = true :=
    take_step (n := 2) (t := 184) (b := 1418) rfl rfl ArealUCore.ArealUK.chunk_0708 s9
  have s7 : leavesOK ctxLitU 56875000000 4 ((leaves.drop 1414).take 186) 34187500000 3 = true :=
    take_step (n := 2) (t := 186) (b := 1416) rfl rfl ArealUCore.ArealUK.chunk_0707 s8
  have s6 : leavesOK ctxLitU 56850000000 4 ((leaves.drop 1412).take 188) 34187500000 3 = true :=
    take_step (n := 2) (t := 188) (b := 1414) rfl rfl ArealUCore.ArealUK.chunk_0706 s7
  have s5 : leavesOK ctxLitU 56825000000 4 ((leaves.drop 1410).take 190) 34187500000 3 = true :=
    take_step (n := 2) (t := 190) (b := 1412) rfl rfl ArealUCore.ArealUK.chunk_0705 s6
  have s4 : leavesOK ctxLitU 14193750000 2 ((leaves.drop 1408).take 192) 34187500000 3 = true :=
    take_step (n := 2) (t := 192) (b := 1410) rfl rfl ArealUCore.ArealUK.chunk_0704 s5
  have s3 : leavesOK ctxLitU 14181250000 2 ((leaves.drop 1406).take 194) 34187500000 3 = true :=
    take_step (n := 2) (t := 194) (b := 1408) rfl rfl ArealUCore.ArealUK.chunk_0703 s4
  have s2 : leavesOK ctxLitU 28350000000 3 ((leaves.drop 1404).take 196) 34187500000 3 = true :=
    take_step (n := 2) (t := 196) (b := 1406) rfl rfl ArealUCore.ArealUK.chunk_0702 s3
  have s1 : leavesOK ctxLitU 28337500000 3 ((leaves.drop 1402).take 198) 34187500000 3 = true :=
    take_step (n := 2) (t := 198) (b := 1404) rfl rfl ArealUCore.ArealUK.chunk_0701 s2
  have s0 : leavesOK ctxLitU 28325000000 3 ((leaves.drop 1400).take 200) 34187500000 3 = true :=
    take_step (n := 2) (t := 200) (b := 1402) rfl rfl ArealUCore.ArealUK.chunk_0700 s1
  exact s0

end Areal.UCert

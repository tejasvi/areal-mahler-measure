import ArealUK.Chunk13700
import ArealUK.Chunk13701
import ArealUK.Chunk13702
import ArealUK.Chunk13703
import ArealUK.Chunk13704
import ArealUK.Chunk13705
import ArealUK.Chunk13706
import ArealUK.Chunk13707
import ArealUK.Chunk13708
import ArealUK.Chunk13709
import ArealUK.Chunk13710
import ArealUK.Chunk13711
import ArealUK.Chunk13712
import ArealUK.Chunk13713
import ArealUK.Chunk13714
import ArealUK.Chunk13715
import ArealUK.Chunk13716
import ArealUK.Chunk13717
import ArealUK.Chunk13718
import ArealUK.Chunk13719
import ArealUK.Chunk13720
import ArealUK.Chunk13721
import ArealUK.Chunk13722
import ArealUK.Chunk13723
import ArealUK.Chunk13724
import ArealUK.Chunk13725
import ArealUK.Chunk13726
import ArealUK.Chunk13727
import ArealUK.Chunk13728
import ArealUK.Chunk13729
import ArealUK.Chunk13730
import ArealUK.Chunk13731
import ArealUK.Chunk13732
import ArealUK.Chunk13733
import ArealUK.Chunk13734
import ArealUK.Chunk13735
import ArealUK.Chunk13736
import ArealUK.Chunk13737
import ArealUK.Chunk13738
import ArealUK.Chunk13739
import ArealUK.Chunk13740
import ArealUK.Chunk13741
import ArealUK.Chunk13742
import ArealUK.Chunk13743
import ArealUK.Chunk13744
import ArealUK.Chunk13745
import ArealUK.Chunk13746
import ArealUK.Chunk13747
import ArealUK.Chunk13748
import ArealUK.Chunk13749
import ArealUK.Chunk13750
import ArealUK.Chunk13751
import ArealUK.Chunk13752
import ArealUK.Chunk13753
import ArealUK.Chunk13754
import ArealUK.Chunk13755
import ArealUK.Chunk13756
import ArealUK.Chunk13757
import ArealUK.Chunk13758
import ArealUK.Chunk13759
import ArealUK.Chunk13760
import ArealUK.Chunk13761
import ArealUK.Chunk13762
import ArealUK.Chunk13763
import ArealUK.Chunk13764
import ArealUK.Chunk13765
import ArealUK.Chunk13766
import ArealUK.Chunk13767
import ArealUK.Chunk13768
import ArealUK.Chunk13769
import ArealUK.Chunk13770
import ArealUK.Chunk13771
import ArealUK.Chunk13772
import ArealUK.Chunk13773
import ArealUK.Chunk13774
import ArealUK.Chunk13775
import ArealUK.Chunk13776
import ArealUK.Chunk13777
import ArealUK.Chunk13778
import ArealUK.Chunk13779
import ArealUK.Chunk13780
import ArealUK.Chunk13781
import ArealUK.Chunk13782
import ArealUK.Chunk13783
import ArealUK.Chunk13784
import ArealUK.Chunk13785
import ArealUK.Chunk13786
import ArealUK.Chunk13787
import ArealUK.Chunk13788
import ArealUK.Chunk13789
import ArealUK.Chunk13790
import ArealUK.Chunk13791
import ArealUK.Chunk13792
import ArealUK.Chunk13793
import ArealUK.Chunk13794
import ArealUK.Chunk13795
import ArealUK.Chunk13796
import ArealUK.Chunk13797
import ArealUK.Chunk13798
import ArealUK.Chunk13799
import Areal.UCert.LeavesKGen

/-! Group 137 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_137 : leavesOK ctxLitU 140325000000 0 ((leaves.drop 27400).take 200) 565925000000 2 = true := by
  have s99 := ArealUCore.ArealUK.chunk_13799
  have s98 : leavesOK ctxLitU 141456250000 0 ((leaves.drop 27596).take 4) 565925000000 2 = true :=
    take_step (n := 2) (t := 4) (b := 27598) rfl rfl ArealUCore.ArealUK.chunk_13798 s99
  have s97 : leavesOK ctxLitU 141443750000 0 ((leaves.drop 27594).take 6) 565925000000 2 = true :=
    take_step (n := 2) (t := 6) (b := 27596) rfl rfl ArealUCore.ArealUK.chunk_13797 s98
  have s96 : leavesOK ctxLitU 282868750000 1 ((leaves.drop 27592).take 8) 565925000000 2 = true :=
    take_step (n := 2) (t := 8) (b := 27594) rfl rfl ArealUCore.ArealUK.chunk_13796 s97
  have s95 : leavesOK ctxLitU 282856250000 1 ((leaves.drop 27590).take 10) 565925000000 2 = true :=
    take_step (n := 2) (t := 10) (b := 27592) rfl rfl ArealUCore.ArealUK.chunk_13795 s96
  have s94 : leavesOK ctxLitU 282837500000 1 ((leaves.drop 27588).take 12) 565925000000 2 = true :=
    take_step (n := 2) (t := 12) (b := 27590) rfl rfl ArealUCore.ArealUK.chunk_13794 s95
  have s93 : leavesOK ctxLitU 282812500000 1 ((leaves.drop 27586).take 14) 565925000000 2 = true :=
    take_step (n := 2) (t := 14) (b := 27588) rfl rfl ArealUCore.ArealUK.chunk_13793 s94
  have s92 : leavesOK ctxLitU 282787500000 1 ((leaves.drop 27584).take 16) 565925000000 2 = true :=
    take_step (n := 2) (t := 16) (b := 27586) rfl rfl ArealUCore.ArealUK.chunk_13792 s93
  have s91 : leavesOK ctxLitU 282762500000 1 ((leaves.drop 27582).take 18) 565925000000 2 = true :=
    take_step (n := 2) (t := 18) (b := 27584) rfl rfl ArealUCore.ArealUK.chunk_13791 s92
  have s90 : leavesOK ctxLitU 282743750000 1 ((leaves.drop 27580).take 20) 565925000000 2 = true :=
    take_step (n := 2) (t := 20) (b := 27582) rfl rfl ArealUCore.ArealUK.chunk_13790 s91
  have s89 : leavesOK ctxLitU 282731250000 1 ((leaves.drop 27578).take 22) 565925000000 2 = true :=
    take_step (n := 2) (t := 22) (b := 27580) rfl rfl ArealUCore.ArealUK.chunk_13789 s90
  have s88 : leavesOK ctxLitU 141356250000 0 ((leaves.drop 27576).take 24) 565925000000 2 = true :=
    take_step (n := 2) (t := 24) (b := 27578) rfl rfl ArealUCore.ArealUK.chunk_13788 s89
  have s87 : leavesOK ctxLitU 141343750000 0 ((leaves.drop 27574).take 26) 565925000000 2 = true :=
    take_step (n := 2) (t := 26) (b := 27576) rfl rfl ArealUCore.ArealUK.chunk_13787 s88
  have s86 : leavesOK ctxLitU 282668750000 1 ((leaves.drop 27572).take 28) 565925000000 2 = true :=
    take_step (n := 2) (t := 28) (b := 27574) rfl rfl ArealUCore.ArealUK.chunk_13786 s87
  have s85 : leavesOK ctxLitU 141325000000 0 ((leaves.drop 27570).take 30) 565925000000 2 = true :=
    take_step (n := 2) (t := 30) (b := 27572) rfl rfl ArealUCore.ArealUK.chunk_13785 s86
  have s84 : leavesOK ctxLitU 282625000000 1 ((leaves.drop 27568).take 32) 565925000000 2 = true :=
    take_step (n := 2) (t := 32) (b := 27570) rfl rfl ArealUCore.ArealUK.chunk_13784 s85
  have s83 : leavesOK ctxLitU 282600000000 1 ((leaves.drop 27566).take 34) 565925000000 2 = true :=
    take_step (n := 2) (t := 34) (b := 27568) rfl rfl ArealUCore.ArealUK.chunk_13783 s84
  have s82 : leavesOK ctxLitU 282575000000 1 ((leaves.drop 27564).take 36) 565925000000 2 = true :=
    take_step (n := 2) (t := 36) (b := 27566) rfl rfl ArealUCore.ArealUK.chunk_13782 s83
  have s81 : leavesOK ctxLitU 282550000000 1 ((leaves.drop 27562).take 38) 565925000000 2 = true :=
    take_step (n := 2) (t := 38) (b := 27564) rfl rfl ArealUCore.ArealUK.chunk_13781 s82
  have s80 : leavesOK ctxLitU 141262500000 0 ((leaves.drop 27560).take 40) 565925000000 2 = true :=
    take_step (n := 2) (t := 40) (b := 27562) rfl rfl ArealUCore.ArealUK.chunk_13780 s81
  have s79 : leavesOK ctxLitU 141250000000 0 ((leaves.drop 27558).take 42) 565925000000 2 = true :=
    take_step (n := 2) (t := 42) (b := 27560) rfl rfl ArealUCore.ArealUK.chunk_13779 s80
  have s78 : leavesOK ctxLitU 141237500000 0 ((leaves.drop 27556).take 44) 565925000000 2 = true :=
    take_step (n := 2) (t := 44) (b := 27558) rfl rfl ArealUCore.ArealUK.chunk_13778 s79
  have s77 : leavesOK ctxLitU 282462500000 1 ((leaves.drop 27554).take 46) 565925000000 2 = true :=
    take_step (n := 2) (t := 46) (b := 27556) rfl rfl ArealUCore.ArealUK.chunk_13777 s78
  have s76 : leavesOK ctxLitU 282450000000 1 ((leaves.drop 27552).take 48) 565925000000 2 = true :=
    take_step (n := 2) (t := 48) (b := 27554) rfl rfl ArealUCore.ArealUK.chunk_13776 s77
  have s75 : leavesOK ctxLitU 282425000000 1 ((leaves.drop 27550).take 50) 565925000000 2 = true :=
    take_step (n := 2) (t := 50) (b := 27552) rfl rfl ArealUCore.ArealUK.chunk_13775 s76
  have s74 : leavesOK ctxLitU 282400000000 1 ((leaves.drop 27548).take 52) 565925000000 2 = true :=
    take_step (n := 2) (t := 52) (b := 27550) rfl rfl ArealUCore.ArealUK.chunk_13774 s75
  have s73 : leavesOK ctxLitU 282375000000 1 ((leaves.drop 27546).take 54) 565925000000 2 = true :=
    take_step (n := 2) (t := 54) (b := 27548) rfl rfl ArealUCore.ArealUK.chunk_13773 s74
  have s72 : leavesOK ctxLitU 282350000000 1 ((leaves.drop 27544).take 56) 565925000000 2 = true :=
    take_step (n := 2) (t := 56) (b := 27546) rfl rfl ArealUCore.ArealUK.chunk_13772 s73
  have s71 : leavesOK ctxLitU 282337500000 1 ((leaves.drop 27542).take 58) 565925000000 2 = true :=
    take_step (n := 2) (t := 58) (b := 27544) rfl rfl ArealUCore.ArealUK.chunk_13771 s72
  have s70 : leavesOK ctxLitU 282325000000 1 ((leaves.drop 27540).take 60) 565925000000 2 = true :=
    take_step (n := 2) (t := 60) (b := 27542) rfl rfl ArealUCore.ArealUK.chunk_13770 s71
  have s69 : leavesOK ctxLitU 141150000000 0 ((leaves.drop 27538).take 62) 565925000000 2 = true :=
    take_step (n := 2) (t := 62) (b := 27540) rfl rfl ArealUCore.ArealUK.chunk_13769 s70
  have s68 : leavesOK ctxLitU 141137500000 0 ((leaves.drop 27536).take 64) 565925000000 2 = true :=
    take_step (n := 2) (t := 64) (b := 27538) rfl rfl ArealUCore.ArealUK.chunk_13768 s69
  have s67 : leavesOK ctxLitU 141125000000 0 ((leaves.drop 27534).take 66) 565925000000 2 = true :=
    take_step (n := 2) (t := 66) (b := 27536) rfl rfl ArealUCore.ArealUK.chunk_13767 s68
  have s66 : leavesOK ctxLitU 282225000000 1 ((leaves.drop 27532).take 68) 565925000000 2 = true :=
    take_step (n := 2) (t := 68) (b := 27534) rfl rfl ArealUCore.ArealUK.chunk_13766 s67
  have s65 : leavesOK ctxLitU 282200000000 1 ((leaves.drop 27530).take 70) 565925000000 2 = true :=
    take_step (n := 2) (t := 70) (b := 27532) rfl rfl ArealUCore.ArealUK.chunk_13765 s66
  have s64 : leavesOK ctxLitU 282175000000 1 ((leaves.drop 27528).take 72) 565925000000 2 = true :=
    take_step (n := 2) (t := 72) (b := 27530) rfl rfl ArealUCore.ArealUK.chunk_13764 s65
  have s63 : leavesOK ctxLitU 282150000000 1 ((leaves.drop 27526).take 74) 565925000000 2 = true :=
    take_step (n := 2) (t := 74) (b := 27528) rfl rfl ArealUCore.ArealUK.chunk_13763 s64
  have s62 : leavesOK ctxLitU 141062500000 0 ((leaves.drop 27524).take 76) 565925000000 2 = true :=
    take_step (n := 2) (t := 76) (b := 27526) rfl rfl ArealUCore.ArealUK.chunk_13762 s63
  have s61 : leavesOK ctxLitU 141050000000 0 ((leaves.drop 27522).take 78) 565925000000 2 = true :=
    take_step (n := 2) (t := 78) (b := 27524) rfl rfl ArealUCore.ArealUK.chunk_13761 s62
  have s60 : leavesOK ctxLitU 141037500000 0 ((leaves.drop 27520).take 80) 565925000000 2 = true :=
    take_step (n := 2) (t := 80) (b := 27522) rfl rfl ArealUCore.ArealUK.chunk_13760 s61
  have s59 : leavesOK ctxLitU 141025000000 0 ((leaves.drop 27518).take 82) 565925000000 2 = true :=
    take_step (n := 2) (t := 82) (b := 27520) rfl rfl ArealUCore.ArealUK.chunk_13759 s60
  have s58 : leavesOK ctxLitU 282025000000 1 ((leaves.drop 27516).take 84) 565925000000 2 = true :=
    take_step (n := 2) (t := 84) (b := 27518) rfl rfl ArealUCore.ArealUK.chunk_13758 s59
  have s57 : leavesOK ctxLitU 282000000000 1 ((leaves.drop 27514).take 86) 565925000000 2 = true :=
    take_step (n := 2) (t := 86) (b := 27516) rfl rfl ArealUCore.ArealUK.chunk_13757 s58
  have s56 : leavesOK ctxLitU 281975000000 1 ((leaves.drop 27512).take 88) 565925000000 2 = true :=
    take_step (n := 2) (t := 88) (b := 27514) rfl rfl ArealUCore.ArealUK.chunk_13756 s57
  have s55 : leavesOK ctxLitU 281950000000 1 ((leaves.drop 27510).take 90) 565925000000 2 = true :=
    take_step (n := 2) (t := 90) (b := 27512) rfl rfl ArealUCore.ArealUK.chunk_13755 s56
  have s54 : leavesOK ctxLitU 140962500000 0 ((leaves.drop 27508).take 92) 565925000000 2 = true :=
    take_step (n := 2) (t := 92) (b := 27510) rfl rfl ArealUCore.ArealUK.chunk_13754 s55
  have s53 : leavesOK ctxLitU 140950000000 0 ((leaves.drop 27506).take 94) 565925000000 2 = true :=
    take_step (n := 2) (t := 94) (b := 27508) rfl rfl ArealUCore.ArealUK.chunk_13753 s54
  have s52 : leavesOK ctxLitU 140937500000 0 ((leaves.drop 27504).take 96) 565925000000 2 = true :=
    take_step (n := 2) (t := 96) (b := 27506) rfl rfl ArealUCore.ArealUK.chunk_13752 s53
  have s51 : leavesOK ctxLitU 140925000000 0 ((leaves.drop 27502).take 98) 565925000000 2 = true :=
    take_step (n := 2) (t := 98) (b := 27504) rfl rfl ArealUCore.ArealUK.chunk_13751 s52
  have s50 : leavesOK ctxLitU 281825000000 1 ((leaves.drop 27500).take 100) 565925000000 2 = true :=
    take_step (n := 2) (t := 100) (b := 27502) rfl rfl ArealUCore.ArealUK.chunk_13750 s51
  have s49 : leavesOK ctxLitU 563625000000 2 ((leaves.drop 27498).take 102) 565925000000 2 = true :=
    take_step (n := 2) (t := 102) (b := 27500) rfl rfl ArealUCore.ArealUK.chunk_13749 s50
  have s48 : leavesOK ctxLitU 281787500000 1 ((leaves.drop 27496).take 104) 565925000000 2 = true :=
    take_step (n := 2) (t := 104) (b := 27498) rfl rfl ArealUCore.ArealUK.chunk_13748 s49
  have s47 : leavesOK ctxLitU 281762500000 1 ((leaves.drop 27494).take 106) 565925000000 2 = true :=
    take_step (n := 2) (t := 106) (b := 27496) rfl rfl ArealUCore.ArealUK.chunk_13747 s48
  have s46 : leavesOK ctxLitU 140868750000 0 ((leaves.drop 27492).take 108) 565925000000 2 = true :=
    take_step (n := 2) (t := 108) (b := 27494) rfl rfl ArealUCore.ArealUK.chunk_13746 s47
  have s45 : leavesOK ctxLitU 140856250000 0 ((leaves.drop 27490).take 110) 565925000000 2 = true :=
    take_step (n := 2) (t := 110) (b := 27492) rfl rfl ArealUCore.ArealUK.chunk_13745 s46
  have s44 : leavesOK ctxLitU 140843750000 0 ((leaves.drop 27488).take 112) 565925000000 2 = true :=
    take_step (n := 2) (t := 112) (b := 27490) rfl rfl ArealUCore.ArealUK.chunk_13744 s45
  have s43 : leavesOK ctxLitU 281668750000 1 ((leaves.drop 27486).take 114) 565925000000 2 = true :=
    take_step (n := 2) (t := 114) (b := 27488) rfl rfl ArealUCore.ArealUK.chunk_13743 s44
  have s42 : leavesOK ctxLitU 281656250000 1 ((leaves.drop 27484).take 116) 565925000000 2 = true :=
    take_step (n := 2) (t := 116) (b := 27486) rfl rfl ArealUCore.ArealUK.chunk_13742 s43
  have s41 : leavesOK ctxLitU 281637500000 1 ((leaves.drop 27482).take 118) 565925000000 2 = true :=
    take_step (n := 2) (t := 118) (b := 27484) rfl rfl ArealUCore.ArealUK.chunk_13741 s42
  have s40 : leavesOK ctxLitU 281612500000 1 ((leaves.drop 27480).take 120) 565925000000 2 = true :=
    take_step (n := 2) (t := 120) (b := 27482) rfl rfl ArealUCore.ArealUK.chunk_13740 s41
  have s39 : leavesOK ctxLitU 281587500000 1 ((leaves.drop 27478).take 122) 565925000000 2 = true :=
    take_step (n := 2) (t := 122) (b := 27480) rfl rfl ArealUCore.ArealUK.chunk_13739 s40
  have s38 : leavesOK ctxLitU 281562500000 1 ((leaves.drop 27476).take 124) 565925000000 2 = true :=
    take_step (n := 2) (t := 124) (b := 27478) rfl rfl ArealUCore.ArealUK.chunk_13738 s39
  have s37 : leavesOK ctxLitU 281543750000 1 ((leaves.drop 27474).take 126) 565925000000 2 = true :=
    take_step (n := 2) (t := 126) (b := 27476) rfl rfl ArealUCore.ArealUK.chunk_13737 s38
  have s36 : leavesOK ctxLitU 140762500000 0 ((leaves.drop 27472).take 128) 565925000000 2 = true :=
    take_step (n := 2) (t := 128) (b := 27474) rfl rfl ArealUCore.ArealUK.chunk_13736 s37
  have s35 : leavesOK ctxLitU 140750000000 0 ((leaves.drop 27470).take 130) 565925000000 2 = true :=
    take_step (n := 2) (t := 130) (b := 27472) rfl rfl ArealUCore.ArealUK.chunk_13735 s36
  have s34 : leavesOK ctxLitU 281475000000 1 ((leaves.drop 27468).take 132) 565925000000 2 = true :=
    take_step (n := 2) (t := 132) (b := 27470) rfl rfl ArealUCore.ArealUK.chunk_13734 s35
  have s33 : leavesOK ctxLitU 281450000000 1 ((leaves.drop 27466).take 134) 565925000000 2 = true :=
    take_step (n := 2) (t := 134) (b := 27468) rfl rfl ArealUCore.ArealUK.chunk_13733 s34
  have s32 : leavesOK ctxLitU 562850000000 2 ((leaves.drop 27464).take 136) 565925000000 2 = true :=
    take_step (n := 2) (t := 136) (b := 27466) rfl rfl ArealUCore.ArealUK.chunk_13732 s33
  have s31 : leavesOK ctxLitU 562800000000 2 ((leaves.drop 27462).take 138) 565925000000 2 = true :=
    take_step (n := 2) (t := 138) (b := 27464) rfl rfl ArealUCore.ArealUK.chunk_13731 s32
  have s30 : leavesOK ctxLitU 562750000000 2 ((leaves.drop 27460).take 140) 565925000000 2 = true :=
    take_step (n := 2) (t := 140) (b := 27462) rfl rfl ArealUCore.ArealUK.chunk_13730 s31
  have s29 : leavesOK ctxLitU 562700000000 2 ((leaves.drop 27458).take 142) 565925000000 2 = true :=
    take_step (n := 2) (t := 142) (b := 27460) rfl rfl ArealUCore.ArealUK.chunk_13729 s30
  have s28 : leavesOK ctxLitU 562650000000 2 ((leaves.drop 27456).take 144) 565925000000 2 = true :=
    take_step (n := 2) (t := 144) (b := 27458) rfl rfl ArealUCore.ArealUK.chunk_13728 s29
  have s27 : leavesOK ctxLitU 562600000000 2 ((leaves.drop 27454).take 146) 565925000000 2 = true :=
    take_step (n := 2) (t := 146) (b := 27456) rfl rfl ArealUCore.ArealUK.chunk_13727 s28
  have s26 : leavesOK ctxLitU 562550000000 2 ((leaves.drop 27452).take 148) 565925000000 2 = true :=
    take_step (n := 2) (t := 148) (b := 27454) rfl rfl ArealUCore.ArealUK.chunk_13726 s27
  have s25 : leavesOK ctxLitU 562500000000 2 ((leaves.drop 27450).take 150) 565925000000 2 = true :=
    take_step (n := 2) (t := 150) (b := 27452) rfl rfl ArealUCore.ArealUK.chunk_13725 s26
  have s24 : leavesOK ctxLitU 562450000000 2 ((leaves.drop 27448).take 152) 565925000000 2 = true :=
    take_step (n := 2) (t := 152) (b := 27450) rfl rfl ArealUCore.ArealUK.chunk_13724 s25
  have s23 : leavesOK ctxLitU 562400000000 2 ((leaves.drop 27446).take 154) 565925000000 2 = true :=
    take_step (n := 2) (t := 154) (b := 27448) rfl rfl ArealUCore.ArealUK.chunk_13723 s24
  have s22 : leavesOK ctxLitU 281175000000 1 ((leaves.drop 27444).take 156) 565925000000 2 = true :=
    take_step (n := 2) (t := 156) (b := 27446) rfl rfl ArealUCore.ArealUK.chunk_13722 s23
  have s21 : leavesOK ctxLitU 281150000000 1 ((leaves.drop 27442).take 158) 565925000000 2 = true :=
    take_step (n := 2) (t := 158) (b := 27444) rfl rfl ArealUCore.ArealUK.chunk_13721 s22
  have s20 : leavesOK ctxLitU 140562500000 0 ((leaves.drop 27440).take 160) 565925000000 2 = true :=
    take_step (n := 2) (t := 160) (b := 27442) rfl rfl ArealUCore.ArealUK.chunk_13720 s21
  have s19 : leavesOK ctxLitU 140550000000 0 ((leaves.drop 27438).take 162) 565925000000 2 = true :=
    take_step (n := 2) (t := 162) (b := 27440) rfl rfl ArealUCore.ArealUK.chunk_13719 s20
  have s18 : leavesOK ctxLitU 140537500000 0 ((leaves.drop 27436).take 164) 565925000000 2 = true :=
    take_step (n := 2) (t := 164) (b := 27438) rfl rfl ArealUCore.ArealUK.chunk_13718 s19
  have s17 : leavesOK ctxLitU 140525000000 0 ((leaves.drop 27434).take 166) 565925000000 2 = true :=
    take_step (n := 2) (t := 166) (b := 27436) rfl rfl ArealUCore.ArealUK.chunk_13717 s18
  have s16 : leavesOK ctxLitU 281025000000 1 ((leaves.drop 27432).take 168) 565925000000 2 = true :=
    take_step (n := 2) (t := 168) (b := 27434) rfl rfl ArealUCore.ArealUK.chunk_13716 s17
  have s15 : leavesOK ctxLitU 281000000000 1 ((leaves.drop 27430).take 170) 565925000000 2 = true :=
    take_step (n := 2) (t := 170) (b := 27432) rfl rfl ArealUCore.ArealUK.chunk_13715 s16
  have s14 : leavesOK ctxLitU 280975000000 1 ((leaves.drop 27428).take 172) 565925000000 2 = true :=
    take_step (n := 2) (t := 172) (b := 27430) rfl rfl ArealUCore.ArealUK.chunk_13714 s15
  have s13 : leavesOK ctxLitU 280950000000 1 ((leaves.drop 27426).take 174) 565925000000 2 = true :=
    take_step (n := 2) (t := 174) (b := 27428) rfl rfl ArealUCore.ArealUK.chunk_13713 s14
  have s12 : leavesOK ctxLitU 140462500000 0 ((leaves.drop 27424).take 176) 565925000000 2 = true :=
    take_step (n := 2) (t := 176) (b := 27426) rfl rfl ArealUCore.ArealUK.chunk_13712 s13
  have s11 : leavesOK ctxLitU 140450000000 0 ((leaves.drop 27422).take 178) 565925000000 2 = true :=
    take_step (n := 2) (t := 178) (b := 27424) rfl rfl ArealUCore.ArealUK.chunk_13711 s12
  have s10 : leavesOK ctxLitU 140437500000 0 ((leaves.drop 27420).take 180) 565925000000 2 = true :=
    take_step (n := 2) (t := 180) (b := 27422) rfl rfl ArealUCore.ArealUK.chunk_13710 s11
  have s9 : leavesOK ctxLitU 140425000000 0 ((leaves.drop 27418).take 182) 565925000000 2 = true :=
    take_step (n := 2) (t := 182) (b := 27420) rfl rfl ArealUCore.ArealUK.chunk_13709 s10
  have s8 : leavesOK ctxLitU 280825000000 1 ((leaves.drop 27416).take 184) 565925000000 2 = true :=
    take_step (n := 2) (t := 184) (b := 27418) rfl rfl ArealUCore.ArealUK.chunk_13708 s9
  have s7 : leavesOK ctxLitU 280800000000 1 ((leaves.drop 27414).take 186) 565925000000 2 = true :=
    take_step (n := 2) (t := 186) (b := 27416) rfl rfl ArealUCore.ArealUK.chunk_13707 s8
  have s6 : leavesOK ctxLitU 280775000000 1 ((leaves.drop 27412).take 188) 565925000000 2 = true :=
    take_step (n := 2) (t := 188) (b := 27414) rfl rfl ArealUCore.ArealUK.chunk_13706 s7
  have s5 : leavesOK ctxLitU 280750000000 1 ((leaves.drop 27410).take 190) 565925000000 2 = true :=
    take_step (n := 2) (t := 190) (b := 27412) rfl rfl ArealUCore.ArealUK.chunk_13705 s6
  have s4 : leavesOK ctxLitU 280737500000 1 ((leaves.drop 27408).take 192) 565925000000 2 = true :=
    take_step (n := 2) (t := 192) (b := 27410) rfl rfl ArealUCore.ArealUK.chunk_13704 s5
  have s3 : leavesOK ctxLitU 280725000000 1 ((leaves.drop 27406).take 194) 565925000000 2 = true :=
    take_step (n := 2) (t := 194) (b := 27408) rfl rfl ArealUCore.ArealUK.chunk_13703 s4
  have s2 : leavesOK ctxLitU 140350000000 0 ((leaves.drop 27404).take 196) 565925000000 2 = true :=
    take_step (n := 2) (t := 196) (b := 27406) rfl rfl ArealUCore.ArealUK.chunk_13702 s3
  have s1 : leavesOK ctxLitU 140337500000 0 ((leaves.drop 27402).take 198) 565925000000 2 = true :=
    take_step (n := 2) (t := 198) (b := 27404) rfl rfl ArealUCore.ArealUK.chunk_13701 s2
  have s0 : leavesOK ctxLitU 140325000000 0 ((leaves.drop 27400).take 200) 565925000000 2 = true :=
    take_step (n := 2) (t := 200) (b := 27402) rfl rfl ArealUCore.ArealUK.chunk_13700 s1
  exact s0

end Areal.UCert

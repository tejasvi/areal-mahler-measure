import ArealUK.Chunk14700
import ArealUK.Chunk14701
import ArealUK.Chunk14702
import ArealUK.Chunk14703
import ArealUK.Chunk14704
import ArealUK.Chunk14705
import ArealUK.Chunk14706
import ArealUK.Chunk14707
import ArealUK.Chunk14708
import ArealUK.Chunk14709
import ArealUK.Chunk14710
import ArealUK.Chunk14711
import ArealUK.Chunk14712
import ArealUK.Chunk14713
import ArealUK.Chunk14714
import ArealUK.Chunk14715
import ArealUK.Chunk14716
import ArealUK.Chunk14717
import ArealUK.Chunk14718
import ArealUK.Chunk14719
import ArealUK.Chunk14720
import ArealUK.Chunk14721
import ArealUK.Chunk14722
import ArealUK.Chunk14723
import ArealUK.Chunk14724
import ArealUK.Chunk14725
import ArealUK.Chunk14726
import ArealUK.Chunk14727
import ArealUK.Chunk14728
import ArealUK.Chunk14729
import ArealUK.Chunk14730
import ArealUK.Chunk14731
import ArealUK.Chunk14732
import ArealUK.Chunk14733
import ArealUK.Chunk14734
import ArealUK.Chunk14735
import ArealUK.Chunk14736
import ArealUK.Chunk14737
import ArealUK.Chunk14738
import ArealUK.Chunk14739
import ArealUK.Chunk14740
import ArealUK.Chunk14741
import ArealUK.Chunk14742
import ArealUK.Chunk14743
import ArealUK.Chunk14744
import ArealUK.Chunk14745
import ArealUK.Chunk14746
import ArealUK.Chunk14747
import ArealUK.Chunk14748
import ArealUK.Chunk14749
import ArealUK.Chunk14750
import ArealUK.Chunk14751
import ArealUK.Chunk14752
import ArealUK.Chunk14753
import ArealUK.Chunk14754
import ArealUK.Chunk14755
import ArealUK.Chunk14756
import ArealUK.Chunk14757
import ArealUK.Chunk14758
import ArealUK.Chunk14759
import ArealUK.Chunk14760
import ArealUK.Chunk14761
import ArealUK.Chunk14762
import ArealUK.Chunk14763
import ArealUK.Chunk14764
import ArealUK.Chunk14765
import ArealUK.Chunk14766
import ArealUK.Chunk14767
import ArealUK.Chunk14768
import ArealUK.Chunk14769
import ArealUK.Chunk14770
import ArealUK.Chunk14771
import ArealUK.Chunk14772
import ArealUK.Chunk14773
import ArealUK.Chunk14774
import ArealUK.Chunk14775
import ArealUK.Chunk14776
import ArealUK.Chunk14777
import ArealUK.Chunk14778
import ArealUK.Chunk14779
import ArealUK.Chunk14780
import ArealUK.Chunk14781
import ArealUK.Chunk14782
import ArealUK.Chunk14783
import ArealUK.Chunk14784
import ArealUK.Chunk14785
import ArealUK.Chunk14786
import ArealUK.Chunk14787
import ArealUK.Chunk14788
import ArealUK.Chunk14789
import ArealUK.Chunk14790
import ArealUK.Chunk14791
import ArealUK.Chunk14792
import ArealUK.Chunk14793
import ArealUK.Chunk14794
import ArealUK.Chunk14795
import ArealUK.Chunk14796
import ArealUK.Chunk14797
import ArealUK.Chunk14798
import ArealUK.Chunk14799
import Areal.UCert.LeavesKGen

/-! Group 147 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_147 : leavesOK ctxLitU 152356250000 0 ((leaves.drop 29400).take 200) 307362500000 1 = true := by
  have s99 := ArealUCore.ArealUK.chunk_14799
  have s98 : leavesOK ctxLitU 153656250000 0 ((leaves.drop 29596).take 4) 307362500000 1 = true :=
    take_step (n := 2) (t := 4) (b := 29598) rfl rfl ArealUCore.ArealUK.chunk_14798 s99
  have s97 : leavesOK ctxLitU 153643750000 0 ((leaves.drop 29594).take 6) 307362500000 1 = true :=
    take_step (n := 2) (t := 6) (b := 29596) rfl rfl ArealUCore.ArealUK.chunk_14797 s98
  have s96 : leavesOK ctxLitU 153631250000 0 ((leaves.drop 29592).take 8) 307362500000 1 = true :=
    take_step (n := 2) (t := 8) (b := 29594) rfl rfl ArealUCore.ArealUK.chunk_14796 s97
  have s95 : leavesOK ctxLitU 153618750000 0 ((leaves.drop 29590).take 10) 307362500000 1 = true :=
    take_step (n := 2) (t := 10) (b := 29592) rfl rfl ArealUCore.ArealUK.chunk_14795 s96
  have s94 : leavesOK ctxLitU 153606250000 0 ((leaves.drop 29588).take 12) 307362500000 1 = true :=
    take_step (n := 2) (t := 12) (b := 29590) rfl rfl ArealUCore.ArealUK.chunk_14794 s95
  have s93 : leavesOK ctxLitU 153593750000 0 ((leaves.drop 29586).take 14) 307362500000 1 = true :=
    take_step (n := 2) (t := 14) (b := 29588) rfl rfl ArealUCore.ArealUK.chunk_14793 s94
  have s92 : leavesOK ctxLitU 153581250000 0 ((leaves.drop 29584).take 16) 307362500000 1 = true :=
    take_step (n := 2) (t := 16) (b := 29586) rfl rfl ArealUCore.ArealUK.chunk_14792 s93
  have s91 : leavesOK ctxLitU 153568750000 0 ((leaves.drop 29582).take 18) 307362500000 1 = true :=
    take_step (n := 2) (t := 18) (b := 29584) rfl rfl ArealUCore.ArealUK.chunk_14791 s92
  have s90 : leavesOK ctxLitU 153556250000 0 ((leaves.drop 29580).take 20) 307362500000 1 = true :=
    take_step (n := 2) (t := 20) (b := 29582) rfl rfl ArealUCore.ArealUK.chunk_14790 s91
  have s89 : leavesOK ctxLitU 153543750000 0 ((leaves.drop 29578).take 22) 307362500000 1 = true :=
    take_step (n := 2) (t := 22) (b := 29580) rfl rfl ArealUCore.ArealUK.chunk_14789 s90
  have s88 : leavesOK ctxLitU 153531250000 0 ((leaves.drop 29576).take 24) 307362500000 1 = true :=
    take_step (n := 2) (t := 24) (b := 29578) rfl rfl ArealUCore.ArealUK.chunk_14788 s89
  have s87 : leavesOK ctxLitU 307037500000 1 ((leaves.drop 29574).take 26) 307362500000 1 = true :=
    take_step (n := 2) (t := 26) (b := 29576) rfl rfl ArealUCore.ArealUK.chunk_14787 s88
  have s86 : leavesOK ctxLitU 307012500000 1 ((leaves.drop 29572).take 28) 307362500000 1 = true :=
    take_step (n := 2) (t := 28) (b := 29574) rfl rfl ArealUCore.ArealUK.chunk_14786 s87
  have s85 : leavesOK ctxLitU 306987500000 1 ((leaves.drop 29570).take 30) 307362500000 1 = true :=
    take_step (n := 2) (t := 30) (b := 29572) rfl rfl ArealUCore.ArealUK.chunk_14785 s86
  have s84 : leavesOK ctxLitU 306962500000 1 ((leaves.drop 29568).take 32) 307362500000 1 = true :=
    take_step (n := 2) (t := 32) (b := 29570) rfl rfl ArealUCore.ArealUK.chunk_14784 s85
  have s83 : leavesOK ctxLitU 153468750000 0 ((leaves.drop 29566).take 34) 307362500000 1 = true :=
    take_step (n := 2) (t := 34) (b := 29568) rfl rfl ArealUCore.ArealUK.chunk_14783 s84
  have s82 : leavesOK ctxLitU 153456250000 0 ((leaves.drop 29564).take 36) 307362500000 1 = true :=
    take_step (n := 2) (t := 36) (b := 29566) rfl rfl ArealUCore.ArealUK.chunk_14782 s83
  have s81 : leavesOK ctxLitU 153443750000 0 ((leaves.drop 29562).take 38) 307362500000 1 = true :=
    take_step (n := 2) (t := 38) (b := 29564) rfl rfl ArealUCore.ArealUK.chunk_14781 s82
  have s80 : leavesOK ctxLitU 153431250000 0 ((leaves.drop 29560).take 40) 307362500000 1 = true :=
    take_step (n := 2) (t := 40) (b := 29562) rfl rfl ArealUCore.ArealUK.chunk_14780 s81
  have s79 : leavesOK ctxLitU 306837500000 1 ((leaves.drop 29558).take 42) 307362500000 1 = true :=
    take_step (n := 2) (t := 42) (b := 29560) rfl rfl ArealUCore.ArealUK.chunk_14779 s80
  have s78 : leavesOK ctxLitU 153400000000 0 ((leaves.drop 29556).take 44) 307362500000 1 = true :=
    take_step (n := 2) (t := 44) (b := 29558) rfl rfl ArealUCore.ArealUK.chunk_14778 s79
  have s77 : leavesOK ctxLitU 306762500000 1 ((leaves.drop 29554).take 46) 307362500000 1 = true :=
    take_step (n := 2) (t := 46) (b := 29556) rfl rfl ArealUCore.ArealUK.chunk_14777 s78
  have s76 : leavesOK ctxLitU 153368750000 0 ((leaves.drop 29552).take 48) 307362500000 1 = true :=
    take_step (n := 2) (t := 48) (b := 29554) rfl rfl ArealUCore.ArealUK.chunk_14776 s77
  have s75 : leavesOK ctxLitU 153356250000 0 ((leaves.drop 29550).take 50) 307362500000 1 = true :=
    take_step (n := 2) (t := 50) (b := 29552) rfl rfl ArealUCore.ArealUK.chunk_14775 s76
  have s74 : leavesOK ctxLitU 153343750000 0 ((leaves.drop 29548).take 52) 307362500000 1 = true :=
    take_step (n := 2) (t := 52) (b := 29550) rfl rfl ArealUCore.ArealUK.chunk_14774 s75
  have s73 : leavesOK ctxLitU 153331250000 0 ((leaves.drop 29546).take 54) 307362500000 1 = true :=
    take_step (n := 2) (t := 54) (b := 29548) rfl rfl ArealUCore.ArealUK.chunk_14773 s74
  have s72 : leavesOK ctxLitU 306637500000 1 ((leaves.drop 29544).take 56) 307362500000 1 = true :=
    take_step (n := 2) (t := 56) (b := 29546) rfl rfl ArealUCore.ArealUK.chunk_14772 s73
  have s71 : leavesOK ctxLitU 306612500000 1 ((leaves.drop 29542).take 58) 307362500000 1 = true :=
    take_step (n := 2) (t := 58) (b := 29544) rfl rfl ArealUCore.ArealUK.chunk_14771 s72
  have s70 : leavesOK ctxLitU 306587500000 1 ((leaves.drop 29540).take 60) 307362500000 1 = true :=
    take_step (n := 2) (t := 60) (b := 29542) rfl rfl ArealUCore.ArealUK.chunk_14770 s71
  have s69 : leavesOK ctxLitU 306562500000 1 ((leaves.drop 29538).take 62) 307362500000 1 = true :=
    take_step (n := 2) (t := 62) (b := 29540) rfl rfl ArealUCore.ArealUK.chunk_14769 s70
  have s68 : leavesOK ctxLitU 153268750000 0 ((leaves.drop 29536).take 64) 307362500000 1 = true :=
    take_step (n := 2) (t := 64) (b := 29538) rfl rfl ArealUCore.ArealUK.chunk_14768 s69
  have s67 : leavesOK ctxLitU 153256250000 0 ((leaves.drop 29534).take 66) 307362500000 1 = true :=
    take_step (n := 2) (t := 66) (b := 29536) rfl rfl ArealUCore.ArealUK.chunk_14767 s68
  have s66 : leavesOK ctxLitU 153243750000 0 ((leaves.drop 29532).take 68) 307362500000 1 = true :=
    take_step (n := 2) (t := 68) (b := 29534) rfl rfl ArealUCore.ArealUK.chunk_14766 s67
  have s65 : leavesOK ctxLitU 153231250000 0 ((leaves.drop 29530).take 70) 307362500000 1 = true :=
    take_step (n := 2) (t := 70) (b := 29532) rfl rfl ArealUCore.ArealUK.chunk_14765 s66
  have s64 : leavesOK ctxLitU 306437500000 1 ((leaves.drop 29528).take 72) 307362500000 1 = true :=
    take_step (n := 2) (t := 72) (b := 29530) rfl rfl ArealUCore.ArealUK.chunk_14764 s65
  have s63 : leavesOK ctxLitU 153200000000 0 ((leaves.drop 29526).take 74) 307362500000 1 = true :=
    take_step (n := 2) (t := 74) (b := 29528) rfl rfl ArealUCore.ArealUK.chunk_14763 s64
  have s62 : leavesOK ctxLitU 306375000000 1 ((leaves.drop 29524).take 76) 307362500000 1 = true :=
    take_step (n := 2) (t := 76) (b := 29526) rfl rfl ArealUCore.ArealUK.chunk_14762 s63
  have s61 : leavesOK ctxLitU 306350000000 1 ((leaves.drop 29522).take 78) 307362500000 1 = true :=
    take_step (n := 2) (t := 78) (b := 29524) rfl rfl ArealUCore.ArealUK.chunk_14761 s62
  have s60 : leavesOK ctxLitU 153162500000 0 ((leaves.drop 29520).take 80) 307362500000 1 = true :=
    take_step (n := 2) (t := 80) (b := 29522) rfl rfl ArealUCore.ArealUK.chunk_14760 s61
  have s59 : leavesOK ctxLitU 153150000000 0 ((leaves.drop 29518).take 82) 307362500000 1 = true :=
    take_step (n := 2) (t := 82) (b := 29520) rfl rfl ArealUCore.ArealUK.chunk_14759 s60
  have s58 : leavesOK ctxLitU 153137500000 0 ((leaves.drop 29516).take 84) 307362500000 1 = true :=
    take_step (n := 2) (t := 84) (b := 29518) rfl rfl ArealUCore.ArealUK.chunk_14758 s59
  have s57 : leavesOK ctxLitU 153125000000 0 ((leaves.drop 29514).take 86) 307362500000 1 = true :=
    take_step (n := 2) (t := 86) (b := 29516) rfl rfl ArealUCore.ArealUK.chunk_14757 s58
  have s56 : leavesOK ctxLitU 306225000000 1 ((leaves.drop 29512).take 88) 307362500000 1 = true :=
    take_step (n := 2) (t := 88) (b := 29514) rfl rfl ArealUCore.ArealUK.chunk_14756 s57
  have s55 : leavesOK ctxLitU 306200000000 1 ((leaves.drop 29510).take 90) 307362500000 1 = true :=
    take_step (n := 2) (t := 90) (b := 29512) rfl rfl ArealUCore.ArealUK.chunk_14755 s56
  have s54 : leavesOK ctxLitU 306175000000 1 ((leaves.drop 29508).take 92) 307362500000 1 = true :=
    take_step (n := 2) (t := 92) (b := 29510) rfl rfl ArealUCore.ArealUK.chunk_14754 s55
  have s53 : leavesOK ctxLitU 306150000000 1 ((leaves.drop 29506).take 94) 307362500000 1 = true :=
    take_step (n := 2) (t := 94) (b := 29508) rfl rfl ArealUCore.ArealUK.chunk_14753 s54
  have s52 : leavesOK ctxLitU 153062500000 0 ((leaves.drop 29504).take 96) 307362500000 1 = true :=
    take_step (n := 2) (t := 96) (b := 29506) rfl rfl ArealUCore.ArealUK.chunk_14752 s53
  have s51 : leavesOK ctxLitU 153050000000 0 ((leaves.drop 29502).take 98) 307362500000 1 = true :=
    take_step (n := 2) (t := 98) (b := 29504) rfl rfl ArealUCore.ArealUK.chunk_14751 s52
  have s50 : leavesOK ctxLitU 153037500000 0 ((leaves.drop 29500).take 100) 307362500000 1 = true :=
    take_step (n := 2) (t := 100) (b := 29502) rfl rfl ArealUCore.ArealUK.chunk_14750 s51
  have s49 : leavesOK ctxLitU 153025000000 0 ((leaves.drop 29498).take 102) 307362500000 1 = true :=
    take_step (n := 2) (t := 102) (b := 29500) rfl rfl ArealUCore.ArealUK.chunk_14749 s50
  have s48 : leavesOK ctxLitU 306025000000 1 ((leaves.drop 29496).take 104) 307362500000 1 = true :=
    take_step (n := 2) (t := 104) (b := 29498) rfl rfl ArealUCore.ArealUK.chunk_14748 s49
  have s47 : leavesOK ctxLitU 306000000000 1 ((leaves.drop 29494).take 106) 307362500000 1 = true :=
    take_step (n := 2) (t := 106) (b := 29496) rfl rfl ArealUCore.ArealUK.chunk_14747 s48
  have s46 : leavesOK ctxLitU 152975000000 0 ((leaves.drop 29492).take 108) 307362500000 1 = true :=
    take_step (n := 2) (t := 108) (b := 29494) rfl rfl ArealUCore.ArealUK.chunk_14746 s47
  have s45 : leavesOK ctxLitU 152962500000 0 ((leaves.drop 29490).take 110) 307362500000 1 = true :=
    take_step (n := 2) (t := 110) (b := 29492) rfl rfl ArealUCore.ArealUK.chunk_14745 s46
  have s44 : leavesOK ctxLitU 152950000000 0 ((leaves.drop 29488).take 112) 307362500000 1 = true :=
    take_step (n := 2) (t := 112) (b := 29490) rfl rfl ArealUCore.ArealUK.chunk_14744 s45
  have s43 : leavesOK ctxLitU 152937500000 0 ((leaves.drop 29486).take 114) 307362500000 1 = true :=
    take_step (n := 2) (t := 114) (b := 29488) rfl rfl ArealUCore.ArealUK.chunk_14743 s44
  have s42 : leavesOK ctxLitU 152925000000 0 ((leaves.drop 29484).take 116) 307362500000 1 = true :=
    take_step (n := 2) (t := 116) (b := 29486) rfl rfl ArealUCore.ArealUK.chunk_14742 s43
  have s41 : leavesOK ctxLitU 305825000000 1 ((leaves.drop 29482).take 118) 307362500000 1 = true :=
    take_step (n := 2) (t := 118) (b := 29484) rfl rfl ArealUCore.ArealUK.chunk_14741 s42
  have s40 : leavesOK ctxLitU 611625000000 2 ((leaves.drop 29480).take 120) 307362500000 1 = true :=
    take_step (n := 2) (t := 120) (b := 29482) rfl rfl ArealUCore.ArealUK.chunk_14740 s41
  have s39 : leavesOK ctxLitU 305787500000 1 ((leaves.drop 29478).take 122) 307362500000 1 = true :=
    take_step (n := 2) (t := 122) (b := 29480) rfl rfl ArealUCore.ArealUK.chunk_14739 s40
  have s38 : leavesOK ctxLitU 152875000000 0 ((leaves.drop 29476).take 124) 307362500000 1 = true :=
    take_step (n := 2) (t := 124) (b := 29478) rfl rfl ArealUCore.ArealUK.chunk_14738 s39
  have s37 : leavesOK ctxLitU 152862500000 0 ((leaves.drop 29474).take 126) 307362500000 1 = true :=
    take_step (n := 2) (t := 126) (b := 29476) rfl rfl ArealUCore.ArealUK.chunk_14737 s38
  have s36 : leavesOK ctxLitU 152850000000 0 ((leaves.drop 29472).take 128) 307362500000 1 = true :=
    take_step (n := 2) (t := 128) (b := 29474) rfl rfl ArealUCore.ArealUK.chunk_14736 s37
  have s35 : leavesOK ctxLitU 152837500000 0 ((leaves.drop 29470).take 130) 307362500000 1 = true :=
    take_step (n := 2) (t := 130) (b := 29472) rfl rfl ArealUCore.ArealUK.chunk_14735 s36
  have s34 : leavesOK ctxLitU 152825000000 0 ((leaves.drop 29468).take 132) 307362500000 1 = true :=
    take_step (n := 2) (t := 132) (b := 29470) rfl rfl ArealUCore.ArealUK.chunk_14734 s35
  have s33 : leavesOK ctxLitU 305625000000 1 ((leaves.drop 29466).take 134) 307362500000 1 = true :=
    take_step (n := 2) (t := 134) (b := 29468) rfl rfl ArealUCore.ArealUK.chunk_14733 s34
  have s32 : leavesOK ctxLitU 305587500000 1 ((leaves.drop 29464).take 136) 307362500000 1 = true :=
    take_step (n := 2) (t := 136) (b := 29466) rfl rfl ArealUCore.ArealUK.chunk_14732 s33
  have s31 : leavesOK ctxLitU 305562500000 1 ((leaves.drop 29462).take 138) 307362500000 1 = true :=
    take_step (n := 2) (t := 138) (b := 29464) rfl rfl ArealUCore.ArealUK.chunk_14731 s32
  have s30 : leavesOK ctxLitU 152768750000 0 ((leaves.drop 29460).take 140) 307362500000 1 = true :=
    take_step (n := 2) (t := 140) (b := 29462) rfl rfl ArealUCore.ArealUK.chunk_14730 s31
  have s29 : leavesOK ctxLitU 152756250000 0 ((leaves.drop 29458).take 142) 307362500000 1 = true :=
    take_step (n := 2) (t := 142) (b := 29460) rfl rfl ArealUCore.ArealUK.chunk_14729 s30
  have s28 : leavesOK ctxLitU 152743750000 0 ((leaves.drop 29456).take 144) 307362500000 1 = true :=
    take_step (n := 2) (t := 144) (b := 29458) rfl rfl ArealUCore.ArealUK.chunk_14728 s29
  have s27 : leavesOK ctxLitU 152731250000 0 ((leaves.drop 29454).take 146) 307362500000 1 = true :=
    take_step (n := 2) (t := 146) (b := 29456) rfl rfl ArealUCore.ArealUK.chunk_14727 s28
  have s26 : leavesOK ctxLitU 305437500000 1 ((leaves.drop 29452).take 148) 307362500000 1 = true :=
    take_step (n := 2) (t := 148) (b := 29454) rfl rfl ArealUCore.ArealUK.chunk_14726 s27
  have s25 : leavesOK ctxLitU 305412500000 1 ((leaves.drop 29450).take 150) 307362500000 1 = true :=
    take_step (n := 2) (t := 150) (b := 29452) rfl rfl ArealUCore.ArealUK.chunk_14725 s26
  have s24 : leavesOK ctxLitU 305387500000 1 ((leaves.drop 29448).take 152) 307362500000 1 = true :=
    take_step (n := 2) (t := 152) (b := 29450) rfl rfl ArealUCore.ArealUK.chunk_14724 s25
  have s23 : leavesOK ctxLitU 305362500000 1 ((leaves.drop 29446).take 154) 307362500000 1 = true :=
    take_step (n := 2) (t := 154) (b := 29448) rfl rfl ArealUCore.ArealUK.chunk_14723 s24
  have s22 : leavesOK ctxLitU 152668750000 0 ((leaves.drop 29444).take 156) 307362500000 1 = true :=
    take_step (n := 2) (t := 156) (b := 29446) rfl rfl ArealUCore.ArealUK.chunk_14722 s23
  have s21 : leavesOK ctxLitU 152656250000 0 ((leaves.drop 29442).take 158) 307362500000 1 = true :=
    take_step (n := 2) (t := 158) (b := 29444) rfl rfl ArealUCore.ArealUK.chunk_14721 s22
  have s20 : leavesOK ctxLitU 152643750000 0 ((leaves.drop 29440).take 160) 307362500000 1 = true :=
    take_step (n := 2) (t := 160) (b := 29442) rfl rfl ArealUCore.ArealUK.chunk_14720 s21
  have s19 : leavesOK ctxLitU 152631250000 0 ((leaves.drop 29438).take 162) 307362500000 1 = true :=
    take_step (n := 2) (t := 162) (b := 29440) rfl rfl ArealUCore.ArealUK.chunk_14719 s20
  have s18 : leavesOK ctxLitU 305237500000 1 ((leaves.drop 29436).take 164) 307362500000 1 = true :=
    take_step (n := 2) (t := 164) (b := 29438) rfl rfl ArealUCore.ArealUK.chunk_14718 s19
  have s17 : leavesOK ctxLitU 305212500000 1 ((leaves.drop 29434).take 166) 307362500000 1 = true :=
    take_step (n := 2) (t := 166) (b := 29436) rfl rfl ArealUCore.ArealUK.chunk_14717 s18
  have s16 : leavesOK ctxLitU 152587500000 0 ((leaves.drop 29432).take 168) 307362500000 1 = true :=
    take_step (n := 2) (t := 168) (b := 29434) rfl rfl ArealUCore.ArealUK.chunk_14716 s17
  have s15 : leavesOK ctxLitU 152568750000 0 ((leaves.drop 29430).take 170) 307362500000 1 = true :=
    take_step (n := 2) (t := 170) (b := 29432) rfl rfl ArealUCore.ArealUK.chunk_14715 s16
  have s14 : leavesOK ctxLitU 152556250000 0 ((leaves.drop 29428).take 172) 307362500000 1 = true :=
    take_step (n := 2) (t := 172) (b := 29430) rfl rfl ArealUCore.ArealUK.chunk_14714 s15
  have s13 : leavesOK ctxLitU 152543750000 0 ((leaves.drop 29426).take 174) 307362500000 1 = true :=
    take_step (n := 2) (t := 174) (b := 29428) rfl rfl ArealUCore.ArealUK.chunk_14713 s14
  have s12 : leavesOK ctxLitU 152531250000 0 ((leaves.drop 29424).take 176) 307362500000 1 = true :=
    take_step (n := 2) (t := 176) (b := 29426) rfl rfl ArealUCore.ArealUK.chunk_14712 s13
  have s11 : leavesOK ctxLitU 305037500000 1 ((leaves.drop 29422).take 178) 307362500000 1 = true :=
    take_step (n := 2) (t := 178) (b := 29424) rfl rfl ArealUCore.ArealUK.chunk_14711 s12
  have s10 : leavesOK ctxLitU 305012500000 1 ((leaves.drop 29420).take 180) 307362500000 1 = true :=
    take_step (n := 2) (t := 180) (b := 29422) rfl rfl ArealUCore.ArealUK.chunk_14710 s11
  have s9 : leavesOK ctxLitU 304987500000 1 ((leaves.drop 29418).take 182) 307362500000 1 = true :=
    take_step (n := 2) (t := 182) (b := 29420) rfl rfl ArealUCore.ArealUK.chunk_14709 s10
  have s8 : leavesOK ctxLitU 152475000000 0 ((leaves.drop 29416).take 184) 307362500000 1 = true :=
    take_step (n := 2) (t := 184) (b := 29418) rfl rfl ArealUCore.ArealUK.chunk_14708 s9
  have s7 : leavesOK ctxLitU 152462500000 0 ((leaves.drop 29414).take 186) 307362500000 1 = true :=
    take_step (n := 2) (t := 186) (b := 29416) rfl rfl ArealUCore.ArealUK.chunk_14707 s8
  have s6 : leavesOK ctxLitU 152450000000 0 ((leaves.drop 29412).take 188) 307362500000 1 = true :=
    take_step (n := 2) (t := 188) (b := 29414) rfl rfl ArealUCore.ArealUK.chunk_14706 s7
  have s5 : leavesOK ctxLitU 152437500000 0 ((leaves.drop 29410).take 190) 307362500000 1 = true :=
    take_step (n := 2) (t := 190) (b := 29412) rfl rfl ArealUCore.ArealUK.chunk_14705 s6
  have s4 : leavesOK ctxLitU 152425000000 0 ((leaves.drop 29408).take 192) 307362500000 1 = true :=
    take_step (n := 2) (t := 192) (b := 29410) rfl rfl ArealUCore.ArealUK.chunk_14704 s5
  have s3 : leavesOK ctxLitU 152400000000 0 ((leaves.drop 29406).take 194) 307362500000 1 = true :=
    take_step (n := 2) (t := 194) (b := 29408) rfl rfl ArealUCore.ArealUK.chunk_14703 s4
  have s2 : leavesOK ctxLitU 304775000000 1 ((leaves.drop 29404).take 196) 307362500000 1 = true :=
    take_step (n := 2) (t := 196) (b := 29406) rfl rfl ArealUCore.ArealUK.chunk_14702 s3
  have s1 : leavesOK ctxLitU 152368750000 0 ((leaves.drop 29402).take 198) 307362500000 1 = true :=
    take_step (n := 2) (t := 198) (b := 29404) rfl rfl ArealUCore.ArealUK.chunk_14701 s2
  have s0 : leavesOK ctxLitU 152356250000 0 ((leaves.drop 29400).take 200) 307362500000 1 = true :=
    take_step (n := 2) (t := 200) (b := 29402) rfl rfl ArealUCore.ArealUK.chunk_14700 s1
  exact s0

end Areal.UCert

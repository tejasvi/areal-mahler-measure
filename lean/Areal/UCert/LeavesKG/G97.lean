import ArealUK.Chunk9700
import ArealUK.Chunk9701
import ArealUK.Chunk9702
import ArealUK.Chunk9703
import ArealUK.Chunk9704
import ArealUK.Chunk9705
import ArealUK.Chunk9706
import ArealUK.Chunk9707
import ArealUK.Chunk9708
import ArealUK.Chunk9709
import ArealUK.Chunk9710
import ArealUK.Chunk9711
import ArealUK.Chunk9712
import ArealUK.Chunk9713
import ArealUK.Chunk9714
import ArealUK.Chunk9715
import ArealUK.Chunk9716
import ArealUK.Chunk9717
import ArealUK.Chunk9718
import ArealUK.Chunk9719
import ArealUK.Chunk9720
import ArealUK.Chunk9721
import ArealUK.Chunk9722
import ArealUK.Chunk9723
import ArealUK.Chunk9724
import ArealUK.Chunk9725
import ArealUK.Chunk9726
import ArealUK.Chunk9727
import ArealUK.Chunk9728
import ArealUK.Chunk9729
import ArealUK.Chunk9730
import ArealUK.Chunk9731
import ArealUK.Chunk9732
import ArealUK.Chunk9733
import ArealUK.Chunk9734
import ArealUK.Chunk9735
import ArealUK.Chunk9736
import ArealUK.Chunk9737
import ArealUK.Chunk9738
import ArealUK.Chunk9739
import ArealUK.Chunk9740
import ArealUK.Chunk9741
import ArealUK.Chunk9742
import ArealUK.Chunk9743
import ArealUK.Chunk9744
import ArealUK.Chunk9745
import ArealUK.Chunk9746
import ArealUK.Chunk9747
import ArealUK.Chunk9748
import ArealUK.Chunk9749
import ArealUK.Chunk9750
import ArealUK.Chunk9751
import ArealUK.Chunk9752
import ArealUK.Chunk9753
import ArealUK.Chunk9754
import ArealUK.Chunk9755
import ArealUK.Chunk9756
import ArealUK.Chunk9757
import ArealUK.Chunk9758
import ArealUK.Chunk9759
import ArealUK.Chunk9760
import ArealUK.Chunk9761
import ArealUK.Chunk9762
import ArealUK.Chunk9763
import ArealUK.Chunk9764
import ArealUK.Chunk9765
import ArealUK.Chunk9766
import ArealUK.Chunk9767
import ArealUK.Chunk9768
import ArealUK.Chunk9769
import ArealUK.Chunk9770
import ArealUK.Chunk9771
import ArealUK.Chunk9772
import ArealUK.Chunk9773
import ArealUK.Chunk9774
import ArealUK.Chunk9775
import ArealUK.Chunk9776
import ArealUK.Chunk9777
import ArealUK.Chunk9778
import ArealUK.Chunk9779
import ArealUK.Chunk9780
import ArealUK.Chunk9781
import ArealUK.Chunk9782
import ArealUK.Chunk9783
import ArealUK.Chunk9784
import ArealUK.Chunk9785
import ArealUK.Chunk9786
import ArealUK.Chunk9787
import ArealUK.Chunk9788
import ArealUK.Chunk9789
import ArealUK.Chunk9790
import ArealUK.Chunk9791
import ArealUK.Chunk9792
import ArealUK.Chunk9793
import ArealUK.Chunk9794
import ArealUK.Chunk9795
import ArealUK.Chunk9796
import ArealUK.Chunk9797
import ArealUK.Chunk9798
import ArealUK.Chunk9799
import Areal.UCert.LeavesKGen

/-! Group 97 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_97 : leavesOK ctxLitU 84850000000 0 ((leaves.drop 19400).take 200) 345100000000 2 = true := by
  have s99 := ArealUCore.ArealUK.chunk_9799
  have s98 : leavesOK ctxLitU 345000000000 2 ((leaves.drop 19596).take 4) 345100000000 2 = true :=
    take_step (n := 2) (t := 4) (b := 19598) rfl rfl ArealUCore.ArealUK.chunk_9798 s99
  have s97 : leavesOK ctxLitU 344950000000 2 ((leaves.drop 19594).take 6) 345100000000 2 = true :=
    take_step (n := 2) (t := 6) (b := 19596) rfl rfl ArealUCore.ArealUK.chunk_9797 s98
  have s96 : leavesOK ctxLitU 344900000000 2 ((leaves.drop 19592).take 8) 345100000000 2 = true :=
    take_step (n := 2) (t := 8) (b := 19594) rfl rfl ArealUCore.ArealUK.chunk_9796 s97
  have s95 : leavesOK ctxLitU 344850000000 2 ((leaves.drop 19590).take 10) 345100000000 2 = true :=
    take_step (n := 2) (t := 10) (b := 19592) rfl rfl ArealUCore.ArealUK.chunk_9795 s96
  have s94 : leavesOK ctxLitU 344800000000 2 ((leaves.drop 19588).take 12) 345100000000 2 = true :=
    take_step (n := 2) (t := 12) (b := 19590) rfl rfl ArealUCore.ArealUK.chunk_9794 s95
  have s93 : leavesOK ctxLitU 344750000000 2 ((leaves.drop 19586).take 14) 345100000000 2 = true :=
    take_step (n := 2) (t := 14) (b := 19588) rfl rfl ArealUCore.ArealUK.chunk_9793 s94
  have s92 : leavesOK ctxLitU 344700000000 2 ((leaves.drop 19584).take 16) 345100000000 2 = true :=
    take_step (n := 2) (t := 16) (b := 19586) rfl rfl ArealUCore.ArealUK.chunk_9792 s93
  have s91 : leavesOK ctxLitU 344650000000 2 ((leaves.drop 19582).take 18) 345100000000 2 = true :=
    take_step (n := 2) (t := 18) (b := 19584) rfl rfl ArealUCore.ArealUK.chunk_9791 s92
  have s90 : leavesOK ctxLitU 344600000000 2 ((leaves.drop 19580).take 20) 345100000000 2 = true :=
    take_step (n := 2) (t := 20) (b := 19582) rfl rfl ArealUCore.ArealUK.chunk_9790 s91
  have s89 : leavesOK ctxLitU 344550000000 2 ((leaves.drop 19578).take 22) 345100000000 2 = true :=
    take_step (n := 2) (t := 22) (b := 19580) rfl rfl ArealUCore.ArealUK.chunk_9789 s90
  have s88 : leavesOK ctxLitU 344500000000 2 ((leaves.drop 19576).take 24) 345100000000 2 = true :=
    take_step (n := 2) (t := 24) (b := 19578) rfl rfl ArealUCore.ArealUK.chunk_9788 s89
  have s87 : leavesOK ctxLitU 344450000000 2 ((leaves.drop 19574).take 26) 345100000000 2 = true :=
    take_step (n := 2) (t := 26) (b := 19576) rfl rfl ArealUCore.ArealUK.chunk_9787 s88
  have s86 : leavesOK ctxLitU 344400000000 2 ((leaves.drop 19572).take 28) 345100000000 2 = true :=
    take_step (n := 2) (t := 28) (b := 19574) rfl rfl ArealUCore.ArealUK.chunk_9786 s87
  have s85 : leavesOK ctxLitU 344350000000 2 ((leaves.drop 19570).take 30) 345100000000 2 = true :=
    take_step (n := 2) (t := 30) (b := 19572) rfl rfl ArealUCore.ArealUK.chunk_9785 s86
  have s84 : leavesOK ctxLitU 344300000000 2 ((leaves.drop 19568).take 32) 345100000000 2 = true :=
    take_step (n := 2) (t := 32) (b := 19570) rfl rfl ArealUCore.ArealUK.chunk_9784 s85
  have s83 : leavesOK ctxLitU 344250000000 2 ((leaves.drop 19566).take 34) 345100000000 2 = true :=
    take_step (n := 2) (t := 34) (b := 19568) rfl rfl ArealUCore.ArealUK.chunk_9783 s84
  have s82 : leavesOK ctxLitU 344200000000 2 ((leaves.drop 19564).take 36) 345100000000 2 = true :=
    take_step (n := 2) (t := 36) (b := 19566) rfl rfl ArealUCore.ArealUK.chunk_9782 s83
  have s81 : leavesOK ctxLitU 344150000000 2 ((leaves.drop 19562).take 38) 345100000000 2 = true :=
    take_step (n := 2) (t := 38) (b := 19564) rfl rfl ArealUCore.ArealUK.chunk_9781 s82
  have s80 : leavesOK ctxLitU 344100000000 2 ((leaves.drop 19560).take 40) 345100000000 2 = true :=
    take_step (n := 2) (t := 40) (b := 19562) rfl rfl ArealUCore.ArealUK.chunk_9780 s81
  have s79 : leavesOK ctxLitU 344050000000 2 ((leaves.drop 19558).take 42) 345100000000 2 = true :=
    take_step (n := 2) (t := 42) (b := 19560) rfl rfl ArealUCore.ArealUK.chunk_9779 s80
  have s78 : leavesOK ctxLitU 344000000000 2 ((leaves.drop 19556).take 44) 345100000000 2 = true :=
    take_step (n := 2) (t := 44) (b := 19558) rfl rfl ArealUCore.ArealUK.chunk_9778 s79
  have s77 : leavesOK ctxLitU 343950000000 2 ((leaves.drop 19554).take 46) 345100000000 2 = true :=
    take_step (n := 2) (t := 46) (b := 19556) rfl rfl ArealUCore.ArealUK.chunk_9777 s78
  have s76 : leavesOK ctxLitU 343900000000 2 ((leaves.drop 19552).take 48) 345100000000 2 = true :=
    take_step (n := 2) (t := 48) (b := 19554) rfl rfl ArealUCore.ArealUK.chunk_9776 s77
  have s75 : leavesOK ctxLitU 343850000000 2 ((leaves.drop 19550).take 50) 345100000000 2 = true :=
    take_step (n := 2) (t := 50) (b := 19552) rfl rfl ArealUCore.ArealUK.chunk_9775 s76
  have s74 : leavesOK ctxLitU 343800000000 2 ((leaves.drop 19548).take 52) 345100000000 2 = true :=
    take_step (n := 2) (t := 52) (b := 19550) rfl rfl ArealUCore.ArealUK.chunk_9774 s75
  have s73 : leavesOK ctxLitU 343750000000 2 ((leaves.drop 19546).take 54) 345100000000 2 = true :=
    take_step (n := 2) (t := 54) (b := 19548) rfl rfl ArealUCore.ArealUK.chunk_9773 s74
  have s72 : leavesOK ctxLitU 343700000000 2 ((leaves.drop 19544).take 56) 345100000000 2 = true :=
    take_step (n := 2) (t := 56) (b := 19546) rfl rfl ArealUCore.ArealUK.chunk_9772 s73
  have s71 : leavesOK ctxLitU 343650000000 2 ((leaves.drop 19542).take 58) 345100000000 2 = true :=
    take_step (n := 2) (t := 58) (b := 19544) rfl rfl ArealUCore.ArealUK.chunk_9771 s72
  have s70 : leavesOK ctxLitU 343600000000 2 ((leaves.drop 19540).take 60) 345100000000 2 = true :=
    take_step (n := 2) (t := 60) (b := 19542) rfl rfl ArealUCore.ArealUK.chunk_9770 s71
  have s69 : leavesOK ctxLitU 343550000000 2 ((leaves.drop 19538).take 62) 345100000000 2 = true :=
    take_step (n := 2) (t := 62) (b := 19540) rfl rfl ArealUCore.ArealUK.chunk_9769 s70
  have s68 : leavesOK ctxLitU 343500000000 2 ((leaves.drop 19536).take 64) 345100000000 2 = true :=
    take_step (n := 2) (t := 64) (b := 19538) rfl rfl ArealUCore.ArealUK.chunk_9768 s69
  have s67 : leavesOK ctxLitU 343450000000 2 ((leaves.drop 19534).take 66) 345100000000 2 = true :=
    take_step (n := 2) (t := 66) (b := 19536) rfl rfl ArealUCore.ArealUK.chunk_9767 s68
  have s66 : leavesOK ctxLitU 343400000000 2 ((leaves.drop 19532).take 68) 345100000000 2 = true :=
    take_step (n := 2) (t := 68) (b := 19534) rfl rfl ArealUCore.ArealUK.chunk_9766 s67
  have s65 : leavesOK ctxLitU 343350000000 2 ((leaves.drop 19530).take 70) 345100000000 2 = true :=
    take_step (n := 2) (t := 70) (b := 19532) rfl rfl ArealUCore.ArealUK.chunk_9765 s66
  have s64 : leavesOK ctxLitU 343300000000 2 ((leaves.drop 19528).take 72) 345100000000 2 = true :=
    take_step (n := 2) (t := 72) (b := 19530) rfl rfl ArealUCore.ArealUK.chunk_9764 s65
  have s63 : leavesOK ctxLitU 343250000000 2 ((leaves.drop 19526).take 74) 345100000000 2 = true :=
    take_step (n := 2) (t := 74) (b := 19528) rfl rfl ArealUCore.ArealUK.chunk_9763 s64
  have s62 : leavesOK ctxLitU 343200000000 2 ((leaves.drop 19524).take 76) 345100000000 2 = true :=
    take_step (n := 2) (t := 76) (b := 19526) rfl rfl ArealUCore.ArealUK.chunk_9762 s63
  have s61 : leavesOK ctxLitU 343150000000 2 ((leaves.drop 19522).take 78) 345100000000 2 = true :=
    take_step (n := 2) (t := 78) (b := 19524) rfl rfl ArealUCore.ArealUK.chunk_9761 s62
  have s60 : leavesOK ctxLitU 343100000000 2 ((leaves.drop 19520).take 80) 345100000000 2 = true :=
    take_step (n := 2) (t := 80) (b := 19522) rfl rfl ArealUCore.ArealUK.chunk_9760 s61
  have s59 : leavesOK ctxLitU 343050000000 2 ((leaves.drop 19518).take 82) 345100000000 2 = true :=
    take_step (n := 2) (t := 82) (b := 19520) rfl rfl ArealUCore.ArealUK.chunk_9759 s60
  have s58 : leavesOK ctxLitU 343000000000 2 ((leaves.drop 19516).take 84) 345100000000 2 = true :=
    take_step (n := 2) (t := 84) (b := 19518) rfl rfl ArealUCore.ArealUK.chunk_9758 s59
  have s57 : leavesOK ctxLitU 342950000000 2 ((leaves.drop 19514).take 86) 345100000000 2 = true :=
    take_step (n := 2) (t := 86) (b := 19516) rfl rfl ArealUCore.ArealUK.chunk_9757 s58
  have s56 : leavesOK ctxLitU 342900000000 2 ((leaves.drop 19512).take 88) 345100000000 2 = true :=
    take_step (n := 2) (t := 88) (b := 19514) rfl rfl ArealUCore.ArealUK.chunk_9756 s57
  have s55 : leavesOK ctxLitU 342850000000 2 ((leaves.drop 19510).take 90) 345100000000 2 = true :=
    take_step (n := 2) (t := 90) (b := 19512) rfl rfl ArealUCore.ArealUK.chunk_9755 s56
  have s54 : leavesOK ctxLitU 342800000000 2 ((leaves.drop 19508).take 92) 345100000000 2 = true :=
    take_step (n := 2) (t := 92) (b := 19510) rfl rfl ArealUCore.ArealUK.chunk_9754 s55
  have s53 : leavesOK ctxLitU 342750000000 2 ((leaves.drop 19506).take 94) 345100000000 2 = true :=
    take_step (n := 2) (t := 94) (b := 19508) rfl rfl ArealUCore.ArealUK.chunk_9753 s54
  have s52 : leavesOK ctxLitU 342700000000 2 ((leaves.drop 19504).take 96) 345100000000 2 = true :=
    take_step (n := 2) (t := 96) (b := 19506) rfl rfl ArealUCore.ArealUK.chunk_9752 s53
  have s51 : leavesOK ctxLitU 342650000000 2 ((leaves.drop 19502).take 98) 345100000000 2 = true :=
    take_step (n := 2) (t := 98) (b := 19504) rfl rfl ArealUCore.ArealUK.chunk_9751 s52
  have s50 : leavesOK ctxLitU 342600000000 2 ((leaves.drop 19500).take 100) 345100000000 2 = true :=
    take_step (n := 2) (t := 100) (b := 19502) rfl rfl ArealUCore.ArealUK.chunk_9750 s51
  have s49 : leavesOK ctxLitU 342550000000 2 ((leaves.drop 19498).take 102) 345100000000 2 = true :=
    take_step (n := 2) (t := 102) (b := 19500) rfl rfl ArealUCore.ArealUK.chunk_9749 s50
  have s48 : leavesOK ctxLitU 342500000000 2 ((leaves.drop 19496).take 104) 345100000000 2 = true :=
    take_step (n := 2) (t := 104) (b := 19498) rfl rfl ArealUCore.ArealUK.chunk_9748 s49
  have s47 : leavesOK ctxLitU 342450000000 2 ((leaves.drop 19494).take 106) 345100000000 2 = true :=
    take_step (n := 2) (t := 106) (b := 19496) rfl rfl ArealUCore.ArealUK.chunk_9747 s48
  have s46 : leavesOK ctxLitU 342400000000 2 ((leaves.drop 19492).take 108) 345100000000 2 = true :=
    take_step (n := 2) (t := 108) (b := 19494) rfl rfl ArealUCore.ArealUK.chunk_9746 s47
  have s45 : leavesOK ctxLitU 342350000000 2 ((leaves.drop 19490).take 110) 345100000000 2 = true :=
    take_step (n := 2) (t := 110) (b := 19492) rfl rfl ArealUCore.ArealUK.chunk_9745 s46
  have s44 : leavesOK ctxLitU 684625000000 3 ((leaves.drop 19488).take 112) 345100000000 2 = true :=
    take_step (n := 2) (t := 112) (b := 19490) rfl rfl ArealUCore.ArealUK.chunk_9744 s45
  have s43 : leavesOK ctxLitU 342275000000 2 ((leaves.drop 19486).take 114) 345100000000 2 = true :=
    take_step (n := 2) (t := 114) (b := 19488) rfl rfl ArealUCore.ArealUK.chunk_9743 s44
  have s42 : leavesOK ctxLitU 342225000000 2 ((leaves.drop 19484).take 116) 345100000000 2 = true :=
    take_step (n := 2) (t := 116) (b := 19486) rfl rfl ArealUCore.ArealUK.chunk_9742 s43
  have s41 : leavesOK ctxLitU 342175000000 2 ((leaves.drop 19482).take 118) 345100000000 2 = true :=
    take_step (n := 2) (t := 118) (b := 19484) rfl rfl ArealUCore.ArealUK.chunk_9741 s42
  have s40 : leavesOK ctxLitU 342125000000 2 ((leaves.drop 19480).take 120) 345100000000 2 = true :=
    take_step (n := 2) (t := 120) (b := 19482) rfl rfl ArealUCore.ArealUK.chunk_9740 s41
  have s39 : leavesOK ctxLitU 342075000000 2 ((leaves.drop 19478).take 122) 345100000000 2 = true :=
    take_step (n := 2) (t := 122) (b := 19480) rfl rfl ArealUCore.ArealUK.chunk_9739 s40
  have s38 : leavesOK ctxLitU 342025000000 2 ((leaves.drop 19476).take 124) 345100000000 2 = true :=
    take_step (n := 2) (t := 124) (b := 19478) rfl rfl ArealUCore.ArealUK.chunk_9738 s39
  have s37 : leavesOK ctxLitU 341975000000 2 ((leaves.drop 19474).take 126) 345100000000 2 = true :=
    take_step (n := 2) (t := 126) (b := 19476) rfl rfl ArealUCore.ArealUK.chunk_9737 s38
  have s36 : leavesOK ctxLitU 341925000000 2 ((leaves.drop 19472).take 128) 345100000000 2 = true :=
    take_step (n := 2) (t := 128) (b := 19474) rfl rfl ArealUCore.ArealUK.chunk_9736 s37
  have s35 : leavesOK ctxLitU 341875000000 2 ((leaves.drop 19470).take 130) 345100000000 2 = true :=
    take_step (n := 2) (t := 130) (b := 19472) rfl rfl ArealUCore.ArealUK.chunk_9735 s36
  have s34 : leavesOK ctxLitU 341825000000 2 ((leaves.drop 19468).take 132) 345100000000 2 = true :=
    take_step (n := 2) (t := 132) (b := 19470) rfl rfl ArealUCore.ArealUK.chunk_9734 s35
  have s33 : leavesOK ctxLitU 341775000000 2 ((leaves.drop 19466).take 134) 345100000000 2 = true :=
    take_step (n := 2) (t := 134) (b := 19468) rfl rfl ArealUCore.ArealUK.chunk_9733 s34
  have s32 : leavesOK ctxLitU 341725000000 2 ((leaves.drop 19464).take 136) 345100000000 2 = true :=
    take_step (n := 2) (t := 136) (b := 19466) rfl rfl ArealUCore.ArealUK.chunk_9732 s33
  have s31 : leavesOK ctxLitU 341675000000 2 ((leaves.drop 19462).take 138) 345100000000 2 = true :=
    take_step (n := 2) (t := 138) (b := 19464) rfl rfl ArealUCore.ArealUK.chunk_9731 s32
  have s30 : leavesOK ctxLitU 341625000000 2 ((leaves.drop 19460).take 140) 345100000000 2 = true :=
    take_step (n := 2) (t := 140) (b := 19462) rfl rfl ArealUCore.ArealUK.chunk_9730 s31
  have s29 : leavesOK ctxLitU 341575000000 2 ((leaves.drop 19458).take 142) 345100000000 2 = true :=
    take_step (n := 2) (t := 142) (b := 19460) rfl rfl ArealUCore.ArealUK.chunk_9729 s30
  have s28 : leavesOK ctxLitU 341525000000 2 ((leaves.drop 19456).take 144) 345100000000 2 = true :=
    take_step (n := 2) (t := 144) (b := 19458) rfl rfl ArealUCore.ArealUK.chunk_9728 s29
  have s27 : leavesOK ctxLitU 341475000000 2 ((leaves.drop 19454).take 146) 345100000000 2 = true :=
    take_step (n := 2) (t := 146) (b := 19456) rfl rfl ArealUCore.ArealUK.chunk_9727 s28
  have s26 : leavesOK ctxLitU 341425000000 2 ((leaves.drop 19452).take 148) 345100000000 2 = true :=
    take_step (n := 2) (t := 148) (b := 19454) rfl rfl ArealUCore.ArealUK.chunk_9726 s27
  have s25 : leavesOK ctxLitU 341375000000 2 ((leaves.drop 19450).take 150) 345100000000 2 = true :=
    take_step (n := 2) (t := 150) (b := 19452) rfl rfl ArealUCore.ArealUK.chunk_9725 s26
  have s24 : leavesOK ctxLitU 682675000000 3 ((leaves.drop 19448).take 152) 345100000000 2 = true :=
    take_step (n := 2) (t := 152) (b := 19450) rfl rfl ArealUCore.ArealUK.chunk_9724 s25
  have s23 : leavesOK ctxLitU 682625000000 3 ((leaves.drop 19446).take 154) 345100000000 2 = true :=
    take_step (n := 2) (t := 154) (b := 19448) rfl rfl ArealUCore.ArealUK.chunk_9723 s24
  have s22 : leavesOK ctxLitU 682575000000 3 ((leaves.drop 19444).take 156) 345100000000 2 = true :=
    take_step (n := 2) (t := 156) (b := 19446) rfl rfl ArealUCore.ArealUK.chunk_9722 s23
  have s21 : leavesOK ctxLitU 682525000000 3 ((leaves.drop 19442).take 158) 345100000000 2 = true :=
    take_step (n := 2) (t := 158) (b := 19444) rfl rfl ArealUCore.ArealUK.chunk_9721 s22
  have s20 : leavesOK ctxLitU 682475000000 3 ((leaves.drop 19440).take 160) 345100000000 2 = true :=
    take_step (n := 2) (t := 160) (b := 19442) rfl rfl ArealUCore.ArealUK.chunk_9720 s21
  have s19 : leavesOK ctxLitU 341200000000 2 ((leaves.drop 19438).take 162) 345100000000 2 = true :=
    take_step (n := 2) (t := 162) (b := 19440) rfl rfl ArealUCore.ArealUK.chunk_9719 s20
  have s18 : leavesOK ctxLitU 170575000000 1 ((leaves.drop 19436).take 164) 345100000000 2 = true :=
    take_step (n := 2) (t := 164) (b := 19438) rfl rfl ArealUCore.ArealUK.chunk_9718 s19
  have s17 : leavesOK ctxLitU 341125000000 2 ((leaves.drop 19434).take 166) 345100000000 2 = true :=
    take_step (n := 2) (t := 166) (b := 19436) rfl rfl ArealUCore.ArealUK.chunk_9717 s18
  have s16 : leavesOK ctxLitU 682212500000 3 ((leaves.drop 19432).take 168) 345100000000 2 = true :=
    take_step (n := 2) (t := 168) (b := 19434) rfl rfl ArealUCore.ArealUK.chunk_9716 s17
  have s15 : leavesOK ctxLitU 170543750000 1 ((leaves.drop 19430).take 170) 345100000000 2 = true :=
    take_step (n := 2) (t := 170) (b := 19432) rfl rfl ArealUCore.ArealUK.chunk_9715 s16
  have s14 : leavesOK ctxLitU 85262500000 0 ((leaves.drop 19428).take 172) 345100000000 2 = true :=
    take_step (n := 2) (t := 172) (b := 19430) rfl rfl ArealUCore.ArealUK.chunk_9714 s15
  have s13 : leavesOK ctxLitU 85250000000 0 ((leaves.drop 19426).take 174) 345100000000 2 = true :=
    take_step (n := 2) (t := 174) (b := 19428) rfl rfl ArealUCore.ArealUK.chunk_9713 s14
  have s12 : leavesOK ctxLitU 85237500000 0 ((leaves.drop 19424).take 176) 345100000000 2 = true :=
    take_step (n := 2) (t := 176) (b := 19426) rfl rfl ArealUCore.ArealUK.chunk_9712 s13
  have s11 : leavesOK ctxLitU 85225000000 0 ((leaves.drop 19422).take 178) 345100000000 2 = true :=
    take_step (n := 2) (t := 178) (b := 19424) rfl rfl ArealUCore.ArealUK.chunk_9711 s12
  have s10 : leavesOK ctxLitU 85200000000 0 ((leaves.drop 19420).take 180) 345100000000 2 = true :=
    take_step (n := 2) (t := 180) (b := 19422) rfl rfl ArealUCore.ArealUK.chunk_9710 s11
  have s9 : leavesOK ctxLitU 85150000000 0 ((leaves.drop 19418).take 182) 345100000000 2 = true :=
    take_step (n := 2) (t := 182) (b := 19420) rfl rfl ArealUCore.ArealUK.chunk_9709 s10
  have s8 : leavesOK ctxLitU 85100000000 0 ((leaves.drop 19416).take 184) 345100000000 2 = true :=
    take_step (n := 2) (t := 184) (b := 19418) rfl rfl ArealUCore.ArealUK.chunk_9708 s9
  have s7 : leavesOK ctxLitU 85050000000 0 ((leaves.drop 19414).take 186) 345100000000 2 = true :=
    take_step (n := 2) (t := 186) (b := 19416) rfl rfl ArealUCore.ArealUK.chunk_9707 s8
  have s6 : leavesOK ctxLitU 348354459452488 12 ((leaves.drop 19412).take 188) 345100000000 2 = true :=
    take_step (n := 2) (t := 188) (b := 19414) rfl rfl ArealUCore.ArealUK.chunk_9706 s7
  have s5 : leavesOK ctxLitU 85000000000 0 ((leaves.drop 19410).take 190) 345100000000 2 = true :=
    take_step (n := 2) (t := 190) (b := 19412) rfl rfl ArealUCore.ArealUK.chunk_9705 s6
  have s4 : leavesOK ctxLitU 84950000000 0 ((leaves.drop 19408).take 192) 345100000000 2 = true :=
    take_step (n := 2) (t := 192) (b := 19410) rfl rfl ArealUCore.ArealUK.chunk_9704 s5
  have s3 : leavesOK ctxLitU 84900000000 0 ((leaves.drop 19406).take 194) 345100000000 2 = true :=
    take_step (n := 2) (t := 194) (b := 19408) rfl rfl ArealUCore.ArealUK.chunk_9703 s4
  have s2 : leavesOK ctxLitU 84875000000 0 ((leaves.drop 19404).take 196) 345100000000 2 = true :=
    take_step (n := 2) (t := 196) (b := 19406) rfl rfl ArealUCore.ArealUK.chunk_9702 s3
  have s1 : leavesOK ctxLitU 84862500000 0 ((leaves.drop 19402).take 198) 345100000000 2 = true :=
    take_step (n := 2) (t := 198) (b := 19404) rfl rfl ArealUCore.ArealUK.chunk_9701 s2
  have s0 : leavesOK ctxLitU 84850000000 0 ((leaves.drop 19400).take 200) 345100000000 2 = true :=
    take_step (n := 2) (t := 200) (b := 19402) rfl rfl ArealUCore.ArealUK.chunk_9700 s1
  exact s0

end Areal.UCert

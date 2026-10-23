import ArealUK.Chunk11700
import ArealUK.Chunk11701
import ArealUK.Chunk11702
import ArealUK.Chunk11703
import ArealUK.Chunk11704
import ArealUK.Chunk11705
import ArealUK.Chunk11706
import ArealUK.Chunk11707
import ArealUK.Chunk11708
import ArealUK.Chunk11709
import ArealUK.Chunk11710
import ArealUK.Chunk11711
import ArealUK.Chunk11712
import ArealUK.Chunk11713
import ArealUK.Chunk11714
import ArealUK.Chunk11715
import ArealUK.Chunk11716
import ArealUK.Chunk11717
import ArealUK.Chunk11718
import ArealUK.Chunk11719
import ArealUK.Chunk11720
import ArealUK.Chunk11721
import ArealUK.Chunk11722
import ArealUK.Chunk11723
import ArealUK.Chunk11724
import ArealUK.Chunk11725
import ArealUK.Chunk11726
import ArealUK.Chunk11727
import ArealUK.Chunk11728
import ArealUK.Chunk11729
import ArealUK.Chunk11730
import ArealUK.Chunk11731
import ArealUK.Chunk11732
import ArealUK.Chunk11733
import ArealUK.Chunk11734
import ArealUK.Chunk11735
import ArealUK.Chunk11736
import ArealUK.Chunk11737
import ArealUK.Chunk11738
import ArealUK.Chunk11739
import ArealUK.Chunk11740
import ArealUK.Chunk11741
import ArealUK.Chunk11742
import ArealUK.Chunk11743
import ArealUK.Chunk11744
import ArealUK.Chunk11745
import ArealUK.Chunk11746
import ArealUK.Chunk11747
import ArealUK.Chunk11748
import ArealUK.Chunk11749
import ArealUK.Chunk11750
import ArealUK.Chunk11751
import ArealUK.Chunk11752
import ArealUK.Chunk11753
import ArealUK.Chunk11754
import ArealUK.Chunk11755
import ArealUK.Chunk11756
import ArealUK.Chunk11757
import ArealUK.Chunk11758
import ArealUK.Chunk11759
import ArealUK.Chunk11760
import ArealUK.Chunk11761
import ArealUK.Chunk11762
import ArealUK.Chunk11763
import ArealUK.Chunk11764
import ArealUK.Chunk11765
import ArealUK.Chunk11766
import ArealUK.Chunk11767
import ArealUK.Chunk11768
import ArealUK.Chunk11769
import ArealUK.Chunk11770
import ArealUK.Chunk11771
import ArealUK.Chunk11772
import ArealUK.Chunk11773
import ArealUK.Chunk11774
import ArealUK.Chunk11775
import ArealUK.Chunk11776
import ArealUK.Chunk11777
import ArealUK.Chunk11778
import ArealUK.Chunk11779
import ArealUK.Chunk11780
import ArealUK.Chunk11781
import ArealUK.Chunk11782
import ArealUK.Chunk11783
import ArealUK.Chunk11784
import ArealUK.Chunk11785
import ArealUK.Chunk11786
import ArealUK.Chunk11787
import ArealUK.Chunk11788
import ArealUK.Chunk11789
import ArealUK.Chunk11790
import ArealUK.Chunk11791
import ArealUK.Chunk11792
import ArealUK.Chunk11793
import ArealUK.Chunk11794
import ArealUK.Chunk11795
import ArealUK.Chunk11796
import ArealUK.Chunk11797
import ArealUK.Chunk11798
import ArealUK.Chunk11799
import Areal.UCert.LeavesKGen

/-! Group 117 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_117 : leavesOK ctxLitU 461750000000 2 ((leaves.drop 23400).take 200) 466750000000 2 = true := by
  have s99 := ArealUCore.ArealUK.chunk_11799
  have s98 : leavesOK ctxLitU 466650000000 2 ((leaves.drop 23596).take 4) 466750000000 2 = true :=
    take_step (n := 2) (t := 4) (b := 23598) rfl rfl ArealUCore.ArealUK.chunk_11798 s99
  have s97 : leavesOK ctxLitU 466600000000 2 ((leaves.drop 23594).take 6) 466750000000 2 = true :=
    take_step (n := 2) (t := 6) (b := 23596) rfl rfl ArealUCore.ArealUK.chunk_11797 s98
  have s96 : leavesOK ctxLitU 466550000000 2 ((leaves.drop 23592).take 8) 466750000000 2 = true :=
    take_step (n := 2) (t := 8) (b := 23594) rfl rfl ArealUCore.ArealUK.chunk_11796 s97
  have s95 : leavesOK ctxLitU 466500000000 2 ((leaves.drop 23590).take 10) 466750000000 2 = true :=
    take_step (n := 2) (t := 10) (b := 23592) rfl rfl ArealUCore.ArealUK.chunk_11795 s96
  have s94 : leavesOK ctxLitU 466450000000 2 ((leaves.drop 23588).take 12) 466750000000 2 = true :=
    take_step (n := 2) (t := 12) (b := 23590) rfl rfl ArealUCore.ArealUK.chunk_11794 s95
  have s93 : leavesOK ctxLitU 466400000000 2 ((leaves.drop 23586).take 14) 466750000000 2 = true :=
    take_step (n := 2) (t := 14) (b := 23588) rfl rfl ArealUCore.ArealUK.chunk_11793 s94
  have s92 : leavesOK ctxLitU 466350000000 2 ((leaves.drop 23584).take 16) 466750000000 2 = true :=
    take_step (n := 2) (t := 16) (b := 23586) rfl rfl ArealUCore.ArealUK.chunk_11792 s93
  have s91 : leavesOK ctxLitU 466300000000 2 ((leaves.drop 23582).take 18) 466750000000 2 = true :=
    take_step (n := 2) (t := 18) (b := 23584) rfl rfl ArealUCore.ArealUK.chunk_11791 s92
  have s90 : leavesOK ctxLitU 466250000000 2 ((leaves.drop 23580).take 20) 466750000000 2 = true :=
    take_step (n := 2) (t := 20) (b := 23582) rfl rfl ArealUCore.ArealUK.chunk_11790 s91
  have s89 : leavesOK ctxLitU 466200000000 2 ((leaves.drop 23578).take 22) 466750000000 2 = true :=
    take_step (n := 2) (t := 22) (b := 23580) rfl rfl ArealUCore.ArealUK.chunk_11789 s90
  have s88 : leavesOK ctxLitU 466150000000 2 ((leaves.drop 23576).take 24) 466750000000 2 = true :=
    take_step (n := 2) (t := 24) (b := 23578) rfl rfl ArealUCore.ArealUK.chunk_11788 s89
  have s87 : leavesOK ctxLitU 466100000000 2 ((leaves.drop 23574).take 26) 466750000000 2 = true :=
    take_step (n := 2) (t := 26) (b := 23576) rfl rfl ArealUCore.ArealUK.chunk_11787 s88
  have s86 : leavesOK ctxLitU 466050000000 2 ((leaves.drop 23572).take 28) 466750000000 2 = true :=
    take_step (n := 2) (t := 28) (b := 23574) rfl rfl ArealUCore.ArealUK.chunk_11786 s87
  have s85 : leavesOK ctxLitU 466000000000 2 ((leaves.drop 23570).take 30) 466750000000 2 = true :=
    take_step (n := 2) (t := 30) (b := 23572) rfl rfl ArealUCore.ArealUK.chunk_11785 s86
  have s84 : leavesOK ctxLitU 465950000000 2 ((leaves.drop 23568).take 32) 466750000000 2 = true :=
    take_step (n := 2) (t := 32) (b := 23570) rfl rfl ArealUCore.ArealUK.chunk_11784 s85
  have s83 : leavesOK ctxLitU 465900000000 2 ((leaves.drop 23566).take 34) 466750000000 2 = true :=
    take_step (n := 2) (t := 34) (b := 23568) rfl rfl ArealUCore.ArealUK.chunk_11783 s84
  have s82 : leavesOK ctxLitU 465850000000 2 ((leaves.drop 23564).take 36) 466750000000 2 = true :=
    take_step (n := 2) (t := 36) (b := 23566) rfl rfl ArealUCore.ArealUK.chunk_11782 s83
  have s81 : leavesOK ctxLitU 465800000000 2 ((leaves.drop 23562).take 38) 466750000000 2 = true :=
    take_step (n := 2) (t := 38) (b := 23564) rfl rfl ArealUCore.ArealUK.chunk_11781 s82
  have s80 : leavesOK ctxLitU 465750000000 2 ((leaves.drop 23560).take 40) 466750000000 2 = true :=
    take_step (n := 2) (t := 40) (b := 23562) rfl rfl ArealUCore.ArealUK.chunk_11780 s81
  have s79 : leavesOK ctxLitU 465700000000 2 ((leaves.drop 23558).take 42) 466750000000 2 = true :=
    take_step (n := 2) (t := 42) (b := 23560) rfl rfl ArealUCore.ArealUK.chunk_11779 s80
  have s78 : leavesOK ctxLitU 465650000000 2 ((leaves.drop 23556).take 44) 466750000000 2 = true :=
    take_step (n := 2) (t := 44) (b := 23558) rfl rfl ArealUCore.ArealUK.chunk_11778 s79
  have s77 : leavesOK ctxLitU 465600000000 2 ((leaves.drop 23554).take 46) 466750000000 2 = true :=
    take_step (n := 2) (t := 46) (b := 23556) rfl rfl ArealUCore.ArealUK.chunk_11777 s78
  have s76 : leavesOK ctxLitU 465550000000 2 ((leaves.drop 23552).take 48) 466750000000 2 = true :=
    take_step (n := 2) (t := 48) (b := 23554) rfl rfl ArealUCore.ArealUK.chunk_11776 s77
  have s75 : leavesOK ctxLitU 465500000000 2 ((leaves.drop 23550).take 50) 466750000000 2 = true :=
    take_step (n := 2) (t := 50) (b := 23552) rfl rfl ArealUCore.ArealUK.chunk_11775 s76
  have s74 : leavesOK ctxLitU 465450000000 2 ((leaves.drop 23548).take 52) 466750000000 2 = true :=
    take_step (n := 2) (t := 52) (b := 23550) rfl rfl ArealUCore.ArealUK.chunk_11774 s75
  have s73 : leavesOK ctxLitU 465400000000 2 ((leaves.drop 23546).take 54) 466750000000 2 = true :=
    take_step (n := 2) (t := 54) (b := 23548) rfl rfl ArealUCore.ArealUK.chunk_11773 s74
  have s72 : leavesOK ctxLitU 465350000000 2 ((leaves.drop 23544).take 56) 466750000000 2 = true :=
    take_step (n := 2) (t := 56) (b := 23546) rfl rfl ArealUCore.ArealUK.chunk_11772 s73
  have s71 : leavesOK ctxLitU 465300000000 2 ((leaves.drop 23542).take 58) 466750000000 2 = true :=
    take_step (n := 2) (t := 58) (b := 23544) rfl rfl ArealUCore.ArealUK.chunk_11771 s72
  have s70 : leavesOK ctxLitU 465250000000 2 ((leaves.drop 23540).take 60) 466750000000 2 = true :=
    take_step (n := 2) (t := 60) (b := 23542) rfl rfl ArealUCore.ArealUK.chunk_11770 s71
  have s69 : leavesOK ctxLitU 465200000000 2 ((leaves.drop 23538).take 62) 466750000000 2 = true :=
    take_step (n := 2) (t := 62) (b := 23540) rfl rfl ArealUCore.ArealUK.chunk_11769 s70
  have s68 : leavesOK ctxLitU 465150000000 2 ((leaves.drop 23536).take 64) 466750000000 2 = true :=
    take_step (n := 2) (t := 64) (b := 23538) rfl rfl ArealUCore.ArealUK.chunk_11768 s69
  have s67 : leavesOK ctxLitU 465100000000 2 ((leaves.drop 23534).take 66) 466750000000 2 = true :=
    take_step (n := 2) (t := 66) (b := 23536) rfl rfl ArealUCore.ArealUK.chunk_11767 s68
  have s66 : leavesOK ctxLitU 465050000000 2 ((leaves.drop 23532).take 68) 466750000000 2 = true :=
    take_step (n := 2) (t := 68) (b := 23534) rfl rfl ArealUCore.ArealUK.chunk_11766 s67
  have s65 : leavesOK ctxLitU 465000000000 2 ((leaves.drop 23530).take 70) 466750000000 2 = true :=
    take_step (n := 2) (t := 70) (b := 23532) rfl rfl ArealUCore.ArealUK.chunk_11765 s66
  have s64 : leavesOK ctxLitU 464950000000 2 ((leaves.drop 23528).take 72) 466750000000 2 = true :=
    take_step (n := 2) (t := 72) (b := 23530) rfl rfl ArealUCore.ArealUK.chunk_11764 s65
  have s63 : leavesOK ctxLitU 464900000000 2 ((leaves.drop 23526).take 74) 466750000000 2 = true :=
    take_step (n := 2) (t := 74) (b := 23528) rfl rfl ArealUCore.ArealUK.chunk_11763 s64
  have s62 : leavesOK ctxLitU 464850000000 2 ((leaves.drop 23524).take 76) 466750000000 2 = true :=
    take_step (n := 2) (t := 76) (b := 23526) rfl rfl ArealUCore.ArealUK.chunk_11762 s63
  have s61 : leavesOK ctxLitU 464800000000 2 ((leaves.drop 23522).take 78) 466750000000 2 = true :=
    take_step (n := 2) (t := 78) (b := 23524) rfl rfl ArealUCore.ArealUK.chunk_11761 s62
  have s60 : leavesOK ctxLitU 464750000000 2 ((leaves.drop 23520).take 80) 466750000000 2 = true :=
    take_step (n := 2) (t := 80) (b := 23522) rfl rfl ArealUCore.ArealUK.chunk_11760 s61
  have s59 : leavesOK ctxLitU 464700000000 2 ((leaves.drop 23518).take 82) 466750000000 2 = true :=
    take_step (n := 2) (t := 82) (b := 23520) rfl rfl ArealUCore.ArealUK.chunk_11759 s60
  have s58 : leavesOK ctxLitU 464650000000 2 ((leaves.drop 23516).take 84) 466750000000 2 = true :=
    take_step (n := 2) (t := 84) (b := 23518) rfl rfl ArealUCore.ArealUK.chunk_11758 s59
  have s57 : leavesOK ctxLitU 464600000000 2 ((leaves.drop 23514).take 86) 466750000000 2 = true :=
    take_step (n := 2) (t := 86) (b := 23516) rfl rfl ArealUCore.ArealUK.chunk_11757 s58
  have s56 : leavesOK ctxLitU 464550000000 2 ((leaves.drop 23512).take 88) 466750000000 2 = true :=
    take_step (n := 2) (t := 88) (b := 23514) rfl rfl ArealUCore.ArealUK.chunk_11756 s57
  have s55 : leavesOK ctxLitU 464500000000 2 ((leaves.drop 23510).take 90) 466750000000 2 = true :=
    take_step (n := 2) (t := 90) (b := 23512) rfl rfl ArealUCore.ArealUK.chunk_11755 s56
  have s54 : leavesOK ctxLitU 464450000000 2 ((leaves.drop 23508).take 92) 466750000000 2 = true :=
    take_step (n := 2) (t := 92) (b := 23510) rfl rfl ArealUCore.ArealUK.chunk_11754 s55
  have s53 : leavesOK ctxLitU 464400000000 2 ((leaves.drop 23506).take 94) 466750000000 2 = true :=
    take_step (n := 2) (t := 94) (b := 23508) rfl rfl ArealUCore.ArealUK.chunk_11753 s54
  have s52 : leavesOK ctxLitU 464350000000 2 ((leaves.drop 23504).take 96) 466750000000 2 = true :=
    take_step (n := 2) (t := 96) (b := 23506) rfl rfl ArealUCore.ArealUK.chunk_11752 s53
  have s51 : leavesOK ctxLitU 464300000000 2 ((leaves.drop 23502).take 98) 466750000000 2 = true :=
    take_step (n := 2) (t := 98) (b := 23504) rfl rfl ArealUCore.ArealUK.chunk_11751 s52
  have s50 : leavesOK ctxLitU 464250000000 2 ((leaves.drop 23500).take 100) 466750000000 2 = true :=
    take_step (n := 2) (t := 100) (b := 23502) rfl rfl ArealUCore.ArealUK.chunk_11750 s51
  have s49 : leavesOK ctxLitU 464200000000 2 ((leaves.drop 23498).take 102) 466750000000 2 = true :=
    take_step (n := 2) (t := 102) (b := 23500) rfl rfl ArealUCore.ArealUK.chunk_11749 s50
  have s48 : leavesOK ctxLitU 464150000000 2 ((leaves.drop 23496).take 104) 466750000000 2 = true :=
    take_step (n := 2) (t := 104) (b := 23498) rfl rfl ArealUCore.ArealUK.chunk_11748 s49
  have s47 : leavesOK ctxLitU 464100000000 2 ((leaves.drop 23494).take 106) 466750000000 2 = true :=
    take_step (n := 2) (t := 106) (b := 23496) rfl rfl ArealUCore.ArealUK.chunk_11747 s48
  have s46 : leavesOK ctxLitU 464050000000 2 ((leaves.drop 23492).take 108) 466750000000 2 = true :=
    take_step (n := 2) (t := 108) (b := 23494) rfl rfl ArealUCore.ArealUK.chunk_11746 s47
  have s45 : leavesOK ctxLitU 464000000000 2 ((leaves.drop 23490).take 110) 466750000000 2 = true :=
    take_step (n := 2) (t := 110) (b := 23492) rfl rfl ArealUCore.ArealUK.chunk_11745 s46
  have s44 : leavesOK ctxLitU 463950000000 2 ((leaves.drop 23488).take 112) 466750000000 2 = true :=
    take_step (n := 2) (t := 112) (b := 23490) rfl rfl ArealUCore.ArealUK.chunk_11744 s45
  have s43 : leavesOK ctxLitU 463900000000 2 ((leaves.drop 23486).take 114) 466750000000 2 = true :=
    take_step (n := 2) (t := 114) (b := 23488) rfl rfl ArealUCore.ArealUK.chunk_11743 s44
  have s42 : leavesOK ctxLitU 463850000000 2 ((leaves.drop 23484).take 116) 466750000000 2 = true :=
    take_step (n := 2) (t := 116) (b := 23486) rfl rfl ArealUCore.ArealUK.chunk_11742 s43
  have s41 : leavesOK ctxLitU 463800000000 2 ((leaves.drop 23482).take 118) 466750000000 2 = true :=
    take_step (n := 2) (t := 118) (b := 23484) rfl rfl ArealUCore.ArealUK.chunk_11741 s42
  have s40 : leavesOK ctxLitU 463750000000 2 ((leaves.drop 23480).take 120) 466750000000 2 = true :=
    take_step (n := 2) (t := 120) (b := 23482) rfl rfl ArealUCore.ArealUK.chunk_11740 s41
  have s39 : leavesOK ctxLitU 463700000000 2 ((leaves.drop 23478).take 122) 466750000000 2 = true :=
    take_step (n := 2) (t := 122) (b := 23480) rfl rfl ArealUCore.ArealUK.chunk_11739 s40
  have s38 : leavesOK ctxLitU 463650000000 2 ((leaves.drop 23476).take 124) 466750000000 2 = true :=
    take_step (n := 2) (t := 124) (b := 23478) rfl rfl ArealUCore.ArealUK.chunk_11738 s39
  have s37 : leavesOK ctxLitU 463600000000 2 ((leaves.drop 23474).take 126) 466750000000 2 = true :=
    take_step (n := 2) (t := 126) (b := 23476) rfl rfl ArealUCore.ArealUK.chunk_11737 s38
  have s36 : leavesOK ctxLitU 463550000000 2 ((leaves.drop 23472).take 128) 466750000000 2 = true :=
    take_step (n := 2) (t := 128) (b := 23474) rfl rfl ArealUCore.ArealUK.chunk_11736 s37
  have s35 : leavesOK ctxLitU 463500000000 2 ((leaves.drop 23470).take 130) 466750000000 2 = true :=
    take_step (n := 2) (t := 130) (b := 23472) rfl rfl ArealUCore.ArealUK.chunk_11735 s36
  have s34 : leavesOK ctxLitU 463450000000 2 ((leaves.drop 23468).take 132) 466750000000 2 = true :=
    take_step (n := 2) (t := 132) (b := 23470) rfl rfl ArealUCore.ArealUK.chunk_11734 s35
  have s33 : leavesOK ctxLitU 463400000000 2 ((leaves.drop 23466).take 134) 466750000000 2 = true :=
    take_step (n := 2) (t := 134) (b := 23468) rfl rfl ArealUCore.ArealUK.chunk_11733 s34
  have s32 : leavesOK ctxLitU 463350000000 2 ((leaves.drop 23464).take 136) 466750000000 2 = true :=
    take_step (n := 2) (t := 136) (b := 23466) rfl rfl ArealUCore.ArealUK.chunk_11732 s33
  have s31 : leavesOK ctxLitU 463300000000 2 ((leaves.drop 23462).take 138) 466750000000 2 = true :=
    take_step (n := 2) (t := 138) (b := 23464) rfl rfl ArealUCore.ArealUK.chunk_11731 s32
  have s30 : leavesOK ctxLitU 463250000000 2 ((leaves.drop 23460).take 140) 466750000000 2 = true :=
    take_step (n := 2) (t := 140) (b := 23462) rfl rfl ArealUCore.ArealUK.chunk_11730 s31
  have s29 : leavesOK ctxLitU 463200000000 2 ((leaves.drop 23458).take 142) 466750000000 2 = true :=
    take_step (n := 2) (t := 142) (b := 23460) rfl rfl ArealUCore.ArealUK.chunk_11729 s30
  have s28 : leavesOK ctxLitU 463150000000 2 ((leaves.drop 23456).take 144) 466750000000 2 = true :=
    take_step (n := 2) (t := 144) (b := 23458) rfl rfl ArealUCore.ArealUK.chunk_11728 s29
  have s27 : leavesOK ctxLitU 463100000000 2 ((leaves.drop 23454).take 146) 466750000000 2 = true :=
    take_step (n := 2) (t := 146) (b := 23456) rfl rfl ArealUCore.ArealUK.chunk_11727 s28
  have s26 : leavesOK ctxLitU 463050000000 2 ((leaves.drop 23452).take 148) 466750000000 2 = true :=
    take_step (n := 2) (t := 148) (b := 23454) rfl rfl ArealUCore.ArealUK.chunk_11726 s27
  have s25 : leavesOK ctxLitU 463000000000 2 ((leaves.drop 23450).take 150) 466750000000 2 = true :=
    take_step (n := 2) (t := 150) (b := 23452) rfl rfl ArealUCore.ArealUK.chunk_11725 s26
  have s24 : leavesOK ctxLitU 462950000000 2 ((leaves.drop 23448).take 152) 466750000000 2 = true :=
    take_step (n := 2) (t := 152) (b := 23450) rfl rfl ArealUCore.ArealUK.chunk_11724 s25
  have s23 : leavesOK ctxLitU 462900000000 2 ((leaves.drop 23446).take 154) 466750000000 2 = true :=
    take_step (n := 2) (t := 154) (b := 23448) rfl rfl ArealUCore.ArealUK.chunk_11723 s24
  have s22 : leavesOK ctxLitU 462850000000 2 ((leaves.drop 23444).take 156) 466750000000 2 = true :=
    take_step (n := 2) (t := 156) (b := 23446) rfl rfl ArealUCore.ArealUK.chunk_11722 s23
  have s21 : leavesOK ctxLitU 462800000000 2 ((leaves.drop 23442).take 158) 466750000000 2 = true :=
    take_step (n := 2) (t := 158) (b := 23444) rfl rfl ArealUCore.ArealUK.chunk_11721 s22
  have s20 : leavesOK ctxLitU 462750000000 2 ((leaves.drop 23440).take 160) 466750000000 2 = true :=
    take_step (n := 2) (t := 160) (b := 23442) rfl rfl ArealUCore.ArealUK.chunk_11720 s21
  have s19 : leavesOK ctxLitU 462700000000 2 ((leaves.drop 23438).take 162) 466750000000 2 = true :=
    take_step (n := 2) (t := 162) (b := 23440) rfl rfl ArealUCore.ArealUK.chunk_11719 s20
  have s18 : leavesOK ctxLitU 462650000000 2 ((leaves.drop 23436).take 164) 466750000000 2 = true :=
    take_step (n := 2) (t := 164) (b := 23438) rfl rfl ArealUCore.ArealUK.chunk_11718 s19
  have s17 : leavesOK ctxLitU 462600000000 2 ((leaves.drop 23434).take 166) 466750000000 2 = true :=
    take_step (n := 2) (t := 166) (b := 23436) rfl rfl ArealUCore.ArealUK.chunk_11717 s18
  have s16 : leavesOK ctxLitU 462550000000 2 ((leaves.drop 23432).take 168) 466750000000 2 = true :=
    take_step (n := 2) (t := 168) (b := 23434) rfl rfl ArealUCore.ArealUK.chunk_11716 s17
  have s15 : leavesOK ctxLitU 462500000000 2 ((leaves.drop 23430).take 170) 466750000000 2 = true :=
    take_step (n := 2) (t := 170) (b := 23432) rfl rfl ArealUCore.ArealUK.chunk_11715 s16
  have s14 : leavesOK ctxLitU 462450000000 2 ((leaves.drop 23428).take 172) 466750000000 2 = true :=
    take_step (n := 2) (t := 172) (b := 23430) rfl rfl ArealUCore.ArealUK.chunk_11714 s15
  have s13 : leavesOK ctxLitU 462400000000 2 ((leaves.drop 23426).take 174) 466750000000 2 = true :=
    take_step (n := 2) (t := 174) (b := 23428) rfl rfl ArealUCore.ArealUK.chunk_11713 s14
  have s12 : leavesOK ctxLitU 462350000000 2 ((leaves.drop 23424).take 176) 466750000000 2 = true :=
    take_step (n := 2) (t := 176) (b := 23426) rfl rfl ArealUCore.ArealUK.chunk_11712 s13
  have s11 : leavesOK ctxLitU 462300000000 2 ((leaves.drop 23422).take 178) 466750000000 2 = true :=
    take_step (n := 2) (t := 178) (b := 23424) rfl rfl ArealUCore.ArealUK.chunk_11711 s12
  have s10 : leavesOK ctxLitU 462250000000 2 ((leaves.drop 23420).take 180) 466750000000 2 = true :=
    take_step (n := 2) (t := 180) (b := 23422) rfl rfl ArealUCore.ArealUK.chunk_11710 s11
  have s9 : leavesOK ctxLitU 462200000000 2 ((leaves.drop 23418).take 182) 466750000000 2 = true :=
    take_step (n := 2) (t := 182) (b := 23420) rfl rfl ArealUCore.ArealUK.chunk_11709 s10
  have s8 : leavesOK ctxLitU 462150000000 2 ((leaves.drop 23416).take 184) 466750000000 2 = true :=
    take_step (n := 2) (t := 184) (b := 23418) rfl rfl ArealUCore.ArealUK.chunk_11708 s9
  have s7 : leavesOK ctxLitU 462100000000 2 ((leaves.drop 23414).take 186) 466750000000 2 = true :=
    take_step (n := 2) (t := 186) (b := 23416) rfl rfl ArealUCore.ArealUK.chunk_11707 s8
  have s6 : leavesOK ctxLitU 462050000000 2 ((leaves.drop 23412).take 188) 466750000000 2 = true :=
    take_step (n := 2) (t := 188) (b := 23414) rfl rfl ArealUCore.ArealUK.chunk_11706 s7
  have s5 : leavesOK ctxLitU 462000000000 2 ((leaves.drop 23410).take 190) 466750000000 2 = true :=
    take_step (n := 2) (t := 190) (b := 23412) rfl rfl ArealUCore.ArealUK.chunk_11705 s6
  have s4 : leavesOK ctxLitU 461950000000 2 ((leaves.drop 23408).take 192) 466750000000 2 = true :=
    take_step (n := 2) (t := 192) (b := 23410) rfl rfl ArealUCore.ArealUK.chunk_11704 s5
  have s3 : leavesOK ctxLitU 461900000000 2 ((leaves.drop 23406).take 194) 466750000000 2 = true :=
    take_step (n := 2) (t := 194) (b := 23408) rfl rfl ArealUCore.ArealUK.chunk_11703 s4
  have s2 : leavesOK ctxLitU 461850000000 2 ((leaves.drop 23404).take 196) 466750000000 2 = true :=
    take_step (n := 2) (t := 196) (b := 23406) rfl rfl ArealUCore.ArealUK.chunk_11702 s3
  have s1 : leavesOK ctxLitU 461800000000 2 ((leaves.drop 23402).take 198) 466750000000 2 = true :=
    take_step (n := 2) (t := 198) (b := 23404) rfl rfl ArealUCore.ArealUK.chunk_11701 s2
  have s0 : leavesOK ctxLitU 461750000000 2 ((leaves.drop 23400).take 200) 466750000000 2 = true :=
    take_step (n := 2) (t := 200) (b := 23402) rfl rfl ArealUCore.ArealUK.chunk_11700 s1
  exact s0

end Areal.UCert

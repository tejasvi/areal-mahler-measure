import ArealUK.Chunk15700
import ArealUK.Chunk15701
import ArealUK.Chunk15702
import ArealUK.Chunk15703
import ArealUK.Chunk15704
import ArealUK.Chunk15705
import ArealUK.Chunk15706
import ArealUK.Chunk15707
import ArealUK.Chunk15708
import ArealUK.Chunk15709
import ArealUK.Chunk15710
import ArealUK.Chunk15711
import ArealUK.Chunk15712
import ArealUK.Chunk15713
import ArealUK.Chunk15714
import ArealUK.Chunk15715
import ArealUK.Chunk15716
import ArealUK.Chunk15717
import ArealUK.Chunk15718
import ArealUK.Chunk15719
import ArealUK.Chunk15720
import ArealUK.Chunk15721
import ArealUK.Chunk15722
import ArealUK.Chunk15723
import ArealUK.Chunk15724
import ArealUK.Chunk15725
import ArealUK.Chunk15726
import ArealUK.Chunk15727
import ArealUK.Chunk15728
import ArealUK.Chunk15729
import ArealUK.Chunk15730
import ArealUK.Chunk15731
import ArealUK.Chunk15732
import ArealUK.Chunk15733
import ArealUK.Chunk15734
import ArealUK.Chunk15735
import ArealUK.Chunk15736
import ArealUK.Chunk15737
import ArealUK.Chunk15738
import ArealUK.Chunk15739
import ArealUK.Chunk15740
import ArealUK.Chunk15741
import ArealUK.Chunk15742
import ArealUK.Chunk15743
import ArealUK.Chunk15744
import ArealUK.Chunk15745
import ArealUK.Chunk15746
import ArealUK.Chunk15747
import ArealUK.Chunk15748
import ArealUK.Chunk15749
import ArealUK.Chunk15750
import ArealUK.Chunk15751
import ArealUK.Chunk15752
import ArealUK.Chunk15753
import ArealUK.Chunk15754
import ArealUK.Chunk15755
import ArealUK.Chunk15756
import ArealUK.Chunk15757
import ArealUK.Chunk15758
import ArealUK.Chunk15759
import ArealUK.Chunk15760
import ArealUK.Chunk15761
import ArealUK.Chunk15762
import ArealUK.Chunk15763
import ArealUK.Chunk15764
import ArealUK.Chunk15765
import ArealUK.Chunk15766
import ArealUK.Chunk15767
import ArealUK.Chunk15768
import ArealUK.Chunk15769
import ArealUK.Chunk15770
import ArealUK.Chunk15771
import ArealUK.Chunk15772
import ArealUK.Chunk15773
import ArealUK.Chunk15774
import ArealUK.Chunk15775
import ArealUK.Chunk15776
import ArealUK.Chunk15777
import ArealUK.Chunk15778
import ArealUK.Chunk15779
import ArealUK.Chunk15780
import ArealUK.Chunk15781
import ArealUK.Chunk15782
import ArealUK.Chunk15783
import ArealUK.Chunk15784
import ArealUK.Chunk15785
import ArealUK.Chunk15786
import ArealUK.Chunk15787
import ArealUK.Chunk15788
import ArealUK.Chunk15789
import ArealUK.Chunk15790
import ArealUK.Chunk15791
import ArealUK.Chunk15792
import ArealUK.Chunk15793
import ArealUK.Chunk15794
import ArealUK.Chunk15795
import ArealUK.Chunk15796
import ArealUK.Chunk15797
import ArealUK.Chunk15798
import ArealUK.Chunk15799
import Areal.UCert.LeavesKGen

/-! Group 157 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_157 : leavesOK ctxLitU 166668750000 0 ((leaves.drop 31400).take 200) 168168750000 0 = true := by
  have s99 := ArealUCore.ArealUK.chunk_15799
  have s98 : leavesOK ctxLitU 168143750000 0 ((leaves.drop 31596).take 4) 168168750000 0 = true :=
    take_step (n := 2) (t := 4) (b := 31598) rfl rfl ArealUCore.ArealUK.chunk_15798 s99
  have s97 : leavesOK ctxLitU 168131250000 0 ((leaves.drop 31594).take 6) 168168750000 0 = true :=
    take_step (n := 2) (t := 6) (b := 31596) rfl rfl ArealUCore.ArealUK.chunk_15797 s98
  have s96 : leavesOK ctxLitU 168112500000 0 ((leaves.drop 31592).take 8) 168168750000 0 = true :=
    take_step (n := 2) (t := 8) (b := 31594) rfl rfl ArealUCore.ArealUK.chunk_15796 s97
  have s95 : leavesOK ctxLitU 336175000000 1 ((leaves.drop 31590).take 10) 168168750000 0 = true :=
    take_step (n := 2) (t := 10) (b := 31592) rfl rfl ArealUCore.ArealUK.chunk_15795 s96
  have s94 : leavesOK ctxLitU 336125000000 1 ((leaves.drop 31588).take 12) 168168750000 0 = true :=
    take_step (n := 2) (t := 12) (b := 31590) rfl rfl ArealUCore.ArealUK.chunk_15794 s95
  have s93 : leavesOK ctxLitU 336075000000 1 ((leaves.drop 31586).take 14) 168168750000 0 = true :=
    take_step (n := 2) (t := 14) (b := 31588) rfl rfl ArealUCore.ArealUK.chunk_15793 s94
  have s92 : leavesOK ctxLitU 336025000000 1 ((leaves.drop 31584).take 16) 168168750000 0 = true :=
    take_step (n := 2) (t := 16) (b := 31586) rfl rfl ArealUCore.ArealUK.chunk_15792 s93
  have s91 : leavesOK ctxLitU 167987500000 0 ((leaves.drop 31582).take 18) 168168750000 0 = true :=
    take_step (n := 2) (t := 18) (b := 31584) rfl rfl ArealUCore.ArealUK.chunk_15791 s92
  have s90 : leavesOK ctxLitU 167968750000 0 ((leaves.drop 31580).take 20) 168168750000 0 = true :=
    take_step (n := 2) (t := 20) (b := 31582) rfl rfl ArealUCore.ArealUK.chunk_15790 s91
  have s89 : leavesOK ctxLitU 167956250000 0 ((leaves.drop 31578).take 22) 168168750000 0 = true :=
    take_step (n := 2) (t := 22) (b := 31580) rfl rfl ArealUCore.ArealUK.chunk_15789 s90
  have s88 : leavesOK ctxLitU 167943750000 0 ((leaves.drop 31576).take 24) 168168750000 0 = true :=
    take_step (n := 2) (t := 24) (b := 31578) rfl rfl ArealUCore.ArealUK.chunk_15788 s89
  have s87 : leavesOK ctxLitU 167931250000 0 ((leaves.drop 31574).take 26) 168168750000 0 = true :=
    take_step (n := 2) (t := 26) (b := 31576) rfl rfl ArealUCore.ArealUK.chunk_15787 s88
  have s86 : leavesOK ctxLitU 335837500000 1 ((leaves.drop 31572).take 28) 168168750000 0 = true :=
    take_step (n := 2) (t := 28) (b := 31574) rfl rfl ArealUCore.ArealUK.chunk_15786 s87
  have s85 : leavesOK ctxLitU 335812500000 1 ((leaves.drop 31570).take 30) 168168750000 0 = true :=
    take_step (n := 2) (t := 30) (b := 31572) rfl rfl ArealUCore.ArealUK.chunk_15785 s86
  have s84 : leavesOK ctxLitU 167887500000 0 ((leaves.drop 31568).take 32) 168168750000 0 = true :=
    take_step (n := 2) (t := 32) (b := 31570) rfl rfl ArealUCore.ArealUK.chunk_15784 s85
  have s83 : leavesOK ctxLitU 167868750000 0 ((leaves.drop 31566).take 34) 168168750000 0 = true :=
    take_step (n := 2) (t := 34) (b := 31568) rfl rfl ArealUCore.ArealUK.chunk_15783 s84
  have s82 : leavesOK ctxLitU 167856250000 0 ((leaves.drop 31564).take 36) 168168750000 0 = true :=
    take_step (n := 2) (t := 36) (b := 31566) rfl rfl ArealUCore.ArealUK.chunk_15782 s83
  have s81 : leavesOK ctxLitU 167843750000 0 ((leaves.drop 31562).take 38) 168168750000 0 = true :=
    take_step (n := 2) (t := 38) (b := 31564) rfl rfl ArealUCore.ArealUK.chunk_15781 s82
  have s80 : leavesOK ctxLitU 167831250000 0 ((leaves.drop 31560).take 40) 168168750000 0 = true :=
    take_step (n := 2) (t := 40) (b := 31562) rfl rfl ArealUCore.ArealUK.chunk_15780 s81
  have s79 : leavesOK ctxLitU 167812500000 0 ((leaves.drop 31558).take 42) 168168750000 0 = true :=
    take_step (n := 2) (t := 42) (b := 31560) rfl rfl ArealUCore.ArealUK.chunk_15779 s80
  have s78 : leavesOK ctxLitU 167793750000 0 ((leaves.drop 31556).take 44) 168168750000 0 = true :=
    take_step (n := 2) (t := 44) (b := 31558) rfl rfl ArealUCore.ArealUK.chunk_15778 s79
  have s77 : leavesOK ctxLitU 167781250000 0 ((leaves.drop 31554).take 46) 168168750000 0 = true :=
    take_step (n := 2) (t := 46) (b := 31556) rfl rfl ArealUCore.ArealUK.chunk_15777 s78
  have s76 : leavesOK ctxLitU 167768750000 0 ((leaves.drop 31552).take 48) 168168750000 0 = true :=
    take_step (n := 2) (t := 48) (b := 31554) rfl rfl ArealUCore.ArealUK.chunk_15776 s77
  have s75 : leavesOK ctxLitU 167756250000 0 ((leaves.drop 31550).take 50) 168168750000 0 = true :=
    take_step (n := 2) (t := 50) (b := 31552) rfl rfl ArealUCore.ArealUK.chunk_15775 s76
  have s74 : leavesOK ctxLitU 167743750000 0 ((leaves.drop 31548).take 52) 168168750000 0 = true :=
    take_step (n := 2) (t := 52) (b := 31550) rfl rfl ArealUCore.ArealUK.chunk_15774 s75
  have s73 : leavesOK ctxLitU 167731250000 0 ((leaves.drop 31546).take 54) 168168750000 0 = true :=
    take_step (n := 2) (t := 54) (b := 31548) rfl rfl ArealUCore.ArealUK.chunk_15773 s74
  have s72 : leavesOK ctxLitU 167712500000 0 ((leaves.drop 31544).take 56) 168168750000 0 = true :=
    take_step (n := 2) (t := 56) (b := 31546) rfl rfl ArealUCore.ArealUK.chunk_15772 s73
  have s71 : leavesOK ctxLitU 335400000000 1 ((leaves.drop 31542).take 58) 168168750000 0 = true :=
    take_step (n := 2) (t := 58) (b := 31544) rfl rfl ArealUCore.ArealUK.chunk_15771 s72
  have s70 : leavesOK ctxLitU 167675000000 0 ((leaves.drop 31540).take 60) 168168750000 0 = true :=
    take_step (n := 2) (t := 60) (b := 31542) rfl rfl ArealUCore.ArealUK.chunk_15770 s71
  have s69 : leavesOK ctxLitU 167662500000 0 ((leaves.drop 31538).take 62) 168168750000 0 = true :=
    take_step (n := 2) (t := 62) (b := 31540) rfl rfl ArealUCore.ArealUK.chunk_15769 s70
  have s68 : leavesOK ctxLitU 167650000000 0 ((leaves.drop 31536).take 64) 168168750000 0 = true :=
    take_step (n := 2) (t := 64) (b := 31538) rfl rfl ArealUCore.ArealUK.chunk_15768 s69
  have s67 : leavesOK ctxLitU 167637500000 0 ((leaves.drop 31534).take 66) 168168750000 0 = true :=
    take_step (n := 2) (t := 66) (b := 31536) rfl rfl ArealUCore.ArealUK.chunk_15767 s68
  have s66 : leavesOK ctxLitU 167625000000 0 ((leaves.drop 31532).take 68) 168168750000 0 = true :=
    take_step (n := 2) (t := 68) (b := 31534) rfl rfl ArealUCore.ArealUK.chunk_15766 s67
  have s65 : leavesOK ctxLitU 167600000000 0 ((leaves.drop 31530).take 70) 168168750000 0 = true :=
    take_step (n := 2) (t := 70) (b := 31532) rfl rfl ArealUCore.ArealUK.chunk_15765 s66
  have s64 : leavesOK ctxLitU 167587500000 0 ((leaves.drop 31528).take 72) 168168750000 0 = true :=
    take_step (n := 2) (t := 72) (b := 31530) rfl rfl ArealUCore.ArealUK.chunk_15764 s65
  have s63 : leavesOK ctxLitU 167575000000 0 ((leaves.drop 31526).take 74) 168168750000 0 = true :=
    take_step (n := 2) (t := 74) (b := 31528) rfl rfl ArealUCore.ArealUK.chunk_15763 s64
  have s62 : leavesOK ctxLitU 167562500000 0 ((leaves.drop 31524).take 76) 168168750000 0 = true :=
    take_step (n := 2) (t := 76) (b := 31526) rfl rfl ArealUCore.ArealUK.chunk_15762 s63
  have s61 : leavesOK ctxLitU 167550000000 0 ((leaves.drop 31522).take 78) 168168750000 0 = true :=
    take_step (n := 2) (t := 78) (b := 31524) rfl rfl ArealUCore.ArealUK.chunk_15761 s62
  have s60 : leavesOK ctxLitU 167537500000 0 ((leaves.drop 31520).take 80) 168168750000 0 = true :=
    take_step (n := 2) (t := 80) (b := 31522) rfl rfl ArealUCore.ArealUK.chunk_15760 s61
  have s59 : leavesOK ctxLitU 167525000000 0 ((leaves.drop 31518).take 82) 168168750000 0 = true :=
    take_step (n := 2) (t := 82) (b := 31520) rfl rfl ArealUCore.ArealUK.chunk_15759 s60
  have s58 : leavesOK ctxLitU 335012500000 1 ((leaves.drop 31516).take 84) 168168750000 0 = true :=
    take_step (n := 2) (t := 84) (b := 31518) rfl rfl ArealUCore.ArealUK.chunk_15758 s59
  have s57 : leavesOK ctxLitU 167487500000 0 ((leaves.drop 31514).take 86) 168168750000 0 = true :=
    take_step (n := 2) (t := 86) (b := 31516) rfl rfl ArealUCore.ArealUK.chunk_15757 s58
  have s56 : leavesOK ctxLitU 167468750000 0 ((leaves.drop 31512).take 88) 168168750000 0 = true :=
    take_step (n := 2) (t := 88) (b := 31514) rfl rfl ArealUCore.ArealUK.chunk_15756 s57
  have s55 : leavesOK ctxLitU 167456250000 0 ((leaves.drop 31510).take 90) 168168750000 0 = true :=
    take_step (n := 2) (t := 90) (b := 31512) rfl rfl ArealUCore.ArealUK.chunk_15755 s56
  have s54 : leavesOK ctxLitU 167443750000 0 ((leaves.drop 31508).take 92) 168168750000 0 = true :=
    take_step (n := 2) (t := 92) (b := 31510) rfl rfl ArealUCore.ArealUK.chunk_15754 s55
  have s53 : leavesOK ctxLitU 167431250000 0 ((leaves.drop 31506).take 94) 168168750000 0 = true :=
    take_step (n := 2) (t := 94) (b := 31508) rfl rfl ArealUCore.ArealUK.chunk_15753 s54
  have s52 : leavesOK ctxLitU 167412500000 0 ((leaves.drop 31504).take 96) 168168750000 0 = true :=
    take_step (n := 2) (t := 96) (b := 31506) rfl rfl ArealUCore.ArealUK.chunk_15752 s53
  have s51 : leavesOK ctxLitU 167393750000 0 ((leaves.drop 31502).take 98) 168168750000 0 = true :=
    take_step (n := 2) (t := 98) (b := 31504) rfl rfl ArealUCore.ArealUK.chunk_15751 s52
  have s50 : leavesOK ctxLitU 167381250000 0 ((leaves.drop 31500).take 100) 168168750000 0 = true :=
    take_step (n := 2) (t := 100) (b := 31502) rfl rfl ArealUCore.ArealUK.chunk_15750 s51
  have s49 : leavesOK ctxLitU 167368750000 0 ((leaves.drop 31498).take 102) 168168750000 0 = true :=
    take_step (n := 2) (t := 102) (b := 31500) rfl rfl ArealUCore.ArealUK.chunk_15749 s50
  have s48 : leavesOK ctxLitU 167356250000 0 ((leaves.drop 31496).take 104) 168168750000 0 = true :=
    take_step (n := 2) (t := 104) (b := 31498) rfl rfl ArealUCore.ArealUK.chunk_15748 s49
  have s47 : leavesOK ctxLitU 167343750000 0 ((leaves.drop 31494).take 106) 168168750000 0 = true :=
    take_step (n := 2) (t := 106) (b := 31496) rfl rfl ArealUCore.ArealUK.chunk_15747 s48
  have s46 : leavesOK ctxLitU 167331250000 0 ((leaves.drop 31492).take 108) 168168750000 0 = true :=
    take_step (n := 2) (t := 108) (b := 31494) rfl rfl ArealUCore.ArealUK.chunk_15746 s47
  have s45 : leavesOK ctxLitU 167312500000 0 ((leaves.drop 31490).take 110) 168168750000 0 = true :=
    take_step (n := 2) (t := 110) (b := 31492) rfl rfl ArealUCore.ArealUK.chunk_15745 s46
  have s44 : leavesOK ctxLitU 334587500000 1 ((leaves.drop 31488).take 112) 168168750000 0 = true :=
    take_step (n := 2) (t := 112) (b := 31490) rfl rfl ArealUCore.ArealUK.chunk_15744 s45
  have s43 : leavesOK ctxLitU 334562500000 1 ((leaves.drop 31486).take 114) 168168750000 0 = true :=
    take_step (n := 2) (t := 114) (b := 31488) rfl rfl ArealUCore.ArealUK.chunk_15743 s44
  have s42 : leavesOK ctxLitU 167268750000 0 ((leaves.drop 31484).take 116) 168168750000 0 = true :=
    take_step (n := 2) (t := 116) (b := 31486) rfl rfl ArealUCore.ArealUK.chunk_15742 s43
  have s41 : leavesOK ctxLitU 167256250000 0 ((leaves.drop 31482).take 118) 168168750000 0 = true :=
    take_step (n := 2) (t := 118) (b := 31484) rfl rfl ArealUCore.ArealUK.chunk_15741 s42
  have s40 : leavesOK ctxLitU 167243750000 0 ((leaves.drop 31480).take 120) 168168750000 0 = true :=
    take_step (n := 2) (t := 120) (b := 31482) rfl rfl ArealUCore.ArealUK.chunk_15740 s41
  have s39 : leavesOK ctxLitU 167231250000 0 ((leaves.drop 31478).take 122) 168168750000 0 = true :=
    take_step (n := 2) (t := 122) (b := 31480) rfl rfl ArealUCore.ArealUK.chunk_15739 s40
  have s38 : leavesOK ctxLitU 167212500000 0 ((leaves.drop 31476).take 124) 168168750000 0 = true :=
    take_step (n := 2) (t := 124) (b := 31478) rfl rfl ArealUCore.ArealUK.chunk_15738 s39
  have s37 : leavesOK ctxLitU 167193750000 0 ((leaves.drop 31474).take 126) 168168750000 0 = true :=
    take_step (n := 2) (t := 126) (b := 31476) rfl rfl ArealUCore.ArealUK.chunk_15737 s38
  have s36 : leavesOK ctxLitU 167181250000 0 ((leaves.drop 31472).take 128) 168168750000 0 = true :=
    take_step (n := 2) (t := 128) (b := 31474) rfl rfl ArealUCore.ArealUK.chunk_15736 s37
  have s35 : leavesOK ctxLitU 167168750000 0 ((leaves.drop 31470).take 130) 168168750000 0 = true :=
    take_step (n := 2) (t := 130) (b := 31472) rfl rfl ArealUCore.ArealUK.chunk_15735 s36
  have s34 : leavesOK ctxLitU 167156250000 0 ((leaves.drop 31468).take 132) 168168750000 0 = true :=
    take_step (n := 2) (t := 132) (b := 31470) rfl rfl ArealUCore.ArealUK.chunk_15734 s35
  have s33 : leavesOK ctxLitU 167143750000 0 ((leaves.drop 31466).take 134) 168168750000 0 = true :=
    take_step (n := 2) (t := 134) (b := 31468) rfl rfl ArealUCore.ArealUK.chunk_15733 s34
  have s32 : leavesOK ctxLitU 167131250000 0 ((leaves.drop 31464).take 136) 168168750000 0 = true :=
    take_step (n := 2) (t := 136) (b := 31466) rfl rfl ArealUCore.ArealUK.chunk_15732 s33
  have s31 : leavesOK ctxLitU 167112500000 0 ((leaves.drop 31462).take 138) 168168750000 0 = true :=
    take_step (n := 2) (t := 138) (b := 31464) rfl rfl ArealUCore.ArealUK.chunk_15731 s32
  have s30 : leavesOK ctxLitU 167087500000 0 ((leaves.drop 31460).take 140) 168168750000 0 = true :=
    take_step (n := 2) (t := 140) (b := 31462) rfl rfl ArealUCore.ArealUK.chunk_15730 s31
  have s29 : leavesOK ctxLitU 167068750000 0 ((leaves.drop 31458).take 142) 168168750000 0 = true :=
    take_step (n := 2) (t := 142) (b := 31460) rfl rfl ArealUCore.ArealUK.chunk_15729 s30
  have s28 : leavesOK ctxLitU 167056250000 0 ((leaves.drop 31456).take 144) 168168750000 0 = true :=
    take_step (n := 2) (t := 144) (b := 31458) rfl rfl ArealUCore.ArealUK.chunk_15728 s29
  have s27 : leavesOK ctxLitU 167043750000 0 ((leaves.drop 31454).take 146) 168168750000 0 = true :=
    take_step (n := 2) (t := 146) (b := 31456) rfl rfl ArealUCore.ArealUK.chunk_15727 s28
  have s26 : leavesOK ctxLitU 167031250000 0 ((leaves.drop 31452).take 148) 168168750000 0 = true :=
    take_step (n := 2) (t := 148) (b := 31454) rfl rfl ArealUCore.ArealUK.chunk_15726 s27
  have s25 : leavesOK ctxLitU 167018750000 0 ((leaves.drop 31450).take 150) 168168750000 0 = true :=
    take_step (n := 2) (t := 150) (b := 31452) rfl rfl ArealUCore.ArealUK.chunk_15725 s26
  have s24 : leavesOK ctxLitU 167006250000 0 ((leaves.drop 31448).take 152) 168168750000 0 = true :=
    take_step (n := 2) (t := 152) (b := 31450) rfl rfl ArealUCore.ArealUK.chunk_15724 s25
  have s23 : leavesOK ctxLitU 166987500000 0 ((leaves.drop 31446).take 154) 168168750000 0 = true :=
    take_step (n := 2) (t := 154) (b := 31448) rfl rfl ArealUCore.ArealUK.chunk_15723 s24
  have s22 : leavesOK ctxLitU 166968750000 0 ((leaves.drop 31444).take 156) 168168750000 0 = true :=
    take_step (n := 2) (t := 156) (b := 31446) rfl rfl ArealUCore.ArealUK.chunk_15722 s23
  have s21 : leavesOK ctxLitU 166956250000 0 ((leaves.drop 31442).take 158) 168168750000 0 = true :=
    take_step (n := 2) (t := 158) (b := 31444) rfl rfl ArealUCore.ArealUK.chunk_15721 s22
  have s20 : leavesOK ctxLitU 166943750000 0 ((leaves.drop 31440).take 160) 168168750000 0 = true :=
    take_step (n := 2) (t := 160) (b := 31442) rfl rfl ArealUCore.ArealUK.chunk_15720 s21
  have s19 : leavesOK ctxLitU 166931250000 0 ((leaves.drop 31438).take 162) 168168750000 0 = true :=
    take_step (n := 2) (t := 162) (b := 31440) rfl rfl ArealUCore.ArealUK.chunk_15719 s20
  have s18 : leavesOK ctxLitU 166912500000 0 ((leaves.drop 31436).take 164) 168168750000 0 = true :=
    take_step (n := 2) (t := 164) (b := 31438) rfl rfl ArealUCore.ArealUK.chunk_15718 s19
  have s17 : leavesOK ctxLitU 333787500000 1 ((leaves.drop 31434).take 166) 168168750000 0 = true :=
    take_step (n := 2) (t := 166) (b := 31436) rfl rfl ArealUCore.ArealUK.chunk_15717 s18
  have s16 : leavesOK ctxLitU 333762500000 1 ((leaves.drop 31432).take 168) 168168750000 0 = true :=
    take_step (n := 2) (t := 168) (b := 31434) rfl rfl ArealUCore.ArealUK.chunk_15716 s17
  have s15 : leavesOK ctxLitU 166868750000 0 ((leaves.drop 31430).take 170) 168168750000 0 = true :=
    take_step (n := 2) (t := 170) (b := 31432) rfl rfl ArealUCore.ArealUK.chunk_15715 s16
  have s14 : leavesOK ctxLitU 166856250000 0 ((leaves.drop 31428).take 172) 168168750000 0 = true :=
    take_step (n := 2) (t := 172) (b := 31430) rfl rfl ArealUCore.ArealUK.chunk_15714 s15
  have s13 : leavesOK ctxLitU 166843750000 0 ((leaves.drop 31426).take 174) 168168750000 0 = true :=
    take_step (n := 2) (t := 174) (b := 31428) rfl rfl ArealUCore.ArealUK.chunk_15713 s14
  have s12 : leavesOK ctxLitU 166831250000 0 ((leaves.drop 31424).take 176) 168168750000 0 = true :=
    take_step (n := 2) (t := 176) (b := 31426) rfl rfl ArealUCore.ArealUK.chunk_15712 s13
  have s11 : leavesOK ctxLitU 166818750000 0 ((leaves.drop 31422).take 178) 168168750000 0 = true :=
    take_step (n := 2) (t := 178) (b := 31424) rfl rfl ArealUCore.ArealUK.chunk_15711 s12
  have s10 : leavesOK ctxLitU 166806250000 0 ((leaves.drop 31420).take 180) 168168750000 0 = true :=
    take_step (n := 2) (t := 180) (b := 31422) rfl rfl ArealUCore.ArealUK.chunk_15710 s11
  have s9 : leavesOK ctxLitU 166793750000 0 ((leaves.drop 31418).take 182) 168168750000 0 = true :=
    take_step (n := 2) (t := 182) (b := 31420) rfl rfl ArealUCore.ArealUK.chunk_15709 s10
  have s8 : leavesOK ctxLitU 166781250000 0 ((leaves.drop 31416).take 184) 168168750000 0 = true :=
    take_step (n := 2) (t := 184) (b := 31418) rfl rfl ArealUCore.ArealUK.chunk_15708 s9
  have s7 : leavesOK ctxLitU 166768750000 0 ((leaves.drop 31414).take 186) 168168750000 0 = true :=
    take_step (n := 2) (t := 186) (b := 31416) rfl rfl ArealUCore.ArealUK.chunk_15707 s8
  have s6 : leavesOK ctxLitU 166756250000 0 ((leaves.drop 31412).take 188) 168168750000 0 = true :=
    take_step (n := 2) (t := 188) (b := 31414) rfl rfl ArealUCore.ArealUK.chunk_15706 s7
  have s5 : leavesOK ctxLitU 166743750000 0 ((leaves.drop 31410).take 190) 168168750000 0 = true :=
    take_step (n := 2) (t := 190) (b := 31412) rfl rfl ArealUCore.ArealUK.chunk_15705 s6
  have s4 : leavesOK ctxLitU 166731250000 0 ((leaves.drop 31408).take 192) 168168750000 0 = true :=
    take_step (n := 2) (t := 192) (b := 31410) rfl rfl ArealUCore.ArealUK.chunk_15704 s5
  have s3 : leavesOK ctxLitU 166712500000 0 ((leaves.drop 31406).take 194) 168168750000 0 = true :=
    take_step (n := 2) (t := 194) (b := 31408) rfl rfl ArealUCore.ArealUK.chunk_15703 s4
  have s2 : leavesOK ctxLitU 333387500000 1 ((leaves.drop 31404).take 196) 168168750000 0 = true :=
    take_step (n := 2) (t := 196) (b := 31406) rfl rfl ArealUCore.ArealUK.chunk_15702 s3
  have s1 : leavesOK ctxLitU 333362500000 1 ((leaves.drop 31402).take 198) 168168750000 0 = true :=
    take_step (n := 2) (t := 198) (b := 31404) rfl rfl ArealUCore.ArealUK.chunk_15701 s2
  have s0 : leavesOK ctxLitU 166668750000 0 ((leaves.drop 31400).take 200) 168168750000 0 = true :=
    take_step (n := 2) (t := 200) (b := 31402) rfl rfl ArealUCore.ArealUK.chunk_15700 s1
  exact s0

end Areal.UCert

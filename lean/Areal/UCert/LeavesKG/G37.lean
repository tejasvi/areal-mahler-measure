import ArealUK.Chunk3700
import ArealUK.Chunk3701
import ArealUK.Chunk3702
import ArealUK.Chunk3703
import ArealUK.Chunk3704
import ArealUK.Chunk3705
import ArealUK.Chunk3706
import ArealUK.Chunk3707
import ArealUK.Chunk3708
import ArealUK.Chunk3709
import ArealUK.Chunk3710
import ArealUK.Chunk3711
import ArealUK.Chunk3712
import ArealUK.Chunk3713
import ArealUK.Chunk3714
import ArealUK.Chunk3715
import ArealUK.Chunk3716
import ArealUK.Chunk3717
import ArealUK.Chunk3718
import ArealUK.Chunk3719
import ArealUK.Chunk3720
import ArealUK.Chunk3721
import ArealUK.Chunk3722
import ArealUK.Chunk3723
import ArealUK.Chunk3724
import ArealUK.Chunk3725
import ArealUK.Chunk3726
import ArealUK.Chunk3727
import ArealUK.Chunk3728
import ArealUK.Chunk3729
import ArealUK.Chunk3730
import ArealUK.Chunk3731
import ArealUK.Chunk3732
import ArealUK.Chunk3733
import ArealUK.Chunk3734
import ArealUK.Chunk3735
import ArealUK.Chunk3736
import ArealUK.Chunk3737
import ArealUK.Chunk3738
import ArealUK.Chunk3739
import ArealUK.Chunk3740
import ArealUK.Chunk3741
import ArealUK.Chunk3742
import ArealUK.Chunk3743
import ArealUK.Chunk3744
import ArealUK.Chunk3745
import ArealUK.Chunk3746
import ArealUK.Chunk3747
import ArealUK.Chunk3748
import ArealUK.Chunk3749
import ArealUK.Chunk3750
import ArealUK.Chunk3751
import ArealUK.Chunk3752
import ArealUK.Chunk3753
import ArealUK.Chunk3754
import ArealUK.Chunk3755
import ArealUK.Chunk3756
import ArealUK.Chunk3757
import ArealUK.Chunk3758
import ArealUK.Chunk3759
import ArealUK.Chunk3760
import ArealUK.Chunk3761
import ArealUK.Chunk3762
import ArealUK.Chunk3763
import ArealUK.Chunk3764
import ArealUK.Chunk3765
import ArealUK.Chunk3766
import ArealUK.Chunk3767
import ArealUK.Chunk3768
import ArealUK.Chunk3769
import ArealUK.Chunk3770
import ArealUK.Chunk3771
import ArealUK.Chunk3772
import ArealUK.Chunk3773
import ArealUK.Chunk3774
import ArealUK.Chunk3775
import ArealUK.Chunk3776
import ArealUK.Chunk3777
import ArealUK.Chunk3778
import ArealUK.Chunk3779
import ArealUK.Chunk3780
import ArealUK.Chunk3781
import ArealUK.Chunk3782
import ArealUK.Chunk3783
import ArealUK.Chunk3784
import ArealUK.Chunk3785
import ArealUK.Chunk3786
import ArealUK.Chunk3787
import ArealUK.Chunk3788
import ArealUK.Chunk3789
import ArealUK.Chunk3790
import ArealUK.Chunk3791
import ArealUK.Chunk3792
import ArealUK.Chunk3793
import ArealUK.Chunk3794
import ArealUK.Chunk3795
import ArealUK.Chunk3796
import ArealUK.Chunk3797
import ArealUK.Chunk3798
import ArealUK.Chunk3799
import Areal.UCert.LeavesKGen

/-! Group 37 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_37 : leavesOK ctxLitU 334900000000 4 ((leaves.drop 7400).take 200) 85093750000 2 = true := by
  have s99 := ArealUCore.ArealUK.chunk_3799
  have s98 : leavesOK ctxLitU 85068750000 2 ((leaves.drop 7596).take 4) 85093750000 2 = true :=
    take_step (n := 2) (t := 4) (b := 7598) rfl rfl ArealUCore.ArealUK.chunk_3798 s99
  have s97 : leavesOK ctxLitU 85056250000 2 ((leaves.drop 7594).take 6) 85093750000 2 = true :=
    take_step (n := 2) (t := 6) (b := 7596) rfl rfl ArealUCore.ArealUK.chunk_3797 s98
  have s96 : leavesOK ctxLitU 85043750000 2 ((leaves.drop 7592).take 8) 85093750000 2 = true :=
    take_step (n := 2) (t := 8) (b := 7594) rfl rfl ArealUCore.ArealUK.chunk_3796 s97
  have s95 : leavesOK ctxLitU 85031250000 2 ((leaves.drop 7590).take 10) 85093750000 2 = true :=
    take_step (n := 2) (t := 10) (b := 7592) rfl rfl ArealUCore.ArealUK.chunk_3795 s96
  have s94 : leavesOK ctxLitU 85018750000 2 ((leaves.drop 7588).take 12) 85093750000 2 = true :=
    take_step (n := 2) (t := 12) (b := 7590) rfl rfl ArealUCore.ArealUK.chunk_3794 s95
  have s93 : leavesOK ctxLitU 85006250000 2 ((leaves.drop 7586).take 14) 85093750000 2 = true :=
    take_step (n := 2) (t := 14) (b := 7588) rfl rfl ArealUCore.ArealUK.chunk_3793 s94
  have s92 : leavesOK ctxLitU 169987500000 3 ((leaves.drop 7584).take 16) 85093750000 2 = true :=
    take_step (n := 2) (t := 16) (b := 7586) rfl rfl ArealUCore.ArealUK.chunk_3792 s93
  have s91 : leavesOK ctxLitU 169962500000 3 ((leaves.drop 7582).take 18) 85093750000 2 = true :=
    take_step (n := 2) (t := 18) (b := 7584) rfl rfl ArealUCore.ArealUK.chunk_3791 s92
  have s90 : leavesOK ctxLitU 169937500000 3 ((leaves.drop 7580).take 20) 85093750000 2 = true :=
    take_step (n := 2) (t := 20) (b := 7582) rfl rfl ArealUCore.ArealUK.chunk_3790 s91
  have s89 : leavesOK ctxLitU 169912500000 3 ((leaves.drop 7578).take 22) 85093750000 2 = true :=
    take_step (n := 2) (t := 22) (b := 7580) rfl rfl ArealUCore.ArealUK.chunk_3789 s90
  have s88 : leavesOK ctxLitU 169887500000 3 ((leaves.drop 7576).take 24) 85093750000 2 = true :=
    take_step (n := 2) (t := 24) (b := 7578) rfl rfl ArealUCore.ArealUK.chunk_3788 s89
  have s87 : leavesOK ctxLitU 169862500000 3 ((leaves.drop 7574).take 26) 85093750000 2 = true :=
    take_step (n := 2) (t := 26) (b := 7576) rfl rfl ArealUCore.ArealUK.chunk_3787 s88
  have s86 : leavesOK ctxLitU 84912500000 2 ((leaves.drop 7572).take 28) 85093750000 2 = true :=
    take_step (n := 2) (t := 28) (b := 7574) rfl rfl ArealUCore.ArealUK.chunk_3786 s87
  have s85 : leavesOK ctxLitU 169775000000 3 ((leaves.drop 7570).take 30) 85093750000 2 = true :=
    take_step (n := 2) (t := 30) (b := 7572) rfl rfl ArealUCore.ArealUK.chunk_3785 s86
  have s84 : leavesOK ctxLitU 339475000000 4 ((leaves.drop 7568).take 32) 85093750000 2 = true :=
    take_step (n := 2) (t := 32) (b := 7570) rfl rfl ArealUCore.ArealUK.chunk_3784 s85
  have s83 : leavesOK ctxLitU 339425000000 4 ((leaves.drop 7566).take 34) 85093750000 2 = true :=
    take_step (n := 2) (t := 34) (b := 7568) rfl rfl ArealUCore.ArealUK.chunk_3783 s84
  have s82 : leavesOK ctxLitU 339375000000 4 ((leaves.drop 7564).take 36) 85093750000 2 = true :=
    take_step (n := 2) (t := 36) (b := 7566) rfl rfl ArealUCore.ArealUK.chunk_3782 s83
  have s81 : leavesOK ctxLitU 339325000000 4 ((leaves.drop 7562).take 38) 85093750000 2 = true :=
    take_step (n := 2) (t := 38) (b := 7564) rfl rfl ArealUCore.ArealUK.chunk_3781 s82
  have s80 : leavesOK ctxLitU 339275000000 4 ((leaves.drop 7560).take 40) 85093750000 2 = true :=
    take_step (n := 2) (t := 40) (b := 7562) rfl rfl ArealUCore.ArealUK.chunk_3780 s81
  have s79 : leavesOK ctxLitU 339225000000 4 ((leaves.drop 7558).take 42) 85093750000 2 = true :=
    take_step (n := 2) (t := 42) (b := 7560) rfl rfl ArealUCore.ArealUK.chunk_3779 s80
  have s78 : leavesOK ctxLitU 339175000000 4 ((leaves.drop 7556).take 44) 85093750000 2 = true :=
    take_step (n := 2) (t := 44) (b := 7558) rfl rfl ArealUCore.ArealUK.chunk_3778 s79
  have s77 : leavesOK ctxLitU 339125000000 4 ((leaves.drop 7554).take 46) 85093750000 2 = true :=
    take_step (n := 2) (t := 46) (b := 7556) rfl rfl ArealUCore.ArealUK.chunk_3777 s78
  have s76 : leavesOK ctxLitU 339075000000 4 ((leaves.drop 7552).take 48) 85093750000 2 = true :=
    take_step (n := 2) (t := 48) (b := 7554) rfl rfl ArealUCore.ArealUK.chunk_3776 s77
  have s75 : leavesOK ctxLitU 339025000000 4 ((leaves.drop 7550).take 50) 85093750000 2 = true :=
    take_step (n := 2) (t := 50) (b := 7552) rfl rfl ArealUCore.ArealUK.chunk_3775 s76
  have s74 : leavesOK ctxLitU 338975000000 4 ((leaves.drop 7548).take 52) 85093750000 2 = true :=
    take_step (n := 2) (t := 52) (b := 7550) rfl rfl ArealUCore.ArealUK.chunk_3774 s75
  have s73 : leavesOK ctxLitU 338925000000 4 ((leaves.drop 7546).take 54) 85093750000 2 = true :=
    take_step (n := 2) (t := 54) (b := 7548) rfl rfl ArealUCore.ArealUK.chunk_3773 s74
  have s72 : leavesOK ctxLitU 338875000000 4 ((leaves.drop 7544).take 56) 85093750000 2 = true :=
    take_step (n := 2) (t := 56) (b := 7546) rfl rfl ArealUCore.ArealUK.chunk_3772 s73
  have s71 : leavesOK ctxLitU 338825000000 4 ((leaves.drop 7542).take 58) 85093750000 2 = true :=
    take_step (n := 2) (t := 58) (b := 7544) rfl rfl ArealUCore.ArealUK.chunk_3771 s72
  have s70 : leavesOK ctxLitU 338775000000 4 ((leaves.drop 7540).take 60) 85093750000 2 = true :=
    take_step (n := 2) (t := 60) (b := 7542) rfl rfl ArealUCore.ArealUK.chunk_3770 s71
  have s69 : leavesOK ctxLitU 338725000000 4 ((leaves.drop 7538).take 62) 85093750000 2 = true :=
    take_step (n := 2) (t := 62) (b := 7540) rfl rfl ArealUCore.ArealUK.chunk_3769 s70
  have s68 : leavesOK ctxLitU 338675000000 4 ((leaves.drop 7536).take 64) 85093750000 2 = true :=
    take_step (n := 2) (t := 64) (b := 7538) rfl rfl ArealUCore.ArealUK.chunk_3768 s69
  have s67 : leavesOK ctxLitU 338625000000 4 ((leaves.drop 7534).take 66) 85093750000 2 = true :=
    take_step (n := 2) (t := 66) (b := 7536) rfl rfl ArealUCore.ArealUK.chunk_3767 s68
  have s66 : leavesOK ctxLitU 338575000000 4 ((leaves.drop 7532).take 68) 85093750000 2 = true :=
    take_step (n := 2) (t := 68) (b := 7534) rfl rfl ArealUCore.ArealUK.chunk_3766 s67
  have s65 : leavesOK ctxLitU 338525000000 4 ((leaves.drop 7530).take 70) 85093750000 2 = true :=
    take_step (n := 2) (t := 70) (b := 7532) rfl rfl ArealUCore.ArealUK.chunk_3765 s66
  have s64 : leavesOK ctxLitU 338475000000 4 ((leaves.drop 7528).take 72) 85093750000 2 = true :=
    take_step (n := 2) (t := 72) (b := 7530) rfl rfl ArealUCore.ArealUK.chunk_3764 s65
  have s63 : leavesOK ctxLitU 338425000000 4 ((leaves.drop 7526).take 74) 85093750000 2 = true :=
    take_step (n := 2) (t := 74) (b := 7528) rfl rfl ArealUCore.ArealUK.chunk_3763 s64
  have s62 : leavesOK ctxLitU 338375000000 4 ((leaves.drop 7524).take 76) 85093750000 2 = true :=
    take_step (n := 2) (t := 76) (b := 7526) rfl rfl ArealUCore.ArealUK.chunk_3762 s63
  have s61 : leavesOK ctxLitU 338325000000 4 ((leaves.drop 7522).take 78) 85093750000 2 = true :=
    take_step (n := 2) (t := 78) (b := 7524) rfl rfl ArealUCore.ArealUK.chunk_3761 s62
  have s60 : leavesOK ctxLitU 338275000000 4 ((leaves.drop 7520).take 80) 85093750000 2 = true :=
    take_step (n := 2) (t := 80) (b := 7522) rfl rfl ArealUCore.ArealUK.chunk_3760 s61
  have s59 : leavesOK ctxLitU 338225000000 4 ((leaves.drop 7518).take 82) 85093750000 2 = true :=
    take_step (n := 2) (t := 82) (b := 7520) rfl rfl ArealUCore.ArealUK.chunk_3759 s60
  have s58 : leavesOK ctxLitU 338175000000 4 ((leaves.drop 7516).take 84) 85093750000 2 = true :=
    take_step (n := 2) (t := 84) (b := 7518) rfl rfl ArealUCore.ArealUK.chunk_3758 s59
  have s57 : leavesOK ctxLitU 338125000000 4 ((leaves.drop 7514).take 86) 85093750000 2 = true :=
    take_step (n := 2) (t := 86) (b := 7516) rfl rfl ArealUCore.ArealUK.chunk_3757 s58
  have s56 : leavesOK ctxLitU 338075000000 4 ((leaves.drop 7512).take 88) 85093750000 2 = true :=
    take_step (n := 2) (t := 88) (b := 7514) rfl rfl ArealUCore.ArealUK.chunk_3756 s57
  have s55 : leavesOK ctxLitU 338025000000 4 ((leaves.drop 7510).take 90) 85093750000 2 = true :=
    take_step (n := 2) (t := 90) (b := 7512) rfl rfl ArealUCore.ArealUK.chunk_3755 s56
  have s54 : leavesOK ctxLitU 337975000000 4 ((leaves.drop 7508).take 92) 85093750000 2 = true :=
    take_step (n := 2) (t := 92) (b := 7510) rfl rfl ArealUCore.ArealUK.chunk_3754 s55
  have s53 : leavesOK ctxLitU 337925000000 4 ((leaves.drop 7506).take 94) 85093750000 2 = true :=
    take_step (n := 2) (t := 94) (b := 7508) rfl rfl ArealUCore.ArealUK.chunk_3753 s54
  have s52 : leavesOK ctxLitU 337875000000 4 ((leaves.drop 7504).take 96) 85093750000 2 = true :=
    take_step (n := 2) (t := 96) (b := 7506) rfl rfl ArealUCore.ArealUK.chunk_3752 s53
  have s51 : leavesOK ctxLitU 337825000000 4 ((leaves.drop 7502).take 98) 85093750000 2 = true :=
    take_step (n := 2) (t := 98) (b := 7504) rfl rfl ArealUCore.ArealUK.chunk_3751 s52
  have s50 : leavesOK ctxLitU 337775000000 4 ((leaves.drop 7500).take 100) 85093750000 2 = true :=
    take_step (n := 2) (t := 100) (b := 7502) rfl rfl ArealUCore.ArealUK.chunk_3750 s51
  have s49 : leavesOK ctxLitU 337725000000 4 ((leaves.drop 7498).take 102) 85093750000 2 = true :=
    take_step (n := 2) (t := 102) (b := 7500) rfl rfl ArealUCore.ArealUK.chunk_3749 s50
  have s48 : leavesOK ctxLitU 337675000000 4 ((leaves.drop 7496).take 104) 85093750000 2 = true :=
    take_step (n := 2) (t := 104) (b := 7498) rfl rfl ArealUCore.ArealUK.chunk_3748 s49
  have s47 : leavesOK ctxLitU 337625000000 4 ((leaves.drop 7494).take 106) 85093750000 2 = true :=
    take_step (n := 2) (t := 106) (b := 7496) rfl rfl ArealUCore.ArealUK.chunk_3747 s48
  have s46 : leavesOK ctxLitU 337575000000 4 ((leaves.drop 7492).take 108) 85093750000 2 = true :=
    take_step (n := 2) (t := 108) (b := 7494) rfl rfl ArealUCore.ArealUK.chunk_3746 s47
  have s45 : leavesOK ctxLitU 337525000000 4 ((leaves.drop 7490).take 110) 85093750000 2 = true :=
    take_step (n := 2) (t := 110) (b := 7492) rfl rfl ArealUCore.ArealUK.chunk_3745 s46
  have s44 : leavesOK ctxLitU 337475000000 4 ((leaves.drop 7488).take 112) 85093750000 2 = true :=
    take_step (n := 2) (t := 112) (b := 7490) rfl rfl ArealUCore.ArealUK.chunk_3744 s45
  have s43 : leavesOK ctxLitU 337425000000 4 ((leaves.drop 7486).take 114) 85093750000 2 = true :=
    take_step (n := 2) (t := 114) (b := 7488) rfl rfl ArealUCore.ArealUK.chunk_3743 s44
  have s42 : leavesOK ctxLitU 337375000000 4 ((leaves.drop 7484).take 116) 85093750000 2 = true :=
    take_step (n := 2) (t := 116) (b := 7486) rfl rfl ArealUCore.ArealUK.chunk_3742 s43
  have s41 : leavesOK ctxLitU 337325000000 4 ((leaves.drop 7482).take 118) 85093750000 2 = true :=
    take_step (n := 2) (t := 118) (b := 7484) rfl rfl ArealUCore.ArealUK.chunk_3741 s42
  have s40 : leavesOK ctxLitU 337275000000 4 ((leaves.drop 7480).take 120) 85093750000 2 = true :=
    take_step (n := 2) (t := 120) (b := 7482) rfl rfl ArealUCore.ArealUK.chunk_3740 s41
  have s39 : leavesOK ctxLitU 337225000000 4 ((leaves.drop 7478).take 122) 85093750000 2 = true :=
    take_step (n := 2) (t := 122) (b := 7480) rfl rfl ArealUCore.ArealUK.chunk_3739 s40
  have s38 : leavesOK ctxLitU 337175000000 4 ((leaves.drop 7476).take 124) 85093750000 2 = true :=
    take_step (n := 2) (t := 124) (b := 7478) rfl rfl ArealUCore.ArealUK.chunk_3738 s39
  have s37 : leavesOK ctxLitU 337125000000 4 ((leaves.drop 7474).take 126) 85093750000 2 = true :=
    take_step (n := 2) (t := 126) (b := 7476) rfl rfl ArealUCore.ArealUK.chunk_3737 s38
  have s36 : leavesOK ctxLitU 337075000000 4 ((leaves.drop 7472).take 128) 85093750000 2 = true :=
    take_step (n := 2) (t := 128) (b := 7474) rfl rfl ArealUCore.ArealUK.chunk_3736 s37
  have s35 : leavesOK ctxLitU 337025000000 4 ((leaves.drop 7470).take 130) 85093750000 2 = true :=
    take_step (n := 2) (t := 130) (b := 7472) rfl rfl ArealUCore.ArealUK.chunk_3735 s36
  have s34 : leavesOK ctxLitU 336975000000 4 ((leaves.drop 7468).take 132) 85093750000 2 = true :=
    take_step (n := 2) (t := 132) (b := 7470) rfl rfl ArealUCore.ArealUK.chunk_3734 s35
  have s33 : leavesOK ctxLitU 336925000000 4 ((leaves.drop 7466).take 134) 85093750000 2 = true :=
    take_step (n := 2) (t := 134) (b := 7468) rfl rfl ArealUCore.ArealUK.chunk_3733 s34
  have s32 : leavesOK ctxLitU 336875000000 4 ((leaves.drop 7464).take 136) 85093750000 2 = true :=
    take_step (n := 2) (t := 136) (b := 7466) rfl rfl ArealUCore.ArealUK.chunk_3732 s33
  have s31 : leavesOK ctxLitU 336825000000 4 ((leaves.drop 7462).take 138) 85093750000 2 = true :=
    take_step (n := 2) (t := 138) (b := 7464) rfl rfl ArealUCore.ArealUK.chunk_3731 s32
  have s30 : leavesOK ctxLitU 336775000000 4 ((leaves.drop 7460).take 140) 85093750000 2 = true :=
    take_step (n := 2) (t := 140) (b := 7462) rfl rfl ArealUCore.ArealUK.chunk_3730 s31
  have s29 : leavesOK ctxLitU 336725000000 4 ((leaves.drop 7458).take 142) 85093750000 2 = true :=
    take_step (n := 2) (t := 142) (b := 7460) rfl rfl ArealUCore.ArealUK.chunk_3729 s30
  have s28 : leavesOK ctxLitU 336675000000 4 ((leaves.drop 7456).take 144) 85093750000 2 = true :=
    take_step (n := 2) (t := 144) (b := 7458) rfl rfl ArealUCore.ArealUK.chunk_3728 s29
  have s27 : leavesOK ctxLitU 336625000000 4 ((leaves.drop 7454).take 146) 85093750000 2 = true :=
    take_step (n := 2) (t := 146) (b := 7456) rfl rfl ArealUCore.ArealUK.chunk_3727 s28
  have s26 : leavesOK ctxLitU 336575000000 4 ((leaves.drop 7452).take 148) 85093750000 2 = true :=
    take_step (n := 2) (t := 148) (b := 7454) rfl rfl ArealUCore.ArealUK.chunk_3726 s27
  have s25 : leavesOK ctxLitU 336525000000 4 ((leaves.drop 7450).take 150) 85093750000 2 = true :=
    take_step (n := 2) (t := 150) (b := 7452) rfl rfl ArealUCore.ArealUK.chunk_3725 s26
  have s24 : leavesOK ctxLitU 336475000000 4 ((leaves.drop 7448).take 152) 85093750000 2 = true :=
    take_step (n := 2) (t := 152) (b := 7450) rfl rfl ArealUCore.ArealUK.chunk_3724 s25
  have s23 : leavesOK ctxLitU 336425000000 4 ((leaves.drop 7446).take 154) 85093750000 2 = true :=
    take_step (n := 2) (t := 154) (b := 7448) rfl rfl ArealUCore.ArealUK.chunk_3723 s24
  have s22 : leavesOK ctxLitU 336375000000 4 ((leaves.drop 7444).take 156) 85093750000 2 = true :=
    take_step (n := 2) (t := 156) (b := 7446) rfl rfl ArealUCore.ArealUK.chunk_3722 s23
  have s21 : leavesOK ctxLitU 336325000000 4 ((leaves.drop 7442).take 158) 85093750000 2 = true :=
    take_step (n := 2) (t := 158) (b := 7444) rfl rfl ArealUCore.ArealUK.chunk_3721 s22
  have s20 : leavesOK ctxLitU 336275000000 4 ((leaves.drop 7440).take 160) 85093750000 2 = true :=
    take_step (n := 2) (t := 160) (b := 7442) rfl rfl ArealUCore.ArealUK.chunk_3720 s21
  have s19 : leavesOK ctxLitU 336225000000 4 ((leaves.drop 7438).take 162) 85093750000 2 = true :=
    take_step (n := 2) (t := 162) (b := 7440) rfl rfl ArealUCore.ArealUK.chunk_3719 s20
  have s18 : leavesOK ctxLitU 336175000000 4 ((leaves.drop 7436).take 164) 85093750000 2 = true :=
    take_step (n := 2) (t := 164) (b := 7438) rfl rfl ArealUCore.ArealUK.chunk_3718 s19
  have s17 : leavesOK ctxLitU 336125000000 4 ((leaves.drop 7434).take 166) 85093750000 2 = true :=
    take_step (n := 2) (t := 166) (b := 7436) rfl rfl ArealUCore.ArealUK.chunk_3717 s18
  have s16 : leavesOK ctxLitU 336075000000 4 ((leaves.drop 7432).take 168) 85093750000 2 = true :=
    take_step (n := 2) (t := 168) (b := 7434) rfl rfl ArealUCore.ArealUK.chunk_3716 s17
  have s15 : leavesOK ctxLitU 336025000000 4 ((leaves.drop 7430).take 170) 85093750000 2 = true :=
    take_step (n := 2) (t := 170) (b := 7432) rfl rfl ArealUCore.ArealUK.chunk_3715 s16
  have s14 : leavesOK ctxLitU 335975000000 4 ((leaves.drop 7428).take 172) 85093750000 2 = true :=
    take_step (n := 2) (t := 172) (b := 7430) rfl rfl ArealUCore.ArealUK.chunk_3714 s15
  have s13 : leavesOK ctxLitU 335925000000 4 ((leaves.drop 7426).take 174) 85093750000 2 = true :=
    take_step (n := 2) (t := 174) (b := 7428) rfl rfl ArealUCore.ArealUK.chunk_3713 s14
  have s12 : leavesOK ctxLitU 335875000000 4 ((leaves.drop 7424).take 176) 85093750000 2 = true :=
    take_step (n := 2) (t := 176) (b := 7426) rfl rfl ArealUCore.ArealUK.chunk_3712 s13
  have s11 : leavesOK ctxLitU 335825000000 4 ((leaves.drop 7422).take 178) 85093750000 2 = true :=
    take_step (n := 2) (t := 178) (b := 7424) rfl rfl ArealUCore.ArealUK.chunk_3711 s12
  have s10 : leavesOK ctxLitU 335775000000 4 ((leaves.drop 7420).take 180) 85093750000 2 = true :=
    take_step (n := 2) (t := 180) (b := 7422) rfl rfl ArealUCore.ArealUK.chunk_3710 s11
  have s9 : leavesOK ctxLitU 335725000000 4 ((leaves.drop 7418).take 182) 85093750000 2 = true :=
    take_step (n := 2) (t := 182) (b := 7420) rfl rfl ArealUCore.ArealUK.chunk_3709 s10
  have s8 : leavesOK ctxLitU 167825000000 3 ((leaves.drop 7416).take 184) 85093750000 2 = true :=
    take_step (n := 2) (t := 184) (b := 7418) rfl rfl ArealUCore.ArealUK.chunk_3708 s9
  have s7 : leavesOK ctxLitU 167775000000 3 ((leaves.drop 7414).take 186) 85093750000 2 = true :=
    take_step (n := 2) (t := 186) (b := 7416) rfl rfl ArealUCore.ArealUK.chunk_3707 s8
  have s6 : leavesOK ctxLitU 167725000000 3 ((leaves.drop 7412).take 188) 85093750000 2 = true :=
    take_step (n := 2) (t := 188) (b := 7414) rfl rfl ArealUCore.ArealUK.chunk_3706 s7
  have s5 : leavesOK ctxLitU 167675000000 3 ((leaves.drop 7410).take 190) 85093750000 2 = true :=
    take_step (n := 2) (t := 190) (b := 7412) rfl rfl ArealUCore.ArealUK.chunk_3705 s6
  have s4 : leavesOK ctxLitU 167625000000 3 ((leaves.drop 7408).take 192) 85093750000 2 = true :=
    take_step (n := 2) (t := 192) (b := 7410) rfl rfl ArealUCore.ArealUK.chunk_3704 s5
  have s3 : leavesOK ctxLitU 167575000000 3 ((leaves.drop 7406).take 194) 85093750000 2 = true :=
    take_step (n := 2) (t := 194) (b := 7408) rfl rfl ArealUCore.ArealUK.chunk_3703 s4
  have s2 : leavesOK ctxLitU 167525000000 3 ((leaves.drop 7404).take 196) 85093750000 2 = true :=
    take_step (n := 2) (t := 196) (b := 7406) rfl rfl ArealUCore.ArealUK.chunk_3702 s3
  have s1 : leavesOK ctxLitU 167475000000 3 ((leaves.drop 7402).take 198) 85093750000 2 = true :=
    take_step (n := 2) (t := 198) (b := 7404) rfl rfl ArealUCore.ArealUK.chunk_3701 s2
  have s0 : leavesOK ctxLitU 334900000000 4 ((leaves.drop 7400).take 200) 85093750000 2 = true :=
    take_step (n := 2) (t := 200) (b := 7402) rfl rfl ArealUCore.ArealUK.chunk_3700 s1
  exact s0

end Areal.UCert

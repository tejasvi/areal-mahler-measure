import ArealUK.Chunk11800
import ArealUK.Chunk11801
import ArealUK.Chunk11802
import ArealUK.Chunk11803
import ArealUK.Chunk11804
import ArealUK.Chunk11805
import ArealUK.Chunk11806
import ArealUK.Chunk11807
import ArealUK.Chunk11808
import ArealUK.Chunk11809
import ArealUK.Chunk11810
import ArealUK.Chunk11811
import ArealUK.Chunk11812
import ArealUK.Chunk11813
import ArealUK.Chunk11814
import ArealUK.Chunk11815
import ArealUK.Chunk11816
import ArealUK.Chunk11817
import ArealUK.Chunk11818
import ArealUK.Chunk11819
import ArealUK.Chunk11820
import ArealUK.Chunk11821
import ArealUK.Chunk11822
import ArealUK.Chunk11823
import ArealUK.Chunk11824
import ArealUK.Chunk11825
import ArealUK.Chunk11826
import ArealUK.Chunk11827
import ArealUK.Chunk11828
import ArealUK.Chunk11829
import ArealUK.Chunk11830
import ArealUK.Chunk11831
import ArealUK.Chunk11832
import ArealUK.Chunk11833
import ArealUK.Chunk11834
import ArealUK.Chunk11835
import ArealUK.Chunk11836
import ArealUK.Chunk11837
import ArealUK.Chunk11838
import ArealUK.Chunk11839
import ArealUK.Chunk11840
import ArealUK.Chunk11841
import ArealUK.Chunk11842
import ArealUK.Chunk11843
import ArealUK.Chunk11844
import ArealUK.Chunk11845
import ArealUK.Chunk11846
import ArealUK.Chunk11847
import ArealUK.Chunk11848
import ArealUK.Chunk11849
import ArealUK.Chunk11850
import ArealUK.Chunk11851
import ArealUK.Chunk11852
import ArealUK.Chunk11853
import ArealUK.Chunk11854
import ArealUK.Chunk11855
import ArealUK.Chunk11856
import ArealUK.Chunk11857
import ArealUK.Chunk11858
import ArealUK.Chunk11859
import ArealUK.Chunk11860
import ArealUK.Chunk11861
import ArealUK.Chunk11862
import ArealUK.Chunk11863
import ArealUK.Chunk11864
import ArealUK.Chunk11865
import ArealUK.Chunk11866
import ArealUK.Chunk11867
import ArealUK.Chunk11868
import ArealUK.Chunk11869
import ArealUK.Chunk11870
import ArealUK.Chunk11871
import ArealUK.Chunk11872
import ArealUK.Chunk11873
import ArealUK.Chunk11874
import ArealUK.Chunk11875
import ArealUK.Chunk11876
import ArealUK.Chunk11877
import ArealUK.Chunk11878
import ArealUK.Chunk11879
import ArealUK.Chunk11880
import ArealUK.Chunk11881
import ArealUK.Chunk11882
import ArealUK.Chunk11883
import ArealUK.Chunk11884
import ArealUK.Chunk11885
import ArealUK.Chunk11886
import ArealUK.Chunk11887
import ArealUK.Chunk11888
import ArealUK.Chunk11889
import ArealUK.Chunk11890
import ArealUK.Chunk11891
import ArealUK.Chunk11892
import ArealUK.Chunk11893
import ArealUK.Chunk11894
import ArealUK.Chunk11895
import ArealUK.Chunk11896
import ArealUK.Chunk11897
import ArealUK.Chunk11898
import ArealUK.Chunk11899
import Areal.UCert.LeavesKGen

/-! Group 118 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_118 : leavesOK ctxLitU 466750000000 2 ((leaves.drop 23600).take 200) 471750000000 2 = true := by
  have s99 := ArealUCore.ArealUK.chunk_11899
  have s98 : leavesOK ctxLitU 471650000000 2 ((leaves.drop 23796).take 4) 471750000000 2 = true :=
    take_step (n := 2) (t := 4) (b := 23798) rfl rfl ArealUCore.ArealUK.chunk_11898 s99
  have s97 : leavesOK ctxLitU 471600000000 2 ((leaves.drop 23794).take 6) 471750000000 2 = true :=
    take_step (n := 2) (t := 6) (b := 23796) rfl rfl ArealUCore.ArealUK.chunk_11897 s98
  have s96 : leavesOK ctxLitU 471550000000 2 ((leaves.drop 23792).take 8) 471750000000 2 = true :=
    take_step (n := 2) (t := 8) (b := 23794) rfl rfl ArealUCore.ArealUK.chunk_11896 s97
  have s95 : leavesOK ctxLitU 471500000000 2 ((leaves.drop 23790).take 10) 471750000000 2 = true :=
    take_step (n := 2) (t := 10) (b := 23792) rfl rfl ArealUCore.ArealUK.chunk_11895 s96
  have s94 : leavesOK ctxLitU 471450000000 2 ((leaves.drop 23788).take 12) 471750000000 2 = true :=
    take_step (n := 2) (t := 12) (b := 23790) rfl rfl ArealUCore.ArealUK.chunk_11894 s95
  have s93 : leavesOK ctxLitU 471400000000 2 ((leaves.drop 23786).take 14) 471750000000 2 = true :=
    take_step (n := 2) (t := 14) (b := 23788) rfl rfl ArealUCore.ArealUK.chunk_11893 s94
  have s92 : leavesOK ctxLitU 471350000000 2 ((leaves.drop 23784).take 16) 471750000000 2 = true :=
    take_step (n := 2) (t := 16) (b := 23786) rfl rfl ArealUCore.ArealUK.chunk_11892 s93
  have s91 : leavesOK ctxLitU 471300000000 2 ((leaves.drop 23782).take 18) 471750000000 2 = true :=
    take_step (n := 2) (t := 18) (b := 23784) rfl rfl ArealUCore.ArealUK.chunk_11891 s92
  have s90 : leavesOK ctxLitU 471250000000 2 ((leaves.drop 23780).take 20) 471750000000 2 = true :=
    take_step (n := 2) (t := 20) (b := 23782) rfl rfl ArealUCore.ArealUK.chunk_11890 s91
  have s89 : leavesOK ctxLitU 471200000000 2 ((leaves.drop 23778).take 22) 471750000000 2 = true :=
    take_step (n := 2) (t := 22) (b := 23780) rfl rfl ArealUCore.ArealUK.chunk_11889 s90
  have s88 : leavesOK ctxLitU 471150000000 2 ((leaves.drop 23776).take 24) 471750000000 2 = true :=
    take_step (n := 2) (t := 24) (b := 23778) rfl rfl ArealUCore.ArealUK.chunk_11888 s89
  have s87 : leavesOK ctxLitU 471100000000 2 ((leaves.drop 23774).take 26) 471750000000 2 = true :=
    take_step (n := 2) (t := 26) (b := 23776) rfl rfl ArealUCore.ArealUK.chunk_11887 s88
  have s86 : leavesOK ctxLitU 471050000000 2 ((leaves.drop 23772).take 28) 471750000000 2 = true :=
    take_step (n := 2) (t := 28) (b := 23774) rfl rfl ArealUCore.ArealUK.chunk_11886 s87
  have s85 : leavesOK ctxLitU 471000000000 2 ((leaves.drop 23770).take 30) 471750000000 2 = true :=
    take_step (n := 2) (t := 30) (b := 23772) rfl rfl ArealUCore.ArealUK.chunk_11885 s86
  have s84 : leavesOK ctxLitU 470950000000 2 ((leaves.drop 23768).take 32) 471750000000 2 = true :=
    take_step (n := 2) (t := 32) (b := 23770) rfl rfl ArealUCore.ArealUK.chunk_11884 s85
  have s83 : leavesOK ctxLitU 470900000000 2 ((leaves.drop 23766).take 34) 471750000000 2 = true :=
    take_step (n := 2) (t := 34) (b := 23768) rfl rfl ArealUCore.ArealUK.chunk_11883 s84
  have s82 : leavesOK ctxLitU 470850000000 2 ((leaves.drop 23764).take 36) 471750000000 2 = true :=
    take_step (n := 2) (t := 36) (b := 23766) rfl rfl ArealUCore.ArealUK.chunk_11882 s83
  have s81 : leavesOK ctxLitU 470800000000 2 ((leaves.drop 23762).take 38) 471750000000 2 = true :=
    take_step (n := 2) (t := 38) (b := 23764) rfl rfl ArealUCore.ArealUK.chunk_11881 s82
  have s80 : leavesOK ctxLitU 470750000000 2 ((leaves.drop 23760).take 40) 471750000000 2 = true :=
    take_step (n := 2) (t := 40) (b := 23762) rfl rfl ArealUCore.ArealUK.chunk_11880 s81
  have s79 : leavesOK ctxLitU 470700000000 2 ((leaves.drop 23758).take 42) 471750000000 2 = true :=
    take_step (n := 2) (t := 42) (b := 23760) rfl rfl ArealUCore.ArealUK.chunk_11879 s80
  have s78 : leavesOK ctxLitU 470650000000 2 ((leaves.drop 23756).take 44) 471750000000 2 = true :=
    take_step (n := 2) (t := 44) (b := 23758) rfl rfl ArealUCore.ArealUK.chunk_11878 s79
  have s77 : leavesOK ctxLitU 470600000000 2 ((leaves.drop 23754).take 46) 471750000000 2 = true :=
    take_step (n := 2) (t := 46) (b := 23756) rfl rfl ArealUCore.ArealUK.chunk_11877 s78
  have s76 : leavesOK ctxLitU 470550000000 2 ((leaves.drop 23752).take 48) 471750000000 2 = true :=
    take_step (n := 2) (t := 48) (b := 23754) rfl rfl ArealUCore.ArealUK.chunk_11876 s77
  have s75 : leavesOK ctxLitU 470500000000 2 ((leaves.drop 23750).take 50) 471750000000 2 = true :=
    take_step (n := 2) (t := 50) (b := 23752) rfl rfl ArealUCore.ArealUK.chunk_11875 s76
  have s74 : leavesOK ctxLitU 470450000000 2 ((leaves.drop 23748).take 52) 471750000000 2 = true :=
    take_step (n := 2) (t := 52) (b := 23750) rfl rfl ArealUCore.ArealUK.chunk_11874 s75
  have s73 : leavesOK ctxLitU 470400000000 2 ((leaves.drop 23746).take 54) 471750000000 2 = true :=
    take_step (n := 2) (t := 54) (b := 23748) rfl rfl ArealUCore.ArealUK.chunk_11873 s74
  have s72 : leavesOK ctxLitU 470350000000 2 ((leaves.drop 23744).take 56) 471750000000 2 = true :=
    take_step (n := 2) (t := 56) (b := 23746) rfl rfl ArealUCore.ArealUK.chunk_11872 s73
  have s71 : leavesOK ctxLitU 470300000000 2 ((leaves.drop 23742).take 58) 471750000000 2 = true :=
    take_step (n := 2) (t := 58) (b := 23744) rfl rfl ArealUCore.ArealUK.chunk_11871 s72
  have s70 : leavesOK ctxLitU 470250000000 2 ((leaves.drop 23740).take 60) 471750000000 2 = true :=
    take_step (n := 2) (t := 60) (b := 23742) rfl rfl ArealUCore.ArealUK.chunk_11870 s71
  have s69 : leavesOK ctxLitU 470200000000 2 ((leaves.drop 23738).take 62) 471750000000 2 = true :=
    take_step (n := 2) (t := 62) (b := 23740) rfl rfl ArealUCore.ArealUK.chunk_11869 s70
  have s68 : leavesOK ctxLitU 470150000000 2 ((leaves.drop 23736).take 64) 471750000000 2 = true :=
    take_step (n := 2) (t := 64) (b := 23738) rfl rfl ArealUCore.ArealUK.chunk_11868 s69
  have s67 : leavesOK ctxLitU 470100000000 2 ((leaves.drop 23734).take 66) 471750000000 2 = true :=
    take_step (n := 2) (t := 66) (b := 23736) rfl rfl ArealUCore.ArealUK.chunk_11867 s68
  have s66 : leavesOK ctxLitU 470050000000 2 ((leaves.drop 23732).take 68) 471750000000 2 = true :=
    take_step (n := 2) (t := 68) (b := 23734) rfl rfl ArealUCore.ArealUK.chunk_11866 s67
  have s65 : leavesOK ctxLitU 470000000000 2 ((leaves.drop 23730).take 70) 471750000000 2 = true :=
    take_step (n := 2) (t := 70) (b := 23732) rfl rfl ArealUCore.ArealUK.chunk_11865 s66
  have s64 : leavesOK ctxLitU 469950000000 2 ((leaves.drop 23728).take 72) 471750000000 2 = true :=
    take_step (n := 2) (t := 72) (b := 23730) rfl rfl ArealUCore.ArealUK.chunk_11864 s65
  have s63 : leavesOK ctxLitU 469900000000 2 ((leaves.drop 23726).take 74) 471750000000 2 = true :=
    take_step (n := 2) (t := 74) (b := 23728) rfl rfl ArealUCore.ArealUK.chunk_11863 s64
  have s62 : leavesOK ctxLitU 469850000000 2 ((leaves.drop 23724).take 76) 471750000000 2 = true :=
    take_step (n := 2) (t := 76) (b := 23726) rfl rfl ArealUCore.ArealUK.chunk_11862 s63
  have s61 : leavesOK ctxLitU 469800000000 2 ((leaves.drop 23722).take 78) 471750000000 2 = true :=
    take_step (n := 2) (t := 78) (b := 23724) rfl rfl ArealUCore.ArealUK.chunk_11861 s62
  have s60 : leavesOK ctxLitU 469750000000 2 ((leaves.drop 23720).take 80) 471750000000 2 = true :=
    take_step (n := 2) (t := 80) (b := 23722) rfl rfl ArealUCore.ArealUK.chunk_11860 s61
  have s59 : leavesOK ctxLitU 469700000000 2 ((leaves.drop 23718).take 82) 471750000000 2 = true :=
    take_step (n := 2) (t := 82) (b := 23720) rfl rfl ArealUCore.ArealUK.chunk_11859 s60
  have s58 : leavesOK ctxLitU 469650000000 2 ((leaves.drop 23716).take 84) 471750000000 2 = true :=
    take_step (n := 2) (t := 84) (b := 23718) rfl rfl ArealUCore.ArealUK.chunk_11858 s59
  have s57 : leavesOK ctxLitU 469600000000 2 ((leaves.drop 23714).take 86) 471750000000 2 = true :=
    take_step (n := 2) (t := 86) (b := 23716) rfl rfl ArealUCore.ArealUK.chunk_11857 s58
  have s56 : leavesOK ctxLitU 469550000000 2 ((leaves.drop 23712).take 88) 471750000000 2 = true :=
    take_step (n := 2) (t := 88) (b := 23714) rfl rfl ArealUCore.ArealUK.chunk_11856 s57
  have s55 : leavesOK ctxLitU 469500000000 2 ((leaves.drop 23710).take 90) 471750000000 2 = true :=
    take_step (n := 2) (t := 90) (b := 23712) rfl rfl ArealUCore.ArealUK.chunk_11855 s56
  have s54 : leavesOK ctxLitU 469450000000 2 ((leaves.drop 23708).take 92) 471750000000 2 = true :=
    take_step (n := 2) (t := 92) (b := 23710) rfl rfl ArealUCore.ArealUK.chunk_11854 s55
  have s53 : leavesOK ctxLitU 469400000000 2 ((leaves.drop 23706).take 94) 471750000000 2 = true :=
    take_step (n := 2) (t := 94) (b := 23708) rfl rfl ArealUCore.ArealUK.chunk_11853 s54
  have s52 : leavesOK ctxLitU 469350000000 2 ((leaves.drop 23704).take 96) 471750000000 2 = true :=
    take_step (n := 2) (t := 96) (b := 23706) rfl rfl ArealUCore.ArealUK.chunk_11852 s53
  have s51 : leavesOK ctxLitU 469300000000 2 ((leaves.drop 23702).take 98) 471750000000 2 = true :=
    take_step (n := 2) (t := 98) (b := 23704) rfl rfl ArealUCore.ArealUK.chunk_11851 s52
  have s50 : leavesOK ctxLitU 469250000000 2 ((leaves.drop 23700).take 100) 471750000000 2 = true :=
    take_step (n := 2) (t := 100) (b := 23702) rfl rfl ArealUCore.ArealUK.chunk_11850 s51
  have s49 : leavesOK ctxLitU 469200000000 2 ((leaves.drop 23698).take 102) 471750000000 2 = true :=
    take_step (n := 2) (t := 102) (b := 23700) rfl rfl ArealUCore.ArealUK.chunk_11849 s50
  have s48 : leavesOK ctxLitU 469150000000 2 ((leaves.drop 23696).take 104) 471750000000 2 = true :=
    take_step (n := 2) (t := 104) (b := 23698) rfl rfl ArealUCore.ArealUK.chunk_11848 s49
  have s47 : leavesOK ctxLitU 469100000000 2 ((leaves.drop 23694).take 106) 471750000000 2 = true :=
    take_step (n := 2) (t := 106) (b := 23696) rfl rfl ArealUCore.ArealUK.chunk_11847 s48
  have s46 : leavesOK ctxLitU 469050000000 2 ((leaves.drop 23692).take 108) 471750000000 2 = true :=
    take_step (n := 2) (t := 108) (b := 23694) rfl rfl ArealUCore.ArealUK.chunk_11846 s47
  have s45 : leavesOK ctxLitU 469000000000 2 ((leaves.drop 23690).take 110) 471750000000 2 = true :=
    take_step (n := 2) (t := 110) (b := 23692) rfl rfl ArealUCore.ArealUK.chunk_11845 s46
  have s44 : leavesOK ctxLitU 468950000000 2 ((leaves.drop 23688).take 112) 471750000000 2 = true :=
    take_step (n := 2) (t := 112) (b := 23690) rfl rfl ArealUCore.ArealUK.chunk_11844 s45
  have s43 : leavesOK ctxLitU 468900000000 2 ((leaves.drop 23686).take 114) 471750000000 2 = true :=
    take_step (n := 2) (t := 114) (b := 23688) rfl rfl ArealUCore.ArealUK.chunk_11843 s44
  have s42 : leavesOK ctxLitU 468850000000 2 ((leaves.drop 23684).take 116) 471750000000 2 = true :=
    take_step (n := 2) (t := 116) (b := 23686) rfl rfl ArealUCore.ArealUK.chunk_11842 s43
  have s41 : leavesOK ctxLitU 468800000000 2 ((leaves.drop 23682).take 118) 471750000000 2 = true :=
    take_step (n := 2) (t := 118) (b := 23684) rfl rfl ArealUCore.ArealUK.chunk_11841 s42
  have s40 : leavesOK ctxLitU 468750000000 2 ((leaves.drop 23680).take 120) 471750000000 2 = true :=
    take_step (n := 2) (t := 120) (b := 23682) rfl rfl ArealUCore.ArealUK.chunk_11840 s41
  have s39 : leavesOK ctxLitU 468700000000 2 ((leaves.drop 23678).take 122) 471750000000 2 = true :=
    take_step (n := 2) (t := 122) (b := 23680) rfl rfl ArealUCore.ArealUK.chunk_11839 s40
  have s38 : leavesOK ctxLitU 468650000000 2 ((leaves.drop 23676).take 124) 471750000000 2 = true :=
    take_step (n := 2) (t := 124) (b := 23678) rfl rfl ArealUCore.ArealUK.chunk_11838 s39
  have s37 : leavesOK ctxLitU 468600000000 2 ((leaves.drop 23674).take 126) 471750000000 2 = true :=
    take_step (n := 2) (t := 126) (b := 23676) rfl rfl ArealUCore.ArealUK.chunk_11837 s38
  have s36 : leavesOK ctxLitU 468550000000 2 ((leaves.drop 23672).take 128) 471750000000 2 = true :=
    take_step (n := 2) (t := 128) (b := 23674) rfl rfl ArealUCore.ArealUK.chunk_11836 s37
  have s35 : leavesOK ctxLitU 468500000000 2 ((leaves.drop 23670).take 130) 471750000000 2 = true :=
    take_step (n := 2) (t := 130) (b := 23672) rfl rfl ArealUCore.ArealUK.chunk_11835 s36
  have s34 : leavesOK ctxLitU 468450000000 2 ((leaves.drop 23668).take 132) 471750000000 2 = true :=
    take_step (n := 2) (t := 132) (b := 23670) rfl rfl ArealUCore.ArealUK.chunk_11834 s35
  have s33 : leavesOK ctxLitU 468400000000 2 ((leaves.drop 23666).take 134) 471750000000 2 = true :=
    take_step (n := 2) (t := 134) (b := 23668) rfl rfl ArealUCore.ArealUK.chunk_11833 s34
  have s32 : leavesOK ctxLitU 468350000000 2 ((leaves.drop 23664).take 136) 471750000000 2 = true :=
    take_step (n := 2) (t := 136) (b := 23666) rfl rfl ArealUCore.ArealUK.chunk_11832 s33
  have s31 : leavesOK ctxLitU 468300000000 2 ((leaves.drop 23662).take 138) 471750000000 2 = true :=
    take_step (n := 2) (t := 138) (b := 23664) rfl rfl ArealUCore.ArealUK.chunk_11831 s32
  have s30 : leavesOK ctxLitU 468250000000 2 ((leaves.drop 23660).take 140) 471750000000 2 = true :=
    take_step (n := 2) (t := 140) (b := 23662) rfl rfl ArealUCore.ArealUK.chunk_11830 s31
  have s29 : leavesOK ctxLitU 468200000000 2 ((leaves.drop 23658).take 142) 471750000000 2 = true :=
    take_step (n := 2) (t := 142) (b := 23660) rfl rfl ArealUCore.ArealUK.chunk_11829 s30
  have s28 : leavesOK ctxLitU 468150000000 2 ((leaves.drop 23656).take 144) 471750000000 2 = true :=
    take_step (n := 2) (t := 144) (b := 23658) rfl rfl ArealUCore.ArealUK.chunk_11828 s29
  have s27 : leavesOK ctxLitU 468100000000 2 ((leaves.drop 23654).take 146) 471750000000 2 = true :=
    take_step (n := 2) (t := 146) (b := 23656) rfl rfl ArealUCore.ArealUK.chunk_11827 s28
  have s26 : leavesOK ctxLitU 468050000000 2 ((leaves.drop 23652).take 148) 471750000000 2 = true :=
    take_step (n := 2) (t := 148) (b := 23654) rfl rfl ArealUCore.ArealUK.chunk_11826 s27
  have s25 : leavesOK ctxLitU 468000000000 2 ((leaves.drop 23650).take 150) 471750000000 2 = true :=
    take_step (n := 2) (t := 150) (b := 23652) rfl rfl ArealUCore.ArealUK.chunk_11825 s26
  have s24 : leavesOK ctxLitU 467950000000 2 ((leaves.drop 23648).take 152) 471750000000 2 = true :=
    take_step (n := 2) (t := 152) (b := 23650) rfl rfl ArealUCore.ArealUK.chunk_11824 s25
  have s23 : leavesOK ctxLitU 467900000000 2 ((leaves.drop 23646).take 154) 471750000000 2 = true :=
    take_step (n := 2) (t := 154) (b := 23648) rfl rfl ArealUCore.ArealUK.chunk_11823 s24
  have s22 : leavesOK ctxLitU 467850000000 2 ((leaves.drop 23644).take 156) 471750000000 2 = true :=
    take_step (n := 2) (t := 156) (b := 23646) rfl rfl ArealUCore.ArealUK.chunk_11822 s23
  have s21 : leavesOK ctxLitU 467800000000 2 ((leaves.drop 23642).take 158) 471750000000 2 = true :=
    take_step (n := 2) (t := 158) (b := 23644) rfl rfl ArealUCore.ArealUK.chunk_11821 s22
  have s20 : leavesOK ctxLitU 467750000000 2 ((leaves.drop 23640).take 160) 471750000000 2 = true :=
    take_step (n := 2) (t := 160) (b := 23642) rfl rfl ArealUCore.ArealUK.chunk_11820 s21
  have s19 : leavesOK ctxLitU 467700000000 2 ((leaves.drop 23638).take 162) 471750000000 2 = true :=
    take_step (n := 2) (t := 162) (b := 23640) rfl rfl ArealUCore.ArealUK.chunk_11819 s20
  have s18 : leavesOK ctxLitU 467650000000 2 ((leaves.drop 23636).take 164) 471750000000 2 = true :=
    take_step (n := 2) (t := 164) (b := 23638) rfl rfl ArealUCore.ArealUK.chunk_11818 s19
  have s17 : leavesOK ctxLitU 467600000000 2 ((leaves.drop 23634).take 166) 471750000000 2 = true :=
    take_step (n := 2) (t := 166) (b := 23636) rfl rfl ArealUCore.ArealUK.chunk_11817 s18
  have s16 : leavesOK ctxLitU 467550000000 2 ((leaves.drop 23632).take 168) 471750000000 2 = true :=
    take_step (n := 2) (t := 168) (b := 23634) rfl rfl ArealUCore.ArealUK.chunk_11816 s17
  have s15 : leavesOK ctxLitU 467500000000 2 ((leaves.drop 23630).take 170) 471750000000 2 = true :=
    take_step (n := 2) (t := 170) (b := 23632) rfl rfl ArealUCore.ArealUK.chunk_11815 s16
  have s14 : leavesOK ctxLitU 467450000000 2 ((leaves.drop 23628).take 172) 471750000000 2 = true :=
    take_step (n := 2) (t := 172) (b := 23630) rfl rfl ArealUCore.ArealUK.chunk_11814 s15
  have s13 : leavesOK ctxLitU 467400000000 2 ((leaves.drop 23626).take 174) 471750000000 2 = true :=
    take_step (n := 2) (t := 174) (b := 23628) rfl rfl ArealUCore.ArealUK.chunk_11813 s14
  have s12 : leavesOK ctxLitU 467350000000 2 ((leaves.drop 23624).take 176) 471750000000 2 = true :=
    take_step (n := 2) (t := 176) (b := 23626) rfl rfl ArealUCore.ArealUK.chunk_11812 s13
  have s11 : leavesOK ctxLitU 467300000000 2 ((leaves.drop 23622).take 178) 471750000000 2 = true :=
    take_step (n := 2) (t := 178) (b := 23624) rfl rfl ArealUCore.ArealUK.chunk_11811 s12
  have s10 : leavesOK ctxLitU 467250000000 2 ((leaves.drop 23620).take 180) 471750000000 2 = true :=
    take_step (n := 2) (t := 180) (b := 23622) rfl rfl ArealUCore.ArealUK.chunk_11810 s11
  have s9 : leavesOK ctxLitU 467200000000 2 ((leaves.drop 23618).take 182) 471750000000 2 = true :=
    take_step (n := 2) (t := 182) (b := 23620) rfl rfl ArealUCore.ArealUK.chunk_11809 s10
  have s8 : leavesOK ctxLitU 467150000000 2 ((leaves.drop 23616).take 184) 471750000000 2 = true :=
    take_step (n := 2) (t := 184) (b := 23618) rfl rfl ArealUCore.ArealUK.chunk_11808 s9
  have s7 : leavesOK ctxLitU 467100000000 2 ((leaves.drop 23614).take 186) 471750000000 2 = true :=
    take_step (n := 2) (t := 186) (b := 23616) rfl rfl ArealUCore.ArealUK.chunk_11807 s8
  have s6 : leavesOK ctxLitU 467050000000 2 ((leaves.drop 23612).take 188) 471750000000 2 = true :=
    take_step (n := 2) (t := 188) (b := 23614) rfl rfl ArealUCore.ArealUK.chunk_11806 s7
  have s5 : leavesOK ctxLitU 467000000000 2 ((leaves.drop 23610).take 190) 471750000000 2 = true :=
    take_step (n := 2) (t := 190) (b := 23612) rfl rfl ArealUCore.ArealUK.chunk_11805 s6
  have s4 : leavesOK ctxLitU 466950000000 2 ((leaves.drop 23608).take 192) 471750000000 2 = true :=
    take_step (n := 2) (t := 192) (b := 23610) rfl rfl ArealUCore.ArealUK.chunk_11804 s5
  have s3 : leavesOK ctxLitU 466900000000 2 ((leaves.drop 23606).take 194) 471750000000 2 = true :=
    take_step (n := 2) (t := 194) (b := 23608) rfl rfl ArealUCore.ArealUK.chunk_11803 s4
  have s2 : leavesOK ctxLitU 466850000000 2 ((leaves.drop 23604).take 196) 471750000000 2 = true :=
    take_step (n := 2) (t := 196) (b := 23606) rfl rfl ArealUCore.ArealUK.chunk_11802 s3
  have s1 : leavesOK ctxLitU 466800000000 2 ((leaves.drop 23602).take 198) 471750000000 2 = true :=
    take_step (n := 2) (t := 198) (b := 23604) rfl rfl ArealUCore.ArealUK.chunk_11801 s2
  have s0 : leavesOK ctxLitU 466750000000 2 ((leaves.drop 23600).take 200) 471750000000 2 = true :=
    take_step (n := 2) (t := 200) (b := 23602) rfl rfl ArealUCore.ArealUK.chunk_11800 s1
  exact s0

end Areal.UCert

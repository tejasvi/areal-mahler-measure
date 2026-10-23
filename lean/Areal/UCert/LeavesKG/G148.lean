import ArealUK.Chunk14800
import ArealUK.Chunk14801
import ArealUK.Chunk14802
import ArealUK.Chunk14803
import ArealUK.Chunk14804
import ArealUK.Chunk14805
import ArealUK.Chunk14806
import ArealUK.Chunk14807
import ArealUK.Chunk14808
import ArealUK.Chunk14809
import ArealUK.Chunk14810
import ArealUK.Chunk14811
import ArealUK.Chunk14812
import ArealUK.Chunk14813
import ArealUK.Chunk14814
import ArealUK.Chunk14815
import ArealUK.Chunk14816
import ArealUK.Chunk14817
import ArealUK.Chunk14818
import ArealUK.Chunk14819
import ArealUK.Chunk14820
import ArealUK.Chunk14821
import ArealUK.Chunk14822
import ArealUK.Chunk14823
import ArealUK.Chunk14824
import ArealUK.Chunk14825
import ArealUK.Chunk14826
import ArealUK.Chunk14827
import ArealUK.Chunk14828
import ArealUK.Chunk14829
import ArealUK.Chunk14830
import ArealUK.Chunk14831
import ArealUK.Chunk14832
import ArealUK.Chunk14833
import ArealUK.Chunk14834
import ArealUK.Chunk14835
import ArealUK.Chunk14836
import ArealUK.Chunk14837
import ArealUK.Chunk14838
import ArealUK.Chunk14839
import ArealUK.Chunk14840
import ArealUK.Chunk14841
import ArealUK.Chunk14842
import ArealUK.Chunk14843
import ArealUK.Chunk14844
import ArealUK.Chunk14845
import ArealUK.Chunk14846
import ArealUK.Chunk14847
import ArealUK.Chunk14848
import ArealUK.Chunk14849
import ArealUK.Chunk14850
import ArealUK.Chunk14851
import ArealUK.Chunk14852
import ArealUK.Chunk14853
import ArealUK.Chunk14854
import ArealUK.Chunk14855
import ArealUK.Chunk14856
import ArealUK.Chunk14857
import ArealUK.Chunk14858
import ArealUK.Chunk14859
import ArealUK.Chunk14860
import ArealUK.Chunk14861
import ArealUK.Chunk14862
import ArealUK.Chunk14863
import ArealUK.Chunk14864
import ArealUK.Chunk14865
import ArealUK.Chunk14866
import ArealUK.Chunk14867
import ArealUK.Chunk14868
import ArealUK.Chunk14869
import ArealUK.Chunk14870
import ArealUK.Chunk14871
import ArealUK.Chunk14872
import ArealUK.Chunk14873
import ArealUK.Chunk14874
import ArealUK.Chunk14875
import ArealUK.Chunk14876
import ArealUK.Chunk14877
import ArealUK.Chunk14878
import ArealUK.Chunk14879
import ArealUK.Chunk14880
import ArealUK.Chunk14881
import ArealUK.Chunk14882
import ArealUK.Chunk14883
import ArealUK.Chunk14884
import ArealUK.Chunk14885
import ArealUK.Chunk14886
import ArealUK.Chunk14887
import ArealUK.Chunk14888
import ArealUK.Chunk14889
import ArealUK.Chunk14890
import ArealUK.Chunk14891
import ArealUK.Chunk14892
import ArealUK.Chunk14893
import ArealUK.Chunk14894
import ArealUK.Chunk14895
import ArealUK.Chunk14896
import ArealUK.Chunk14897
import ArealUK.Chunk14898
import ArealUK.Chunk14899
import Areal.UCert.LeavesKGen

/-! Group 148 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_148 : leavesOK ctxLitU 307362500000 1 ((leaves.drop 29600).take 200) 155056250000 0 = true := by
  have s99 := ArealUCore.ArealUK.chunk_14899
  have s98 : leavesOK ctxLitU 155031250000 0 ((leaves.drop 29796).take 4) 155056250000 0 = true :=
    take_step (n := 2) (t := 4) (b := 29798) rfl rfl ArealUCore.ArealUK.chunk_14898 s99
  have s97 : leavesOK ctxLitU 310037500000 1 ((leaves.drop 29794).take 6) 155056250000 0 = true :=
    take_step (n := 2) (t := 6) (b := 29796) rfl rfl ArealUCore.ArealUK.chunk_14897 s98
  have s96 : leavesOK ctxLitU 155000000000 0 ((leaves.drop 29792).take 8) 155056250000 0 = true :=
    take_step (n := 2) (t := 8) (b := 29794) rfl rfl ArealUCore.ArealUK.chunk_14896 s97
  have s95 : leavesOK ctxLitU 619925000000 2 ((leaves.drop 29790).take 10) 155056250000 0 = true :=
    take_step (n := 2) (t := 10) (b := 29792) rfl rfl ArealUCore.ArealUK.chunk_14895 s96
  have s94 : leavesOK ctxLitU 619875000000 2 ((leaves.drop 29788).take 12) 155056250000 0 = true :=
    take_step (n := 2) (t := 12) (b := 29790) rfl rfl ArealUCore.ArealUK.chunk_14894 s95
  have s93 : leavesOK ctxLitU 619825000000 2 ((leaves.drop 29786).take 14) 155056250000 0 = true :=
    take_step (n := 2) (t := 14) (b := 29788) rfl rfl ArealUCore.ArealUK.chunk_14893 s94
  have s92 : leavesOK ctxLitU 619775000000 2 ((leaves.drop 29784).take 16) 155056250000 0 = true :=
    take_step (n := 2) (t := 16) (b := 29786) rfl rfl ArealUCore.ArealUK.chunk_14892 s93
  have s91 : leavesOK ctxLitU 309850000000 1 ((leaves.drop 29782).take 18) 155056250000 0 = true :=
    take_step (n := 2) (t := 18) (b := 29784) rfl rfl ArealUCore.ArealUK.chunk_14891 s92
  have s90 : leavesOK ctxLitU 619625000000 2 ((leaves.drop 29780).take 20) 155056250000 0 = true :=
    take_step (n := 2) (t := 20) (b := 29782) rfl rfl ArealUCore.ArealUK.chunk_14890 s91
  have s89 : leavesOK ctxLitU 309787500000 1 ((leaves.drop 29778).take 22) 155056250000 0 = true :=
    take_step (n := 2) (t := 22) (b := 29780) rfl rfl ArealUCore.ArealUK.chunk_14889 s90
  have s88 : leavesOK ctxLitU 309762500000 1 ((leaves.drop 29776).take 24) 155056250000 0 = true :=
    take_step (n := 2) (t := 24) (b := 29778) rfl rfl ArealUCore.ArealUK.chunk_14888 s89
  have s87 : leavesOK ctxLitU 154868750000 0 ((leaves.drop 29774).take 26) 155056250000 0 = true :=
    take_step (n := 2) (t := 26) (b := 29776) rfl rfl ArealUCore.ArealUK.chunk_14887 s88
  have s86 : leavesOK ctxLitU 154856250000 0 ((leaves.drop 29772).take 28) 155056250000 0 = true :=
    take_step (n := 2) (t := 28) (b := 29774) rfl rfl ArealUCore.ArealUK.chunk_14886 s87
  have s85 : leavesOK ctxLitU 154843750000 0 ((leaves.drop 29770).take 30) 155056250000 0 = true :=
    take_step (n := 2) (t := 30) (b := 29772) rfl rfl ArealUCore.ArealUK.chunk_14885 s86
  have s84 : leavesOK ctxLitU 154831250000 0 ((leaves.drop 29768).take 32) 155056250000 0 = true :=
    take_step (n := 2) (t := 32) (b := 29770) rfl rfl ArealUCore.ArealUK.chunk_14884 s85
  have s83 : leavesOK ctxLitU 309637500000 1 ((leaves.drop 29766).take 34) 155056250000 0 = true :=
    take_step (n := 2) (t := 34) (b := 29768) rfl rfl ArealUCore.ArealUK.chunk_14883 s84
  have s82 : leavesOK ctxLitU 309612500000 1 ((leaves.drop 29764).take 36) 155056250000 0 = true :=
    take_step (n := 2) (t := 36) (b := 29766) rfl rfl ArealUCore.ArealUK.chunk_14882 s83
  have s81 : leavesOK ctxLitU 154787500000 0 ((leaves.drop 29762).take 38) 155056250000 0 = true :=
    take_step (n := 2) (t := 38) (b := 29764) rfl rfl ArealUCore.ArealUK.chunk_14881 s82
  have s80 : leavesOK ctxLitU 309550000000 1 ((leaves.drop 29760).take 40) 155056250000 0 = true :=
    take_step (n := 2) (t := 40) (b := 29762) rfl rfl ArealUCore.ArealUK.chunk_14880 s81
  have s79 : leavesOK ctxLitU 154762500000 0 ((leaves.drop 29758).take 42) 155056250000 0 = true :=
    take_step (n := 2) (t := 42) (b := 29760) rfl rfl ArealUCore.ArealUK.chunk_14879 s80
  have s78 : leavesOK ctxLitU 154750000000 0 ((leaves.drop 29756).take 44) 155056250000 0 = true :=
    take_step (n := 2) (t := 44) (b := 29758) rfl rfl ArealUCore.ArealUK.chunk_14878 s79
  have s77 : leavesOK ctxLitU 154737500000 0 ((leaves.drop 29754).take 46) 155056250000 0 = true :=
    take_step (n := 2) (t := 46) (b := 29756) rfl rfl ArealUCore.ArealUK.chunk_14877 s78
  have s76 : leavesOK ctxLitU 154725000000 0 ((leaves.drop 29752).take 48) 155056250000 0 = true :=
    take_step (n := 2) (t := 48) (b := 29754) rfl rfl ArealUCore.ArealUK.chunk_14876 s77
  have s75 : leavesOK ctxLitU 309425000000 1 ((leaves.drop 29750).take 50) 155056250000 0 = true :=
    take_step (n := 2) (t := 50) (b := 29752) rfl rfl ArealUCore.ArealUK.chunk_14875 s76
  have s74 : leavesOK ctxLitU 309400000000 1 ((leaves.drop 29748).take 52) 155056250000 0 = true :=
    take_step (n := 2) (t := 52) (b := 29750) rfl rfl ArealUCore.ArealUK.chunk_14874 s75
  have s73 : leavesOK ctxLitU 309375000000 1 ((leaves.drop 29746).take 54) 155056250000 0 = true :=
    take_step (n := 2) (t := 54) (b := 29748) rfl rfl ArealUCore.ArealUK.chunk_14873 s74
  have s72 : leavesOK ctxLitU 309350000000 1 ((leaves.drop 29744).take 56) 155056250000 0 = true :=
    take_step (n := 2) (t := 56) (b := 29746) rfl rfl ArealUCore.ArealUK.chunk_14872 s73
  have s71 : leavesOK ctxLitU 154662500000 0 ((leaves.drop 29742).take 58) 155056250000 0 = true :=
    take_step (n := 2) (t := 58) (b := 29744) rfl rfl ArealUCore.ArealUK.chunk_14871 s72
  have s70 : leavesOK ctxLitU 154650000000 0 ((leaves.drop 29740).take 60) 155056250000 0 = true :=
    take_step (n := 2) (t := 60) (b := 29742) rfl rfl ArealUCore.ArealUK.chunk_14870 s71
  have s69 : leavesOK ctxLitU 154637500000 0 ((leaves.drop 29738).take 62) 155056250000 0 = true :=
    take_step (n := 2) (t := 62) (b := 29740) rfl rfl ArealUCore.ArealUK.chunk_14869 s70
  have s68 : leavesOK ctxLitU 154625000000 0 ((leaves.drop 29736).take 64) 155056250000 0 = true :=
    take_step (n := 2) (t := 64) (b := 29738) rfl rfl ArealUCore.ArealUK.chunk_14868 s69
  have s67 : leavesOK ctxLitU 154600000000 0 ((leaves.drop 29734).take 66) 155056250000 0 = true :=
    take_step (n := 2) (t := 66) (b := 29736) rfl rfl ArealUCore.ArealUK.chunk_14867 s68
  have s66 : leavesOK ctxLitU 309175000000 1 ((leaves.drop 29732).take 68) 155056250000 0 = true :=
    take_step (n := 2) (t := 68) (b := 29734) rfl rfl ArealUCore.ArealUK.chunk_14866 s67
  have s65 : leavesOK ctxLitU 309150000000 1 ((leaves.drop 29730).take 70) 155056250000 0 = true :=
    take_step (n := 2) (t := 70) (b := 29732) rfl rfl ArealUCore.ArealUK.chunk_14865 s66
  have s64 : leavesOK ctxLitU 154562500000 0 ((leaves.drop 29728).take 72) 155056250000 0 = true :=
    take_step (n := 2) (t := 72) (b := 29730) rfl rfl ArealUCore.ArealUK.chunk_14864 s65
  have s63 : leavesOK ctxLitU 154550000000 0 ((leaves.drop 29726).take 74) 155056250000 0 = true :=
    take_step (n := 2) (t := 74) (b := 29728) rfl rfl ArealUCore.ArealUK.chunk_14863 s64
  have s62 : leavesOK ctxLitU 154537500000 0 ((leaves.drop 29724).take 76) 155056250000 0 = true :=
    take_step (n := 2) (t := 76) (b := 29726) rfl rfl ArealUCore.ArealUK.chunk_14862 s63
  have s61 : leavesOK ctxLitU 154525000000 0 ((leaves.drop 29722).take 78) 155056250000 0 = true :=
    take_step (n := 2) (t := 78) (b := 29724) rfl rfl ArealUCore.ArealUK.chunk_14861 s62
  have s60 : leavesOK ctxLitU 309025000000 1 ((leaves.drop 29720).take 80) 155056250000 0 = true :=
    take_step (n := 2) (t := 80) (b := 29722) rfl rfl ArealUCore.ArealUK.chunk_14860 s61
  have s59 : leavesOK ctxLitU 309000000000 1 ((leaves.drop 29718).take 82) 155056250000 0 = true :=
    take_step (n := 2) (t := 82) (b := 29720) rfl rfl ArealUCore.ArealUK.chunk_14859 s60
  have s58 : leavesOK ctxLitU 308975000000 1 ((leaves.drop 29716).take 84) 155056250000 0 = true :=
    take_step (n := 2) (t := 84) (b := 29718) rfl rfl ArealUCore.ArealUK.chunk_14858 s59
  have s57 : leavesOK ctxLitU 308950000000 1 ((leaves.drop 29714).take 86) 155056250000 0 = true :=
    take_step (n := 2) (t := 86) (b := 29716) rfl rfl ArealUCore.ArealUK.chunk_14857 s58
  have s56 : leavesOK ctxLitU 154462500000 0 ((leaves.drop 29712).take 88) 155056250000 0 = true :=
    take_step (n := 2) (t := 88) (b := 29714) rfl rfl ArealUCore.ArealUK.chunk_14856 s57
  have s55 : leavesOK ctxLitU 154450000000 0 ((leaves.drop 29710).take 90) 155056250000 0 = true :=
    take_step (n := 2) (t := 90) (b := 29712) rfl rfl ArealUCore.ArealUK.chunk_14855 s56
  have s54 : leavesOK ctxLitU 154437500000 0 ((leaves.drop 29708).take 92) 155056250000 0 = true :=
    take_step (n := 2) (t := 92) (b := 29710) rfl rfl ArealUCore.ArealUK.chunk_14854 s55
  have s53 : leavesOK ctxLitU 154425000000 0 ((leaves.drop 29706).take 94) 155056250000 0 = true :=
    take_step (n := 2) (t := 94) (b := 29708) rfl rfl ArealUCore.ArealUK.chunk_14853 s54
  have s52 : leavesOK ctxLitU 308825000000 1 ((leaves.drop 29704).take 96) 155056250000 0 = true :=
    take_step (n := 2) (t := 96) (b := 29706) rfl rfl ArealUCore.ArealUK.chunk_14852 s53
  have s51 : leavesOK ctxLitU 308800000000 1 ((leaves.drop 29702).take 98) 155056250000 0 = true :=
    take_step (n := 2) (t := 98) (b := 29704) rfl rfl ArealUCore.ArealUK.chunk_14851 s52
  have s50 : leavesOK ctxLitU 308762500000 1 ((leaves.drop 29700).take 100) 155056250000 0 = true :=
    take_step (n := 2) (t := 100) (b := 29702) rfl rfl ArealUCore.ArealUK.chunk_14850 s51
  have s49 : leavesOK ctxLitU 154368750000 0 ((leaves.drop 29698).take 102) 155056250000 0 = true :=
    take_step (n := 2) (t := 102) (b := 29700) rfl rfl ArealUCore.ArealUK.chunk_14849 s50
  have s48 : leavesOK ctxLitU 154356250000 0 ((leaves.drop 29696).take 104) 155056250000 0 = true :=
    take_step (n := 2) (t := 104) (b := 29698) rfl rfl ArealUCore.ArealUK.chunk_14848 s49
  have s47 : leavesOK ctxLitU 154343750000 0 ((leaves.drop 29694).take 106) 155056250000 0 = true :=
    take_step (n := 2) (t := 106) (b := 29696) rfl rfl ArealUCore.ArealUK.chunk_14847 s48
  have s46 : leavesOK ctxLitU 154331250000 0 ((leaves.drop 29692).take 108) 155056250000 0 = true :=
    take_step (n := 2) (t := 108) (b := 29694) rfl rfl ArealUCore.ArealUK.chunk_14846 s47
  have s45 : leavesOK ctxLitU 154312500000 0 ((leaves.drop 29690).take 110) 155056250000 0 = true :=
    take_step (n := 2) (t := 110) (b := 29692) rfl rfl ArealUCore.ArealUK.chunk_14845 s46
  have s44 : leavesOK ctxLitU 308600000000 1 ((leaves.drop 29688).take 112) 155056250000 0 = true :=
    take_step (n := 2) (t := 112) (b := 29690) rfl rfl ArealUCore.ArealUK.chunk_14844 s45
  have s43 : leavesOK ctxLitU 617150000000 2 ((leaves.drop 29686).take 114) 155056250000 0 = true :=
    take_step (n := 2) (t := 114) (b := 29688) rfl rfl ArealUCore.ArealUK.chunk_14843 s44
  have s42 : leavesOK ctxLitU 308537500000 1 ((leaves.drop 29684).take 116) 155056250000 0 = true :=
    take_step (n := 2) (t := 116) (b := 29686) rfl rfl ArealUCore.ArealUK.chunk_14842 s43
  have s41 : leavesOK ctxLitU 308512500000 1 ((leaves.drop 29682).take 118) 155056250000 0 = true :=
    take_step (n := 2) (t := 118) (b := 29684) rfl rfl ArealUCore.ArealUK.chunk_14841 s42
  have s40 : leavesOK ctxLitU 154243750000 0 ((leaves.drop 29680).take 120) 155056250000 0 = true :=
    take_step (n := 2) (t := 120) (b := 29682) rfl rfl ArealUCore.ArealUK.chunk_14840 s41
  have s39 : leavesOK ctxLitU 308468750000 1 ((leaves.drop 29678).take 122) 155056250000 0 = true :=
    take_step (n := 2) (t := 122) (b := 29680) rfl rfl ArealUCore.ArealUK.chunk_14839 s40
  have s38 : leavesOK ctxLitU 308456250000 1 ((leaves.drop 29676).take 124) 155056250000 0 = true :=
    take_step (n := 2) (t := 124) (b := 29678) rfl rfl ArealUCore.ArealUK.chunk_14838 s39
  have s37 : leavesOK ctxLitU 308437500000 1 ((leaves.drop 29674).take 126) 155056250000 0 = true :=
    take_step (n := 2) (t := 126) (b := 29676) rfl rfl ArealUCore.ArealUK.chunk_14837 s38
  have s36 : leavesOK ctxLitU 154200000000 0 ((leaves.drop 29672).take 128) 155056250000 0 = true :=
    take_step (n := 2) (t := 128) (b := 29674) rfl rfl ArealUCore.ArealUK.chunk_14836 s37
  have s35 : leavesOK ctxLitU 308375000000 1 ((leaves.drop 29670).take 130) 155056250000 0 = true :=
    take_step (n := 2) (t := 130) (b := 29672) rfl rfl ArealUCore.ArealUK.chunk_14835 s36
  have s34 : leavesOK ctxLitU 308350000000 1 ((leaves.drop 29668).take 132) 155056250000 0 = true :=
    take_step (n := 2) (t := 132) (b := 29670) rfl rfl ArealUCore.ArealUK.chunk_14834 s35
  have s33 : leavesOK ctxLitU 154162500000 0 ((leaves.drop 29666).take 134) 155056250000 0 = true :=
    take_step (n := 2) (t := 134) (b := 29668) rfl rfl ArealUCore.ArealUK.chunk_14833 s34
  have s32 : leavesOK ctxLitU 154150000000 0 ((leaves.drop 29664).take 136) 155056250000 0 = true :=
    take_step (n := 2) (t := 136) (b := 29666) rfl rfl ArealUCore.ArealUK.chunk_14832 s33
  have s31 : leavesOK ctxLitU 154137500000 0 ((leaves.drop 29662).take 138) 155056250000 0 = true :=
    take_step (n := 2) (t := 138) (b := 29664) rfl rfl ArealUCore.ArealUK.chunk_14831 s32
  have s30 : leavesOK ctxLitU 154125000000 0 ((leaves.drop 29660).take 140) 155056250000 0 = true :=
    take_step (n := 2) (t := 140) (b := 29662) rfl rfl ArealUCore.ArealUK.chunk_14830 s31
  have s29 : leavesOK ctxLitU 308225000000 1 ((leaves.drop 29658).take 142) 155056250000 0 = true :=
    take_step (n := 2) (t := 142) (b := 29660) rfl rfl ArealUCore.ArealUK.chunk_14829 s30
  have s28 : leavesOK ctxLitU 308200000000 1 ((leaves.drop 29656).take 144) 155056250000 0 = true :=
    take_step (n := 2) (t := 144) (b := 29658) rfl rfl ArealUCore.ArealUK.chunk_14828 s29
  have s27 : leavesOK ctxLitU 616350000000 2 ((leaves.drop 29654).take 146) 155056250000 0 = true :=
    take_step (n := 2) (t := 146) (b := 29656) rfl rfl ArealUCore.ArealUK.chunk_14827 s28
  have s26 : leavesOK ctxLitU 308125000000 1 ((leaves.drop 29652).take 148) 155056250000 0 = true :=
    take_step (n := 2) (t := 148) (b := 29654) rfl rfl ArealUCore.ArealUK.chunk_14826 s27
  have s25 : leavesOK ctxLitU 308075000000 1 ((leaves.drop 29650).take 150) 155056250000 0 = true :=
    take_step (n := 2) (t := 150) (b := 29652) rfl rfl ArealUCore.ArealUK.chunk_14825 s26
  have s24 : leavesOK ctxLitU 616075000000 2 ((leaves.drop 29648).take 152) 155056250000 0 = true :=
    take_step (n := 2) (t := 152) (b := 29650) rfl rfl ArealUCore.ArealUK.chunk_14824 s25
  have s23 : leavesOK ctxLitU 308000000000 1 ((leaves.drop 29646).take 154) 155056250000 0 = true :=
    take_step (n := 2) (t := 154) (b := 29648) rfl rfl ArealUCore.ArealUK.chunk_14823 s24
  have s22 : leavesOK ctxLitU 307975000000 1 ((leaves.drop 29644).take 156) 155056250000 0 = true :=
    take_step (n := 2) (t := 156) (b := 29646) rfl rfl ArealUCore.ArealUK.chunk_14822 s23
  have s21 : leavesOK ctxLitU 153968750000 0 ((leaves.drop 29642).take 158) 155056250000 0 = true :=
    take_step (n := 2) (t := 158) (b := 29644) rfl rfl ArealUCore.ArealUK.chunk_14821 s22
  have s20 : leavesOK ctxLitU 153956250000 0 ((leaves.drop 29640).take 160) 155056250000 0 = true :=
    take_step (n := 2) (t := 160) (b := 29642) rfl rfl ArealUCore.ArealUK.chunk_14820 s21
  have s19 : leavesOK ctxLitU 153943750000 0 ((leaves.drop 29638).take 162) 155056250000 0 = true :=
    take_step (n := 2) (t := 162) (b := 29640) rfl rfl ArealUCore.ArealUK.chunk_14819 s20
  have s18 : leavesOK ctxLitU 153931250000 0 ((leaves.drop 29636).take 164) 155056250000 0 = true :=
    take_step (n := 2) (t := 164) (b := 29638) rfl rfl ArealUCore.ArealUK.chunk_14818 s19
  have s17 : leavesOK ctxLitU 307837500000 1 ((leaves.drop 29634).take 166) 155056250000 0 = true :=
    take_step (n := 2) (t := 166) (b := 29636) rfl rfl ArealUCore.ArealUK.chunk_14817 s18
  have s16 : leavesOK ctxLitU 307812500000 1 ((leaves.drop 29632).take 168) 155056250000 0 = true :=
    take_step (n := 2) (t := 168) (b := 29634) rfl rfl ArealUCore.ArealUK.chunk_14816 s17
  have s15 : leavesOK ctxLitU 307787500000 1 ((leaves.drop 29630).take 170) 155056250000 0 = true :=
    take_step (n := 2) (t := 170) (b := 29632) rfl rfl ArealUCore.ArealUK.chunk_14815 s16
  have s14 : leavesOK ctxLitU 153875000000 0 ((leaves.drop 29628).take 172) 155056250000 0 = true :=
    take_step (n := 2) (t := 172) (b := 29630) rfl rfl ArealUCore.ArealUK.chunk_14814 s15
  have s13 : leavesOK ctxLitU 153862500000 0 ((leaves.drop 29626).take 174) 155056250000 0 = true :=
    take_step (n := 2) (t := 174) (b := 29628) rfl rfl ArealUCore.ArealUK.chunk_14813 s14
  have s12 : leavesOK ctxLitU 153850000000 0 ((leaves.drop 29624).take 176) 155056250000 0 = true :=
    take_step (n := 2) (t := 176) (b := 29626) rfl rfl ArealUCore.ArealUK.chunk_14812 s13
  have s11 : leavesOK ctxLitU 153837500000 0 ((leaves.drop 29622).take 178) 155056250000 0 = true :=
    take_step (n := 2) (t := 178) (b := 29624) rfl rfl ArealUCore.ArealUK.chunk_14811 s12
  have s10 : leavesOK ctxLitU 153825000000 0 ((leaves.drop 29620).take 180) 155056250000 0 = true :=
    take_step (n := 2) (t := 180) (b := 29622) rfl rfl ArealUCore.ArealUK.chunk_14810 s11
  have s9 : leavesOK ctxLitU 307625000000 1 ((leaves.drop 29618).take 182) 155056250000 0 = true :=
    take_step (n := 2) (t := 182) (b := 29620) rfl rfl ArealUCore.ArealUK.chunk_14809 s10
  have s8 : leavesOK ctxLitU 153787500000 0 ((leaves.drop 29616).take 184) 155056250000 0 = true :=
    take_step (n := 2) (t := 184) (b := 29618) rfl rfl ArealUCore.ArealUK.chunk_14808 s9
  have s7 : leavesOK ctxLitU 307550000000 1 ((leaves.drop 29614).take 186) 155056250000 0 = true :=
    take_step (n := 2) (t := 186) (b := 29616) rfl rfl ArealUCore.ArealUK.chunk_14807 s8
  have s6 : leavesOK ctxLitU 153762500000 0 ((leaves.drop 29612).take 188) 155056250000 0 = true :=
    take_step (n := 2) (t := 188) (b := 29614) rfl rfl ArealUCore.ArealUK.chunk_14806 s7
  have s5 : leavesOK ctxLitU 153750000000 0 ((leaves.drop 29610).take 190) 155056250000 0 = true :=
    take_step (n := 2) (t := 190) (b := 29612) rfl rfl ArealUCore.ArealUK.chunk_14805 s6
  have s4 : leavesOK ctxLitU 153737500000 0 ((leaves.drop 29608).take 192) 155056250000 0 = true :=
    take_step (n := 2) (t := 192) (b := 29610) rfl rfl ArealUCore.ArealUK.chunk_14804 s5
  have s3 : leavesOK ctxLitU 153725000000 0 ((leaves.drop 29606).take 194) 155056250000 0 = true :=
    take_step (n := 2) (t := 194) (b := 29608) rfl rfl ArealUCore.ArealUK.chunk_14803 s4
  have s2 : leavesOK ctxLitU 307412500000 1 ((leaves.drop 29604).take 196) 155056250000 0 = true :=
    take_step (n := 2) (t := 196) (b := 29606) rfl rfl ArealUCore.ArealUK.chunk_14802 s3
  have s1 : leavesOK ctxLitU 307387500000 1 ((leaves.drop 29602).take 198) 155056250000 0 = true :=
    take_step (n := 2) (t := 198) (b := 29604) rfl rfl ArealUCore.ArealUK.chunk_14801 s2
  have s0 : leavesOK ctxLitU 307362500000 1 ((leaves.drop 29600).take 200) 155056250000 0 = true :=
    take_step (n := 2) (t := 200) (b := 29602) rfl rfl ArealUCore.ArealUK.chunk_14800 s1
  exact s0

end Areal.UCert

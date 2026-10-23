import ArealUK.Chunk8800
import ArealUK.Chunk8801
import ArealUK.Chunk8802
import ArealUK.Chunk8803
import ArealUK.Chunk8804
import ArealUK.Chunk8805
import ArealUK.Chunk8806
import ArealUK.Chunk8807
import ArealUK.Chunk8808
import ArealUK.Chunk8809
import ArealUK.Chunk8810
import ArealUK.Chunk8811
import ArealUK.Chunk8812
import ArealUK.Chunk8813
import ArealUK.Chunk8814
import ArealUK.Chunk8815
import ArealUK.Chunk8816
import ArealUK.Chunk8817
import ArealUK.Chunk8818
import ArealUK.Chunk8819
import ArealUK.Chunk8820
import ArealUK.Chunk8821
import ArealUK.Chunk8822
import ArealUK.Chunk8823
import ArealUK.Chunk8824
import ArealUK.Chunk8825
import ArealUK.Chunk8826
import ArealUK.Chunk8827
import ArealUK.Chunk8828
import ArealUK.Chunk8829
import ArealUK.Chunk8830
import ArealUK.Chunk8831
import ArealUK.Chunk8832
import ArealUK.Chunk8833
import ArealUK.Chunk8834
import ArealUK.Chunk8835
import ArealUK.Chunk8836
import ArealUK.Chunk8837
import ArealUK.Chunk8838
import ArealUK.Chunk8839
import ArealUK.Chunk8840
import ArealUK.Chunk8841
import ArealUK.Chunk8842
import ArealUK.Chunk8843
import ArealUK.Chunk8844
import ArealUK.Chunk8845
import ArealUK.Chunk8846
import ArealUK.Chunk8847
import ArealUK.Chunk8848
import ArealUK.Chunk8849
import ArealUK.Chunk8850
import ArealUK.Chunk8851
import ArealUK.Chunk8852
import ArealUK.Chunk8853
import ArealUK.Chunk8854
import ArealUK.Chunk8855
import ArealUK.Chunk8856
import ArealUK.Chunk8857
import ArealUK.Chunk8858
import ArealUK.Chunk8859
import ArealUK.Chunk8860
import ArealUK.Chunk8861
import ArealUK.Chunk8862
import ArealUK.Chunk8863
import ArealUK.Chunk8864
import ArealUK.Chunk8865
import ArealUK.Chunk8866
import ArealUK.Chunk8867
import ArealUK.Chunk8868
import ArealUK.Chunk8869
import ArealUK.Chunk8870
import ArealUK.Chunk8871
import ArealUK.Chunk8872
import ArealUK.Chunk8873
import ArealUK.Chunk8874
import ArealUK.Chunk8875
import ArealUK.Chunk8876
import ArealUK.Chunk8877
import ArealUK.Chunk8878
import ArealUK.Chunk8879
import ArealUK.Chunk8880
import ArealUK.Chunk8881
import ArealUK.Chunk8882
import ArealUK.Chunk8883
import ArealUK.Chunk8884
import ArealUK.Chunk8885
import ArealUK.Chunk8886
import ArealUK.Chunk8887
import ArealUK.Chunk8888
import ArealUK.Chunk8889
import ArealUK.Chunk8890
import ArealUK.Chunk8891
import ArealUK.Chunk8892
import ArealUK.Chunk8893
import ArealUK.Chunk8894
import ArealUK.Chunk8895
import ArealUK.Chunk8896
import ArealUK.Chunk8897
import ArealUK.Chunk8898
import ArealUK.Chunk8899
import Areal.UCert.LeavesKGen

/-! Group 88 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_88 : leavesOK ctxLitU 289425000000 2 ((leaves.drop 17600).take 200) 73150000000 0 = true := by
  have s99 := ArealUCore.ArealUK.chunk_8899
  have s98 : leavesOK ctxLitU 73125000000 0 ((leaves.drop 17796).take 4) 73150000000 0 = true :=
    take_step (n := 2) (t := 4) (b := 17798) rfl rfl ArealUCore.ArealUK.chunk_8898 s99
  have s97 : leavesOK ctxLitU 73112500000 0 ((leaves.drop 17794).take 6) 73150000000 0 = true :=
    take_step (n := 2) (t := 6) (b := 17796) rfl rfl ArealUCore.ArealUK.chunk_8897 s98
  have s96 : leavesOK ctxLitU 73100000000 0 ((leaves.drop 17792).take 8) 73150000000 0 = true :=
    take_step (n := 2) (t := 8) (b := 17794) rfl rfl ArealUCore.ArealUK.chunk_8896 s97
  have s95 : leavesOK ctxLitU 299391506103018 12 ((leaves.drop 17790).take 10) 73150000000 0 = true :=
    take_step (n := 2) (t := 10) (b := 17792) rfl rfl ArealUCore.ArealUK.chunk_8895 s96
  have s94 : leavesOK ctxLitU 73075000000 0 ((leaves.drop 17788).take 12) 73150000000 0 = true :=
    take_step (n := 2) (t := 12) (b := 17790) rfl rfl ArealUCore.ArealUK.chunk_8894 s95
  have s93 : leavesOK ctxLitU 73062500000 0 ((leaves.drop 17786).take 14) 73150000000 0 = true :=
    take_step (n := 2) (t := 14) (b := 17788) rfl rfl ArealUCore.ArealUK.chunk_8893 s94
  have s92 : leavesOK ctxLitU 73050000000 0 ((leaves.drop 17784).take 16) 73150000000 0 = true :=
    take_step (n := 2) (t := 16) (b := 17786) rfl rfl ArealUCore.ArealUK.chunk_8892 s93
  have s91 : leavesOK ctxLitU 73037500000 0 ((leaves.drop 17782).take 18) 73150000000 0 = true :=
    take_step (n := 2) (t := 18) (b := 17784) rfl rfl ArealUCore.ArealUK.chunk_8891 s92
  have s90 : leavesOK ctxLitU 73025000000 0 ((leaves.drop 17780).take 20) 73150000000 0 = true :=
    take_step (n := 2) (t := 20) (b := 17782) rfl rfl ArealUCore.ArealUK.chunk_8890 s91
  have s89 : leavesOK ctxLitU 73012500000 0 ((leaves.drop 17778).take 22) 73150000000 0 = true :=
    take_step (n := 2) (t := 22) (b := 17780) rfl rfl ArealUCore.ArealUK.chunk_8889 s90
  have s88 : leavesOK ctxLitU 146012500000 1 ((leaves.drop 17776).take 24) 73150000000 0 = true :=
    take_step (n := 2) (t := 24) (b := 17778) rfl rfl ArealUCore.ArealUK.chunk_8888 s89
  have s87 : leavesOK ctxLitU 292012500000 2 ((leaves.drop 17774).take 26) 73150000000 0 = true :=
    take_step (n := 2) (t := 26) (b := 17776) rfl rfl ArealUCore.ArealUK.chunk_8887 s88
  have s86 : leavesOK ctxLitU 145993750000 1 ((leaves.drop 17772).take 28) 73150000000 0 = true :=
    take_step (n := 2) (t := 28) (b := 17774) rfl rfl ArealUCore.ArealUK.chunk_8886 s87
  have s85 : leavesOK ctxLitU 72987500000 0 ((leaves.drop 17770).take 30) 73150000000 0 = true :=
    take_step (n := 2) (t := 30) (b := 17772) rfl rfl ArealUCore.ArealUK.chunk_8885 s86
  have s84 : leavesOK ctxLitU 72975000000 0 ((leaves.drop 17768).take 32) 73150000000 0 = true :=
    take_step (n := 2) (t := 32) (b := 17770) rfl rfl ArealUCore.ArealUK.chunk_8884 s85
  have s83 : leavesOK ctxLitU 291875000000 2 ((leaves.drop 17766).take 34) 73150000000 0 = true :=
    take_step (n := 2) (t := 34) (b := 17768) rfl rfl ArealUCore.ArealUK.chunk_8883 s84
  have s82 : leavesOK ctxLitU 291850000000 2 ((leaves.drop 17764).take 36) 73150000000 0 = true :=
    take_step (n := 2) (t := 36) (b := 17766) rfl rfl ArealUCore.ArealUK.chunk_8882 s83
  have s81 : leavesOK ctxLitU 291825000000 2 ((leaves.drop 17762).take 38) 73150000000 0 = true :=
    take_step (n := 2) (t := 38) (b := 17764) rfl rfl ArealUCore.ArealUK.chunk_8881 s82
  have s80 : leavesOK ctxLitU 291800000000 2 ((leaves.drop 17760).take 40) 73150000000 0 = true :=
    take_step (n := 2) (t := 40) (b := 17762) rfl rfl ArealUCore.ArealUK.chunk_8880 s81
  have s79 : leavesOK ctxLitU 583550000000 3 ((leaves.drop 17758).take 42) 73150000000 0 = true :=
    take_step (n := 2) (t := 42) (b := 17760) rfl rfl ArealUCore.ArealUK.chunk_8879 s80
  have s78 : leavesOK ctxLitU 583500000000 3 ((leaves.drop 17756).take 44) 73150000000 0 = true :=
    take_step (n := 2) (t := 44) (b := 17758) rfl rfl ArealUCore.ArealUK.chunk_8878 s79
  have s77 : leavesOK ctxLitU 583450000000 3 ((leaves.drop 17754).take 46) 73150000000 0 = true :=
    take_step (n := 2) (t := 46) (b := 17756) rfl rfl ArealUCore.ArealUK.chunk_8877 s78
  have s76 : leavesOK ctxLitU 583400000000 3 ((leaves.drop 17752).take 48) 73150000000 0 = true :=
    take_step (n := 2) (t := 48) (b := 17754) rfl rfl ArealUCore.ArealUK.chunk_8876 s77
  have s75 : leavesOK ctxLitU 583350000000 3 ((leaves.drop 17750).take 50) 73150000000 0 = true :=
    take_step (n := 2) (t := 50) (b := 17752) rfl rfl ArealUCore.ArealUK.chunk_8875 s76
  have s74 : leavesOK ctxLitU 583300000000 3 ((leaves.drop 17748).take 52) 73150000000 0 = true :=
    take_step (n := 2) (t := 52) (b := 17750) rfl rfl ArealUCore.ArealUK.chunk_8874 s75
  have s73 : leavesOK ctxLitU 583250000000 3 ((leaves.drop 17746).take 54) 73150000000 0 = true :=
    take_step (n := 2) (t := 54) (b := 17748) rfl rfl ArealUCore.ArealUK.chunk_8873 s74
  have s72 : leavesOK ctxLitU 583200000000 3 ((leaves.drop 17744).take 56) 73150000000 0 = true :=
    take_step (n := 2) (t := 56) (b := 17746) rfl rfl ArealUCore.ArealUK.chunk_8872 s73
  have s71 : leavesOK ctxLitU 583150000000 3 ((leaves.drop 17742).take 58) 73150000000 0 = true :=
    take_step (n := 2) (t := 58) (b := 17744) rfl rfl ArealUCore.ArealUK.chunk_8871 s72
  have s70 : leavesOK ctxLitU 583100000000 3 ((leaves.drop 17740).take 60) 73150000000 0 = true :=
    take_step (n := 2) (t := 60) (b := 17742) rfl rfl ArealUCore.ArealUK.chunk_8870 s71
  have s69 : leavesOK ctxLitU 291500000000 2 ((leaves.drop 17738).take 62) 73150000000 0 = true :=
    take_step (n := 2) (t := 62) (b := 17740) rfl rfl ArealUCore.ArealUK.chunk_8869 s70
  have s68 : leavesOK ctxLitU 291450000000 2 ((leaves.drop 17736).take 64) 73150000000 0 = true :=
    take_step (n := 2) (t := 64) (b := 17738) rfl rfl ArealUCore.ArealUK.chunk_8868 s69
  have s67 : leavesOK ctxLitU 582850000000 3 ((leaves.drop 17734).take 66) 73150000000 0 = true :=
    take_step (n := 2) (t := 66) (b := 17736) rfl rfl ArealUCore.ArealUK.chunk_8867 s68
  have s66 : leavesOK ctxLitU 582800000000 3 ((leaves.drop 17732).take 68) 73150000000 0 = true :=
    take_step (n := 2) (t := 68) (b := 17734) rfl rfl ArealUCore.ArealUK.chunk_8866 s67
  have s65 : leavesOK ctxLitU 582750000000 3 ((leaves.drop 17730).take 70) 73150000000 0 = true :=
    take_step (n := 2) (t := 70) (b := 17732) rfl rfl ArealUCore.ArealUK.chunk_8865 s66
  have s64 : leavesOK ctxLitU 582700000000 3 ((leaves.drop 17728).take 72) 73150000000 0 = true :=
    take_step (n := 2) (t := 72) (b := 17730) rfl rfl ArealUCore.ArealUK.chunk_8864 s65
  have s63 : leavesOK ctxLitU 582650000000 3 ((leaves.drop 17726).take 74) 73150000000 0 = true :=
    take_step (n := 2) (t := 74) (b := 17728) rfl rfl ArealUCore.ArealUK.chunk_8863 s64
  have s62 : leavesOK ctxLitU 582600000000 3 ((leaves.drop 17724).take 76) 73150000000 0 = true :=
    take_step (n := 2) (t := 76) (b := 17726) rfl rfl ArealUCore.ArealUK.chunk_8862 s63
  have s61 : leavesOK ctxLitU 582550000000 3 ((leaves.drop 17722).take 78) 73150000000 0 = true :=
    take_step (n := 2) (t := 78) (b := 17724) rfl rfl ArealUCore.ArealUK.chunk_8861 s62
  have s60 : leavesOK ctxLitU 582500000000 3 ((leaves.drop 17720).take 80) 73150000000 0 = true :=
    take_step (n := 2) (t := 80) (b := 17722) rfl rfl ArealUCore.ArealUK.chunk_8860 s61
  have s59 : leavesOK ctxLitU 582450000000 3 ((leaves.drop 17718).take 82) 73150000000 0 = true :=
    take_step (n := 2) (t := 82) (b := 17720) rfl rfl ArealUCore.ArealUK.chunk_8859 s60
  have s58 : leavesOK ctxLitU 582400000000 3 ((leaves.drop 17716).take 84) 73150000000 0 = true :=
    take_step (n := 2) (t := 84) (b := 17718) rfl rfl ArealUCore.ArealUK.chunk_8858 s59
  have s57 : leavesOK ctxLitU 582350000000 3 ((leaves.drop 17714).take 86) 73150000000 0 = true :=
    take_step (n := 2) (t := 86) (b := 17716) rfl rfl ArealUCore.ArealUK.chunk_8857 s58
  have s56 : leavesOK ctxLitU 582300000000 3 ((leaves.drop 17712).take 88) 73150000000 0 = true :=
    take_step (n := 2) (t := 88) (b := 17714) rfl rfl ArealUCore.ArealUK.chunk_8856 s57
  have s55 : leavesOK ctxLitU 582250000000 3 ((leaves.drop 17710).take 90) 73150000000 0 = true :=
    take_step (n := 2) (t := 90) (b := 17712) rfl rfl ArealUCore.ArealUK.chunk_8855 s56
  have s54 : leavesOK ctxLitU 582200000000 3 ((leaves.drop 17708).take 92) 73150000000 0 = true :=
    take_step (n := 2) (t := 92) (b := 17710) rfl rfl ArealUCore.ArealUK.chunk_8854 s55
  have s53 : leavesOK ctxLitU 582150000000 3 ((leaves.drop 17706).take 94) 73150000000 0 = true :=
    take_step (n := 2) (t := 94) (b := 17708) rfl rfl ArealUCore.ArealUK.chunk_8853 s54
  have s52 : leavesOK ctxLitU 582100000000 3 ((leaves.drop 17704).take 96) 73150000000 0 = true :=
    take_step (n := 2) (t := 96) (b := 17706) rfl rfl ArealUCore.ArealUK.chunk_8852 s53
  have s51 : leavesOK ctxLitU 291000000000 2 ((leaves.drop 17702).take 98) 73150000000 0 = true :=
    take_step (n := 2) (t := 98) (b := 17704) rfl rfl ArealUCore.ArealUK.chunk_8851 s52
  have s50 : leavesOK ctxLitU 290950000000 2 ((leaves.drop 17700).take 100) 73150000000 0 = true :=
    take_step (n := 2) (t := 100) (b := 17702) rfl rfl ArealUCore.ArealUK.chunk_8850 s51
  have s49 : leavesOK ctxLitU 581850000000 3 ((leaves.drop 17698).take 102) 73150000000 0 = true :=
    take_step (n := 2) (t := 102) (b := 17700) rfl rfl ArealUCore.ArealUK.chunk_8849 s50
  have s48 : leavesOK ctxLitU 581800000000 3 ((leaves.drop 17696).take 104) 73150000000 0 = true :=
    take_step (n := 2) (t := 104) (b := 17698) rfl rfl ArealUCore.ArealUK.chunk_8848 s49
  have s47 : leavesOK ctxLitU 581750000000 3 ((leaves.drop 17694).take 106) 73150000000 0 = true :=
    take_step (n := 2) (t := 106) (b := 17696) rfl rfl ArealUCore.ArealUK.chunk_8847 s48
  have s46 : leavesOK ctxLitU 581700000000 3 ((leaves.drop 17692).take 108) 73150000000 0 = true :=
    take_step (n := 2) (t := 108) (b := 17694) rfl rfl ArealUCore.ArealUK.chunk_8846 s47
  have s45 : leavesOK ctxLitU 581650000000 3 ((leaves.drop 17690).take 110) 73150000000 0 = true :=
    take_step (n := 2) (t := 110) (b := 17692) rfl rfl ArealUCore.ArealUK.chunk_8845 s46
  have s44 : leavesOK ctxLitU 581600000000 3 ((leaves.drop 17688).take 112) 73150000000 0 = true :=
    take_step (n := 2) (t := 112) (b := 17690) rfl rfl ArealUCore.ArealUK.chunk_8844 s45
  have s43 : leavesOK ctxLitU 581550000000 3 ((leaves.drop 17686).take 114) 73150000000 0 = true :=
    take_step (n := 2) (t := 114) (b := 17688) rfl rfl ArealUCore.ArealUK.chunk_8843 s44
  have s42 : leavesOK ctxLitU 581500000000 3 ((leaves.drop 17684).take 116) 73150000000 0 = true :=
    take_step (n := 2) (t := 116) (b := 17686) rfl rfl ArealUCore.ArealUK.chunk_8842 s43
  have s41 : leavesOK ctxLitU 581450000000 3 ((leaves.drop 17682).take 118) 73150000000 0 = true :=
    take_step (n := 2) (t := 118) (b := 17684) rfl rfl ArealUCore.ArealUK.chunk_8841 s42
  have s40 : leavesOK ctxLitU 581400000000 3 ((leaves.drop 17680).take 120) 73150000000 0 = true :=
    take_step (n := 2) (t := 120) (b := 17682) rfl rfl ArealUCore.ArealUK.chunk_8840 s41
  have s39 : leavesOK ctxLitU 581350000000 3 ((leaves.drop 17678).take 122) 73150000000 0 = true :=
    take_step (n := 2) (t := 122) (b := 17680) rfl rfl ArealUCore.ArealUK.chunk_8839 s40
  have s38 : leavesOK ctxLitU 290625000000 2 ((leaves.drop 17676).take 124) 73150000000 0 = true :=
    take_step (n := 2) (t := 124) (b := 17678) rfl rfl ArealUCore.ArealUK.chunk_8838 s39
  have s37 : leavesOK ctxLitU 290575000000 2 ((leaves.drop 17674).take 126) 73150000000 0 = true :=
    take_step (n := 2) (t := 126) (b := 17676) rfl rfl ArealUCore.ArealUK.chunk_8837 s38
  have s36 : leavesOK ctxLitU 290525000000 2 ((leaves.drop 17672).take 128) 73150000000 0 = true :=
    take_step (n := 2) (t := 128) (b := 17674) rfl rfl ArealUCore.ArealUK.chunk_8836 s37
  have s35 : leavesOK ctxLitU 581000000000 3 ((leaves.drop 17670).take 130) 73150000000 0 = true :=
    take_step (n := 2) (t := 130) (b := 17672) rfl rfl ArealUCore.ArealUK.chunk_8835 s36
  have s34 : leavesOK ctxLitU 580950000000 3 ((leaves.drop 17668).take 132) 73150000000 0 = true :=
    take_step (n := 2) (t := 132) (b := 17670) rfl rfl ArealUCore.ArealUK.chunk_8834 s35
  have s33 : leavesOK ctxLitU 580900000000 3 ((leaves.drop 17666).take 134) 73150000000 0 = true :=
    take_step (n := 2) (t := 134) (b := 17668) rfl rfl ArealUCore.ArealUK.chunk_8833 s34
  have s32 : leavesOK ctxLitU 580850000000 3 ((leaves.drop 17664).take 136) 73150000000 0 = true :=
    take_step (n := 2) (t := 136) (b := 17666) rfl rfl ArealUCore.ArealUK.chunk_8832 s33
  have s31 : leavesOK ctxLitU 580800000000 3 ((leaves.drop 17662).take 138) 73150000000 0 = true :=
    take_step (n := 2) (t := 138) (b := 17664) rfl rfl ArealUCore.ArealUK.chunk_8831 s32
  have s30 : leavesOK ctxLitU 580750000000 3 ((leaves.drop 17660).take 140) 73150000000 0 = true :=
    take_step (n := 2) (t := 140) (b := 17662) rfl rfl ArealUCore.ArealUK.chunk_8830 s31
  have s29 : leavesOK ctxLitU 580700000000 3 ((leaves.drop 17658).take 142) 73150000000 0 = true :=
    take_step (n := 2) (t := 142) (b := 17660) rfl rfl ArealUCore.ArealUK.chunk_8829 s30
  have s28 : leavesOK ctxLitU 580650000000 3 ((leaves.drop 17656).take 144) 73150000000 0 = true :=
    take_step (n := 2) (t := 144) (b := 17658) rfl rfl ArealUCore.ArealUK.chunk_8828 s29
  have s27 : leavesOK ctxLitU 580600000000 3 ((leaves.drop 17654).take 146) 73150000000 0 = true :=
    take_step (n := 2) (t := 146) (b := 17656) rfl rfl ArealUCore.ArealUK.chunk_8827 s28
  have s26 : leavesOK ctxLitU 580550000000 3 ((leaves.drop 17652).take 148) 73150000000 0 = true :=
    take_step (n := 2) (t := 148) (b := 17654) rfl rfl ArealUCore.ArealUK.chunk_8826 s27
  have s25 : leavesOK ctxLitU 580500000000 3 ((leaves.drop 17650).take 150) 73150000000 0 = true :=
    take_step (n := 2) (t := 150) (b := 17652) rfl rfl ArealUCore.ArealUK.chunk_8825 s26
  have s24 : leavesOK ctxLitU 290200000000 2 ((leaves.drop 17648).take 152) 73150000000 0 = true :=
    take_step (n := 2) (t := 152) (b := 17650) rfl rfl ArealUCore.ArealUK.chunk_8824 s25
  have s23 : leavesOK ctxLitU 290150000000 2 ((leaves.drop 17646).take 154) 73150000000 0 = true :=
    take_step (n := 2) (t := 154) (b := 17648) rfl rfl ArealUCore.ArealUK.chunk_8823 s24
  have s22 : leavesOK ctxLitU 580225000000 3 ((leaves.drop 17644).take 156) 73150000000 0 = true :=
    take_step (n := 2) (t := 156) (b := 17646) rfl rfl ArealUCore.ArealUK.chunk_8822 s23
  have s21 : leavesOK ctxLitU 580175000000 3 ((leaves.drop 17642).take 158) 73150000000 0 = true :=
    take_step (n := 2) (t := 158) (b := 17644) rfl rfl ArealUCore.ArealUK.chunk_8821 s22
  have s20 : leavesOK ctxLitU 580125000000 3 ((leaves.drop 17640).take 160) 73150000000 0 = true :=
    take_step (n := 2) (t := 160) (b := 17642) rfl rfl ArealUCore.ArealUK.chunk_8820 s21
  have s19 : leavesOK ctxLitU 580075000000 3 ((leaves.drop 17638).take 162) 73150000000 0 = true :=
    take_step (n := 2) (t := 162) (b := 17640) rfl rfl ArealUCore.ArealUK.chunk_8819 s20
  have s18 : leavesOK ctxLitU 580025000000 3 ((leaves.drop 17636).take 164) 73150000000 0 = true :=
    take_step (n := 2) (t := 164) (b := 17638) rfl rfl ArealUCore.ArealUK.chunk_8818 s19
  have s17 : leavesOK ctxLitU 579975000000 3 ((leaves.drop 17634).take 166) 73150000000 0 = true :=
    take_step (n := 2) (t := 166) (b := 17636) rfl rfl ArealUCore.ArealUK.chunk_8817 s18
  have s16 : leavesOK ctxLitU 579925000000 3 ((leaves.drop 17632).take 168) 73150000000 0 = true :=
    take_step (n := 2) (t := 168) (b := 17634) rfl rfl ArealUCore.ArealUK.chunk_8816 s17
  have s15 : leavesOK ctxLitU 579875000000 3 ((leaves.drop 17630).take 170) 73150000000 0 = true :=
    take_step (n := 2) (t := 170) (b := 17632) rfl rfl ArealUCore.ArealUK.chunk_8815 s16
  have s14 : leavesOK ctxLitU 579825000000 3 ((leaves.drop 17628).take 172) 73150000000 0 = true :=
    take_step (n := 2) (t := 172) (b := 17630) rfl rfl ArealUCore.ArealUK.chunk_8814 s15
  have s13 : leavesOK ctxLitU 579775000000 3 ((leaves.drop 17626).take 174) 73150000000 0 = true :=
    take_step (n := 2) (t := 174) (b := 17628) rfl rfl ArealUCore.ArealUK.chunk_8813 s14
  have s12 : leavesOK ctxLitU 289850000000 2 ((leaves.drop 17624).take 176) 73150000000 0 = true :=
    take_step (n := 2) (t := 176) (b := 17626) rfl rfl ArealUCore.ArealUK.chunk_8812 s13
  have s11 : leavesOK ctxLitU 289800000000 2 ((leaves.drop 17622).take 178) 73150000000 0 = true :=
    take_step (n := 2) (t := 178) (b := 17624) rfl rfl ArealUCore.ArealUK.chunk_8811 s12
  have s10 : leavesOK ctxLitU 289750000000 2 ((leaves.drop 17620).take 180) 73150000000 0 = true :=
    take_step (n := 2) (t := 180) (b := 17622) rfl rfl ArealUCore.ArealUK.chunk_8810 s11
  have s9 : leavesOK ctxLitU 579425000000 3 ((leaves.drop 17618).take 182) 73150000000 0 = true :=
    take_step (n := 2) (t := 182) (b := 17620) rfl rfl ArealUCore.ArealUK.chunk_8809 s10
  have s8 : leavesOK ctxLitU 579375000000 3 ((leaves.drop 17616).take 184) 73150000000 0 = true :=
    take_step (n := 2) (t := 184) (b := 17618) rfl rfl ArealUCore.ArealUK.chunk_8808 s9
  have s7 : leavesOK ctxLitU 579325000000 3 ((leaves.drop 17614).take 186) 73150000000 0 = true :=
    take_step (n := 2) (t := 186) (b := 17616) rfl rfl ArealUCore.ArealUK.chunk_8807 s8
  have s6 : leavesOK ctxLitU 579275000000 3 ((leaves.drop 17612).take 188) 73150000000 0 = true :=
    take_step (n := 2) (t := 188) (b := 17614) rfl rfl ArealUCore.ArealUK.chunk_8806 s7
  have s5 : leavesOK ctxLitU 289600000000 2 ((leaves.drop 17610).take 190) 73150000000 0 = true :=
    take_step (n := 2) (t := 190) (b := 17612) rfl rfl ArealUCore.ArealUK.chunk_8805 s6
  have s4 : leavesOK ctxLitU 289550000000 2 ((leaves.drop 17608).take 192) 73150000000 0 = true :=
    take_step (n := 2) (t := 192) (b := 17610) rfl rfl ArealUCore.ArealUK.chunk_8804 s5
  have s3 : leavesOK ctxLitU 579050000000 3 ((leaves.drop 17606).take 194) 73150000000 0 = true :=
    take_step (n := 2) (t := 194) (b := 17608) rfl rfl ArealUCore.ArealUK.chunk_8803 s4
  have s2 : leavesOK ctxLitU 579000000000 3 ((leaves.drop 17604).take 196) 73150000000 0 = true :=
    take_step (n := 2) (t := 196) (b := 17606) rfl rfl ArealUCore.ArealUK.chunk_8802 s3
  have s1 : leavesOK ctxLitU 578950000000 3 ((leaves.drop 17602).take 198) 73150000000 0 = true :=
    take_step (n := 2) (t := 198) (b := 17604) rfl rfl ArealUCore.ArealUK.chunk_8801 s2
  have s0 : leavesOK ctxLitU 289425000000 2 ((leaves.drop 17600).take 200) 73150000000 0 = true :=
    take_step (n := 2) (t := 200) (b := 17602) rfl rfl ArealUCore.ArealUK.chunk_8800 s1
  exact s0

end Areal.UCert

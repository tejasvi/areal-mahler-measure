import ArealUK.Chunk5800
import ArealUK.Chunk5801
import ArealUK.Chunk5802
import ArealUK.Chunk5803
import ArealUK.Chunk5804
import ArealUK.Chunk5805
import ArealUK.Chunk5806
import ArealUK.Chunk5807
import ArealUK.Chunk5808
import ArealUK.Chunk5809
import ArealUK.Chunk5810
import ArealUK.Chunk5811
import ArealUK.Chunk5812
import ArealUK.Chunk5813
import ArealUK.Chunk5814
import ArealUK.Chunk5815
import ArealUK.Chunk5816
import ArealUK.Chunk5817
import ArealUK.Chunk5818
import ArealUK.Chunk5819
import ArealUK.Chunk5820
import ArealUK.Chunk5821
import ArealUK.Chunk5822
import ArealUK.Chunk5823
import ArealUK.Chunk5824
import ArealUK.Chunk5825
import ArealUK.Chunk5826
import ArealUK.Chunk5827
import ArealUK.Chunk5828
import ArealUK.Chunk5829
import ArealUK.Chunk5830
import ArealUK.Chunk5831
import ArealUK.Chunk5832
import ArealUK.Chunk5833
import ArealUK.Chunk5834
import ArealUK.Chunk5835
import ArealUK.Chunk5836
import ArealUK.Chunk5837
import ArealUK.Chunk5838
import ArealUK.Chunk5839
import ArealUK.Chunk5840
import ArealUK.Chunk5841
import ArealUK.Chunk5842
import ArealUK.Chunk5843
import ArealUK.Chunk5844
import ArealUK.Chunk5845
import ArealUK.Chunk5846
import ArealUK.Chunk5847
import ArealUK.Chunk5848
import ArealUK.Chunk5849
import ArealUK.Chunk5850
import ArealUK.Chunk5851
import ArealUK.Chunk5852
import ArealUK.Chunk5853
import ArealUK.Chunk5854
import ArealUK.Chunk5855
import ArealUK.Chunk5856
import ArealUK.Chunk5857
import ArealUK.Chunk5858
import ArealUK.Chunk5859
import ArealUK.Chunk5860
import ArealUK.Chunk5861
import ArealUK.Chunk5862
import ArealUK.Chunk5863
import ArealUK.Chunk5864
import ArealUK.Chunk5865
import ArealUK.Chunk5866
import ArealUK.Chunk5867
import ArealUK.Chunk5868
import ArealUK.Chunk5869
import ArealUK.Chunk5870
import ArealUK.Chunk5871
import ArealUK.Chunk5872
import ArealUK.Chunk5873
import ArealUK.Chunk5874
import ArealUK.Chunk5875
import ArealUK.Chunk5876
import ArealUK.Chunk5877
import ArealUK.Chunk5878
import ArealUK.Chunk5879
import ArealUK.Chunk5880
import ArealUK.Chunk5881
import ArealUK.Chunk5882
import ArealUK.Chunk5883
import ArealUK.Chunk5884
import ArealUK.Chunk5885
import ArealUK.Chunk5886
import ArealUK.Chunk5887
import ArealUK.Chunk5888
import ArealUK.Chunk5889
import ArealUK.Chunk5890
import ArealUK.Chunk5891
import ArealUK.Chunk5892
import ArealUK.Chunk5893
import ArealUK.Chunk5894
import ArealUK.Chunk5895
import ArealUK.Chunk5896
import ArealUK.Chunk5897
import ArealUK.Chunk5898
import ArealUK.Chunk5899
import Areal.UCert.LeavesKGen

/-! Group 58 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_58 : leavesOK ctxLitU 300700000000 3 ((leaves.drop 11600).take 200) 305500000000 3 = true := by
  have s99 := ArealUCore.ArealUK.chunk_5899
  have s98 : leavesOK ctxLitU 305400000000 3 ((leaves.drop 11796).take 4) 305500000000 3 = true :=
    take_step (n := 2) (t := 4) (b := 11798) rfl rfl ArealUCore.ArealUK.chunk_5898 s99
  have s97 : leavesOK ctxLitU 305350000000 3 ((leaves.drop 11794).take 6) 305500000000 3 = true :=
    take_step (n := 2) (t := 6) (b := 11796) rfl rfl ArealUCore.ArealUK.chunk_5897 s98
  have s96 : leavesOK ctxLitU 305300000000 3 ((leaves.drop 11792).take 8) 305500000000 3 = true :=
    take_step (n := 2) (t := 8) (b := 11794) rfl rfl ArealUCore.ArealUK.chunk_5896 s97
  have s95 : leavesOK ctxLitU 305250000000 3 ((leaves.drop 11790).take 10) 305500000000 3 = true :=
    take_step (n := 2) (t := 10) (b := 11792) rfl rfl ArealUCore.ArealUK.chunk_5895 s96
  have s94 : leavesOK ctxLitU 305200000000 3 ((leaves.drop 11788).take 12) 305500000000 3 = true :=
    take_step (n := 2) (t := 12) (b := 11790) rfl rfl ArealUCore.ArealUK.chunk_5894 s95
  have s93 : leavesOK ctxLitU 305150000000 3 ((leaves.drop 11786).take 14) 305500000000 3 = true :=
    take_step (n := 2) (t := 14) (b := 11788) rfl rfl ArealUCore.ArealUK.chunk_5893 s94
  have s92 : leavesOK ctxLitU 305100000000 3 ((leaves.drop 11784).take 16) 305500000000 3 = true :=
    take_step (n := 2) (t := 16) (b := 11786) rfl rfl ArealUCore.ArealUK.chunk_5892 s93
  have s91 : leavesOK ctxLitU 305050000000 3 ((leaves.drop 11782).take 18) 305500000000 3 = true :=
    take_step (n := 2) (t := 18) (b := 11784) rfl rfl ArealUCore.ArealUK.chunk_5891 s92
  have s90 : leavesOK ctxLitU 305000000000 3 ((leaves.drop 11780).take 20) 305500000000 3 = true :=
    take_step (n := 2) (t := 20) (b := 11782) rfl rfl ArealUCore.ArealUK.chunk_5890 s91
  have s89 : leavesOK ctxLitU 304950000000 3 ((leaves.drop 11778).take 22) 305500000000 3 = true :=
    take_step (n := 2) (t := 22) (b := 11780) rfl rfl ArealUCore.ArealUK.chunk_5889 s90
  have s88 : leavesOK ctxLitU 304900000000 3 ((leaves.drop 11776).take 24) 305500000000 3 = true :=
    take_step (n := 2) (t := 24) (b := 11778) rfl rfl ArealUCore.ArealUK.chunk_5888 s89
  have s87 : leavesOK ctxLitU 304850000000 3 ((leaves.drop 11774).take 26) 305500000000 3 = true :=
    take_step (n := 2) (t := 26) (b := 11776) rfl rfl ArealUCore.ArealUK.chunk_5887 s88
  have s86 : leavesOK ctxLitU 304800000000 3 ((leaves.drop 11772).take 28) 305500000000 3 = true :=
    take_step (n := 2) (t := 28) (b := 11774) rfl rfl ArealUCore.ArealUK.chunk_5886 s87
  have s85 : leavesOK ctxLitU 304750000000 3 ((leaves.drop 11770).take 30) 305500000000 3 = true :=
    take_step (n := 2) (t := 30) (b := 11772) rfl rfl ArealUCore.ArealUK.chunk_5885 s86
  have s84 : leavesOK ctxLitU 304700000000 3 ((leaves.drop 11768).take 32) 305500000000 3 = true :=
    take_step (n := 2) (t := 32) (b := 11770) rfl rfl ArealUCore.ArealUK.chunk_5884 s85
  have s83 : leavesOK ctxLitU 304650000000 3 ((leaves.drop 11766).take 34) 305500000000 3 = true :=
    take_step (n := 2) (t := 34) (b := 11768) rfl rfl ArealUCore.ArealUK.chunk_5883 s84
  have s82 : leavesOK ctxLitU 304600000000 3 ((leaves.drop 11764).take 36) 305500000000 3 = true :=
    take_step (n := 2) (t := 36) (b := 11766) rfl rfl ArealUCore.ArealUK.chunk_5882 s83
  have s81 : leavesOK ctxLitU 304550000000 3 ((leaves.drop 11762).take 38) 305500000000 3 = true :=
    take_step (n := 2) (t := 38) (b := 11764) rfl rfl ArealUCore.ArealUK.chunk_5881 s82
  have s80 : leavesOK ctxLitU 304500000000 3 ((leaves.drop 11760).take 40) 305500000000 3 = true :=
    take_step (n := 2) (t := 40) (b := 11762) rfl rfl ArealUCore.ArealUK.chunk_5880 s81
  have s79 : leavesOK ctxLitU 304450000000 3 ((leaves.drop 11758).take 42) 305500000000 3 = true :=
    take_step (n := 2) (t := 42) (b := 11760) rfl rfl ArealUCore.ArealUK.chunk_5879 s80
  have s78 : leavesOK ctxLitU 304400000000 3 ((leaves.drop 11756).take 44) 305500000000 3 = true :=
    take_step (n := 2) (t := 44) (b := 11758) rfl rfl ArealUCore.ArealUK.chunk_5878 s79
  have s77 : leavesOK ctxLitU 304350000000 3 ((leaves.drop 11754).take 46) 305500000000 3 = true :=
    take_step (n := 2) (t := 46) (b := 11756) rfl rfl ArealUCore.ArealUK.chunk_5877 s78
  have s76 : leavesOK ctxLitU 304300000000 3 ((leaves.drop 11752).take 48) 305500000000 3 = true :=
    take_step (n := 2) (t := 48) (b := 11754) rfl rfl ArealUCore.ArealUK.chunk_5876 s77
  have s75 : leavesOK ctxLitU 304250000000 3 ((leaves.drop 11750).take 50) 305500000000 3 = true :=
    take_step (n := 2) (t := 50) (b := 11752) rfl rfl ArealUCore.ArealUK.chunk_5875 s76
  have s74 : leavesOK ctxLitU 304200000000 3 ((leaves.drop 11748).take 52) 305500000000 3 = true :=
    take_step (n := 2) (t := 52) (b := 11750) rfl rfl ArealUCore.ArealUK.chunk_5874 s75
  have s73 : leavesOK ctxLitU 304150000000 3 ((leaves.drop 11746).take 54) 305500000000 3 = true :=
    take_step (n := 2) (t := 54) (b := 11748) rfl rfl ArealUCore.ArealUK.chunk_5873 s74
  have s72 : leavesOK ctxLitU 304100000000 3 ((leaves.drop 11744).take 56) 305500000000 3 = true :=
    take_step (n := 2) (t := 56) (b := 11746) rfl rfl ArealUCore.ArealUK.chunk_5872 s73
  have s71 : leavesOK ctxLitU 304050000000 3 ((leaves.drop 11742).take 58) 305500000000 3 = true :=
    take_step (n := 2) (t := 58) (b := 11744) rfl rfl ArealUCore.ArealUK.chunk_5871 s72
  have s70 : leavesOK ctxLitU 304000000000 3 ((leaves.drop 11740).take 60) 305500000000 3 = true :=
    take_step (n := 2) (t := 60) (b := 11742) rfl rfl ArealUCore.ArealUK.chunk_5870 s71
  have s69 : leavesOK ctxLitU 303950000000 3 ((leaves.drop 11738).take 62) 305500000000 3 = true :=
    take_step (n := 2) (t := 62) (b := 11740) rfl rfl ArealUCore.ArealUK.chunk_5869 s70
  have s68 : leavesOK ctxLitU 303900000000 3 ((leaves.drop 11736).take 64) 305500000000 3 = true :=
    take_step (n := 2) (t := 64) (b := 11738) rfl rfl ArealUCore.ArealUK.chunk_5868 s69
  have s67 : leavesOK ctxLitU 303850000000 3 ((leaves.drop 11734).take 66) 305500000000 3 = true :=
    take_step (n := 2) (t := 66) (b := 11736) rfl rfl ArealUCore.ArealUK.chunk_5867 s68
  have s66 : leavesOK ctxLitU 303800000000 3 ((leaves.drop 11732).take 68) 305500000000 3 = true :=
    take_step (n := 2) (t := 68) (b := 11734) rfl rfl ArealUCore.ArealUK.chunk_5866 s67
  have s65 : leavesOK ctxLitU 303750000000 3 ((leaves.drop 11730).take 70) 305500000000 3 = true :=
    take_step (n := 2) (t := 70) (b := 11732) rfl rfl ArealUCore.ArealUK.chunk_5865 s66
  have s64 : leavesOK ctxLitU 303700000000 3 ((leaves.drop 11728).take 72) 305500000000 3 = true :=
    take_step (n := 2) (t := 72) (b := 11730) rfl rfl ArealUCore.ArealUK.chunk_5864 s65
  have s63 : leavesOK ctxLitU 303650000000 3 ((leaves.drop 11726).take 74) 305500000000 3 = true :=
    take_step (n := 2) (t := 74) (b := 11728) rfl rfl ArealUCore.ArealUK.chunk_5863 s64
  have s62 : leavesOK ctxLitU 303600000000 3 ((leaves.drop 11724).take 76) 305500000000 3 = true :=
    take_step (n := 2) (t := 76) (b := 11726) rfl rfl ArealUCore.ArealUK.chunk_5862 s63
  have s61 : leavesOK ctxLitU 303550000000 3 ((leaves.drop 11722).take 78) 305500000000 3 = true :=
    take_step (n := 2) (t := 78) (b := 11724) rfl rfl ArealUCore.ArealUK.chunk_5861 s62
  have s60 : leavesOK ctxLitU 303500000000 3 ((leaves.drop 11720).take 80) 305500000000 3 = true :=
    take_step (n := 2) (t := 80) (b := 11722) rfl rfl ArealUCore.ArealUK.chunk_5860 s61
  have s59 : leavesOK ctxLitU 303450000000 3 ((leaves.drop 11718).take 82) 305500000000 3 = true :=
    take_step (n := 2) (t := 82) (b := 11720) rfl rfl ArealUCore.ArealUK.chunk_5859 s60
  have s58 : leavesOK ctxLitU 303400000000 3 ((leaves.drop 11716).take 84) 305500000000 3 = true :=
    take_step (n := 2) (t := 84) (b := 11718) rfl rfl ArealUCore.ArealUK.chunk_5858 s59
  have s57 : leavesOK ctxLitU 303350000000 3 ((leaves.drop 11714).take 86) 305500000000 3 = true :=
    take_step (n := 2) (t := 86) (b := 11716) rfl rfl ArealUCore.ArealUK.chunk_5857 s58
  have s56 : leavesOK ctxLitU 303300000000 3 ((leaves.drop 11712).take 88) 305500000000 3 = true :=
    take_step (n := 2) (t := 88) (b := 11714) rfl rfl ArealUCore.ArealUK.chunk_5856 s57
  have s55 : leavesOK ctxLitU 303250000000 3 ((leaves.drop 11710).take 90) 305500000000 3 = true :=
    take_step (n := 2) (t := 90) (b := 11712) rfl rfl ArealUCore.ArealUK.chunk_5855 s56
  have s54 : leavesOK ctxLitU 303200000000 3 ((leaves.drop 11708).take 92) 305500000000 3 = true :=
    take_step (n := 2) (t := 92) (b := 11710) rfl rfl ArealUCore.ArealUK.chunk_5854 s55
  have s53 : leavesOK ctxLitU 303150000000 3 ((leaves.drop 11706).take 94) 305500000000 3 = true :=
    take_step (n := 2) (t := 94) (b := 11708) rfl rfl ArealUCore.ArealUK.chunk_5853 s54
  have s52 : leavesOK ctxLitU 303100000000 3 ((leaves.drop 11704).take 96) 305500000000 3 = true :=
    take_step (n := 2) (t := 96) (b := 11706) rfl rfl ArealUCore.ArealUK.chunk_5852 s53
  have s51 : leavesOK ctxLitU 303050000000 3 ((leaves.drop 11702).take 98) 305500000000 3 = true :=
    take_step (n := 2) (t := 98) (b := 11704) rfl rfl ArealUCore.ArealUK.chunk_5851 s52
  have s50 : leavesOK ctxLitU 303000000000 3 ((leaves.drop 11700).take 100) 305500000000 3 = true :=
    take_step (n := 2) (t := 100) (b := 11702) rfl rfl ArealUCore.ArealUK.chunk_5850 s51
  have s49 : leavesOK ctxLitU 302950000000 3 ((leaves.drop 11698).take 102) 305500000000 3 = true :=
    take_step (n := 2) (t := 102) (b := 11700) rfl rfl ArealUCore.ArealUK.chunk_5849 s50
  have s48 : leavesOK ctxLitU 302900000000 3 ((leaves.drop 11696).take 104) 305500000000 3 = true :=
    take_step (n := 2) (t := 104) (b := 11698) rfl rfl ArealUCore.ArealUK.chunk_5848 s49
  have s47 : leavesOK ctxLitU 302850000000 3 ((leaves.drop 11694).take 106) 305500000000 3 = true :=
    take_step (n := 2) (t := 106) (b := 11696) rfl rfl ArealUCore.ArealUK.chunk_5847 s48
  have s46 : leavesOK ctxLitU 302800000000 3 ((leaves.drop 11692).take 108) 305500000000 3 = true :=
    take_step (n := 2) (t := 108) (b := 11694) rfl rfl ArealUCore.ArealUK.chunk_5846 s47
  have s45 : leavesOK ctxLitU 605550000000 4 ((leaves.drop 11690).take 110) 305500000000 3 = true :=
    take_step (n := 2) (t := 110) (b := 11692) rfl rfl ArealUCore.ArealUK.chunk_5845 s46
  have s44 : leavesOK ctxLitU 605500000000 4 ((leaves.drop 11688).take 112) 305500000000 3 = true :=
    take_step (n := 2) (t := 112) (b := 11690) rfl rfl ArealUCore.ArealUK.chunk_5844 s45
  have s43 : leavesOK ctxLitU 605450000000 4 ((leaves.drop 11686).take 114) 305500000000 3 = true :=
    take_step (n := 2) (t := 114) (b := 11688) rfl rfl ArealUCore.ArealUK.chunk_5843 s44
  have s42 : leavesOK ctxLitU 605400000000 4 ((leaves.drop 11684).take 116) 305500000000 3 = true :=
    take_step (n := 2) (t := 116) (b := 11686) rfl rfl ArealUCore.ArealUK.chunk_5842 s43
  have s41 : leavesOK ctxLitU 302650000000 3 ((leaves.drop 11682).take 118) 305500000000 3 = true :=
    take_step (n := 2) (t := 118) (b := 11684) rfl rfl ArealUCore.ArealUK.chunk_5841 s42
  have s40 : leavesOK ctxLitU 302600000000 3 ((leaves.drop 11680).take 120) 305500000000 3 = true :=
    take_step (n := 2) (t := 120) (b := 11682) rfl rfl ArealUCore.ArealUK.chunk_5840 s41
  have s39 : leavesOK ctxLitU 302550000000 3 ((leaves.drop 11678).take 122) 305500000000 3 = true :=
    take_step (n := 2) (t := 122) (b := 11680) rfl rfl ArealUCore.ArealUK.chunk_5839 s40
  have s38 : leavesOK ctxLitU 302500000000 3 ((leaves.drop 11676).take 124) 305500000000 3 = true :=
    take_step (n := 2) (t := 124) (b := 11678) rfl rfl ArealUCore.ArealUK.chunk_5838 s39
  have s37 : leavesOK ctxLitU 302450000000 3 ((leaves.drop 11674).take 126) 305500000000 3 = true :=
    take_step (n := 2) (t := 126) (b := 11676) rfl rfl ArealUCore.ArealUK.chunk_5837 s38
  have s36 : leavesOK ctxLitU 302400000000 3 ((leaves.drop 11672).take 128) 305500000000 3 = true :=
    take_step (n := 2) (t := 128) (b := 11674) rfl rfl ArealUCore.ArealUK.chunk_5836 s37
  have s35 : leavesOK ctxLitU 302350000000 3 ((leaves.drop 11670).take 130) 305500000000 3 = true :=
    take_step (n := 2) (t := 130) (b := 11672) rfl rfl ArealUCore.ArealUK.chunk_5835 s36
  have s34 : leavesOK ctxLitU 302300000000 3 ((leaves.drop 11668).take 132) 305500000000 3 = true :=
    take_step (n := 2) (t := 132) (b := 11670) rfl rfl ArealUCore.ArealUK.chunk_5834 s35
  have s33 : leavesOK ctxLitU 302250000000 3 ((leaves.drop 11666).take 134) 305500000000 3 = true :=
    take_step (n := 2) (t := 134) (b := 11668) rfl rfl ArealUCore.ArealUK.chunk_5833 s34
  have s32 : leavesOK ctxLitU 302200000000 3 ((leaves.drop 11664).take 136) 305500000000 3 = true :=
    take_step (n := 2) (t := 136) (b := 11666) rfl rfl ArealUCore.ArealUK.chunk_5832 s33
  have s31 : leavesOK ctxLitU 302150000000 3 ((leaves.drop 11662).take 138) 305500000000 3 = true :=
    take_step (n := 2) (t := 138) (b := 11664) rfl rfl ArealUCore.ArealUK.chunk_5831 s32
  have s30 : leavesOK ctxLitU 302100000000 3 ((leaves.drop 11660).take 140) 305500000000 3 = true :=
    take_step (n := 2) (t := 140) (b := 11662) rfl rfl ArealUCore.ArealUK.chunk_5830 s31
  have s29 : leavesOK ctxLitU 302050000000 3 ((leaves.drop 11658).take 142) 305500000000 3 = true :=
    take_step (n := 2) (t := 142) (b := 11660) rfl rfl ArealUCore.ArealUK.chunk_5829 s30
  have s28 : leavesOK ctxLitU 302000000000 3 ((leaves.drop 11656).take 144) 305500000000 3 = true :=
    take_step (n := 2) (t := 144) (b := 11658) rfl rfl ArealUCore.ArealUK.chunk_5828 s29
  have s27 : leavesOK ctxLitU 301950000000 3 ((leaves.drop 11654).take 146) 305500000000 3 = true :=
    take_step (n := 2) (t := 146) (b := 11656) rfl rfl ArealUCore.ArealUK.chunk_5827 s28
  have s26 : leavesOK ctxLitU 301900000000 3 ((leaves.drop 11652).take 148) 305500000000 3 = true :=
    take_step (n := 2) (t := 148) (b := 11654) rfl rfl ArealUCore.ArealUK.chunk_5826 s27
  have s25 : leavesOK ctxLitU 301850000000 3 ((leaves.drop 11650).take 150) 305500000000 3 = true :=
    take_step (n := 2) (t := 150) (b := 11652) rfl rfl ArealUCore.ArealUK.chunk_5825 s26
  have s24 : leavesOK ctxLitU 301800000000 3 ((leaves.drop 11648).take 152) 305500000000 3 = true :=
    take_step (n := 2) (t := 152) (b := 11650) rfl rfl ArealUCore.ArealUK.chunk_5824 s25
  have s23 : leavesOK ctxLitU 301750000000 3 ((leaves.drop 11646).take 154) 305500000000 3 = true :=
    take_step (n := 2) (t := 154) (b := 11648) rfl rfl ArealUCore.ArealUK.chunk_5823 s24
  have s22 : leavesOK ctxLitU 301700000000 3 ((leaves.drop 11644).take 156) 305500000000 3 = true :=
    take_step (n := 2) (t := 156) (b := 11646) rfl rfl ArealUCore.ArealUK.chunk_5822 s23
  have s21 : leavesOK ctxLitU 301650000000 3 ((leaves.drop 11642).take 158) 305500000000 3 = true :=
    take_step (n := 2) (t := 158) (b := 11644) rfl rfl ArealUCore.ArealUK.chunk_5821 s22
  have s20 : leavesOK ctxLitU 301600000000 3 ((leaves.drop 11640).take 160) 305500000000 3 = true :=
    take_step (n := 2) (t := 160) (b := 11642) rfl rfl ArealUCore.ArealUK.chunk_5820 s21
  have s19 : leavesOK ctxLitU 301550000000 3 ((leaves.drop 11638).take 162) 305500000000 3 = true :=
    take_step (n := 2) (t := 162) (b := 11640) rfl rfl ArealUCore.ArealUK.chunk_5819 s20
  have s18 : leavesOK ctxLitU 301500000000 3 ((leaves.drop 11636).take 164) 305500000000 3 = true :=
    take_step (n := 2) (t := 164) (b := 11638) rfl rfl ArealUCore.ArealUK.chunk_5818 s19
  have s17 : leavesOK ctxLitU 301450000000 3 ((leaves.drop 11634).take 166) 305500000000 3 = true :=
    take_step (n := 2) (t := 166) (b := 11636) rfl rfl ArealUCore.ArealUK.chunk_5817 s18
  have s16 : leavesOK ctxLitU 301400000000 3 ((leaves.drop 11632).take 168) 305500000000 3 = true :=
    take_step (n := 2) (t := 168) (b := 11634) rfl rfl ArealUCore.ArealUK.chunk_5816 s17
  have s15 : leavesOK ctxLitU 301350000000 3 ((leaves.drop 11630).take 170) 305500000000 3 = true :=
    take_step (n := 2) (t := 170) (b := 11632) rfl rfl ArealUCore.ArealUK.chunk_5815 s16
  have s14 : leavesOK ctxLitU 301300000000 3 ((leaves.drop 11628).take 172) 305500000000 3 = true :=
    take_step (n := 2) (t := 172) (b := 11630) rfl rfl ArealUCore.ArealUK.chunk_5814 s15
  have s13 : leavesOK ctxLitU 301250000000 3 ((leaves.drop 11626).take 174) 305500000000 3 = true :=
    take_step (n := 2) (t := 174) (b := 11628) rfl rfl ArealUCore.ArealUK.chunk_5813 s14
  have s12 : leavesOK ctxLitU 301200000000 3 ((leaves.drop 11624).take 176) 305500000000 3 = true :=
    take_step (n := 2) (t := 176) (b := 11626) rfl rfl ArealUCore.ArealUK.chunk_5812 s13
  have s11 : leavesOK ctxLitU 602350000000 4 ((leaves.drop 11622).take 178) 305500000000 3 = true :=
    take_step (n := 2) (t := 178) (b := 11624) rfl rfl ArealUCore.ArealUK.chunk_5811 s12
  have s10 : leavesOK ctxLitU 602300000000 4 ((leaves.drop 11620).take 180) 305500000000 3 = true :=
    take_step (n := 2) (t := 180) (b := 11622) rfl rfl ArealUCore.ArealUK.chunk_5810 s11
  have s9 : leavesOK ctxLitU 602250000000 4 ((leaves.drop 11618).take 182) 305500000000 3 = true :=
    take_step (n := 2) (t := 182) (b := 11620) rfl rfl ArealUCore.ArealUK.chunk_5809 s10
  have s8 : leavesOK ctxLitU 602200000000 4 ((leaves.drop 11616).take 184) 305500000000 3 = true :=
    take_step (n := 2) (t := 184) (b := 11618) rfl rfl ArealUCore.ArealUK.chunk_5808 s9
  have s7 : leavesOK ctxLitU 301050000000 3 ((leaves.drop 11614).take 186) 305500000000 3 = true :=
    take_step (n := 2) (t := 186) (b := 11616) rfl rfl ArealUCore.ArealUK.chunk_5807 s8
  have s6 : leavesOK ctxLitU 301000000000 3 ((leaves.drop 11612).take 188) 305500000000 3 = true :=
    take_step (n := 2) (t := 188) (b := 11614) rfl rfl ArealUCore.ArealUK.chunk_5806 s7
  have s5 : leavesOK ctxLitU 300950000000 3 ((leaves.drop 11610).take 190) 305500000000 3 = true :=
    take_step (n := 2) (t := 190) (b := 11612) rfl rfl ArealUCore.ArealUK.chunk_5805 s6
  have s4 : leavesOK ctxLitU 300900000000 3 ((leaves.drop 11608).take 192) 305500000000 3 = true :=
    take_step (n := 2) (t := 192) (b := 11610) rfl rfl ArealUCore.ArealUK.chunk_5804 s5
  have s3 : leavesOK ctxLitU 300850000000 3 ((leaves.drop 11606).take 194) 305500000000 3 = true :=
    take_step (n := 2) (t := 194) (b := 11608) rfl rfl ArealUCore.ArealUK.chunk_5803 s4
  have s2 : leavesOK ctxLitU 300800000000 3 ((leaves.drop 11604).take 196) 305500000000 3 = true :=
    take_step (n := 2) (t := 196) (b := 11606) rfl rfl ArealUCore.ArealUK.chunk_5802 s3
  have s1 : leavesOK ctxLitU 300750000000 3 ((leaves.drop 11602).take 198) 305500000000 3 = true :=
    take_step (n := 2) (t := 198) (b := 11604) rfl rfl ArealUCore.ArealUK.chunk_5801 s2
  have s0 : leavesOK ctxLitU 300700000000 3 ((leaves.drop 11600).take 200) 305500000000 3 = true :=
    take_step (n := 2) (t := 200) (b := 11602) rfl rfl ArealUCore.ArealUK.chunk_5800 s1
  exact s0

end Areal.UCert

import ArealUK.Chunk13800
import ArealUK.Chunk13801
import ArealUK.Chunk13802
import ArealUK.Chunk13803
import ArealUK.Chunk13804
import ArealUK.Chunk13805
import ArealUK.Chunk13806
import ArealUK.Chunk13807
import ArealUK.Chunk13808
import ArealUK.Chunk13809
import ArealUK.Chunk13810
import ArealUK.Chunk13811
import ArealUK.Chunk13812
import ArealUK.Chunk13813
import ArealUK.Chunk13814
import ArealUK.Chunk13815
import ArealUK.Chunk13816
import ArealUK.Chunk13817
import ArealUK.Chunk13818
import ArealUK.Chunk13819
import ArealUK.Chunk13820
import ArealUK.Chunk13821
import ArealUK.Chunk13822
import ArealUK.Chunk13823
import ArealUK.Chunk13824
import ArealUK.Chunk13825
import ArealUK.Chunk13826
import ArealUK.Chunk13827
import ArealUK.Chunk13828
import ArealUK.Chunk13829
import ArealUK.Chunk13830
import ArealUK.Chunk13831
import ArealUK.Chunk13832
import ArealUK.Chunk13833
import ArealUK.Chunk13834
import ArealUK.Chunk13835
import ArealUK.Chunk13836
import ArealUK.Chunk13837
import ArealUK.Chunk13838
import ArealUK.Chunk13839
import ArealUK.Chunk13840
import ArealUK.Chunk13841
import ArealUK.Chunk13842
import ArealUK.Chunk13843
import ArealUK.Chunk13844
import ArealUK.Chunk13845
import ArealUK.Chunk13846
import ArealUK.Chunk13847
import ArealUK.Chunk13848
import ArealUK.Chunk13849
import ArealUK.Chunk13850
import ArealUK.Chunk13851
import ArealUK.Chunk13852
import ArealUK.Chunk13853
import ArealUK.Chunk13854
import ArealUK.Chunk13855
import ArealUK.Chunk13856
import ArealUK.Chunk13857
import ArealUK.Chunk13858
import ArealUK.Chunk13859
import ArealUK.Chunk13860
import ArealUK.Chunk13861
import ArealUK.Chunk13862
import ArealUK.Chunk13863
import ArealUK.Chunk13864
import ArealUK.Chunk13865
import ArealUK.Chunk13866
import ArealUK.Chunk13867
import ArealUK.Chunk13868
import ArealUK.Chunk13869
import ArealUK.Chunk13870
import ArealUK.Chunk13871
import ArealUK.Chunk13872
import ArealUK.Chunk13873
import ArealUK.Chunk13874
import ArealUK.Chunk13875
import ArealUK.Chunk13876
import ArealUK.Chunk13877
import ArealUK.Chunk13878
import ArealUK.Chunk13879
import ArealUK.Chunk13880
import ArealUK.Chunk13881
import ArealUK.Chunk13882
import ArealUK.Chunk13883
import ArealUK.Chunk13884
import ArealUK.Chunk13885
import ArealUK.Chunk13886
import ArealUK.Chunk13887
import ArealUK.Chunk13888
import ArealUK.Chunk13889
import ArealUK.Chunk13890
import ArealUK.Chunk13891
import ArealUK.Chunk13892
import ArealUK.Chunk13893
import ArealUK.Chunk13894
import ArealUK.Chunk13895
import ArealUK.Chunk13896
import ArealUK.Chunk13897
import ArealUK.Chunk13898
import ArealUK.Chunk13899
import Areal.UCert.LeavesKGen

/-! Group 138 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_138 : leavesOK ctxLitU 565925000000 2 ((leaves.drop 27600).take 200) 142650000000 0 = true := by
  have s99 := ArealUCore.ArealUK.chunk_13899
  have s98 : leavesOK ctxLitU 142625000000 0 ((leaves.drop 27796).take 4) 142650000000 0 = true :=
    take_step (n := 2) (t := 4) (b := 27798) rfl rfl ArealUCore.ArealUK.chunk_13898 s99
  have s97 : leavesOK ctxLitU 285225000000 1 ((leaves.drop 27794).take 6) 142650000000 0 = true :=
    take_step (n := 2) (t := 6) (b := 27796) rfl rfl ArealUCore.ArealUK.chunk_13897 s98
  have s96 : leavesOK ctxLitU 285200000000 1 ((leaves.drop 27792).take 8) 142650000000 0 = true :=
    take_step (n := 2) (t := 8) (b := 27794) rfl rfl ArealUCore.ArealUK.chunk_13896 s97
  have s95 : leavesOK ctxLitU 285175000000 1 ((leaves.drop 27790).take 10) 142650000000 0 = true :=
    take_step (n := 2) (t := 10) (b := 27792) rfl rfl ArealUCore.ArealUK.chunk_13895 s96
  have s94 : leavesOK ctxLitU 285150000000 1 ((leaves.drop 27788).take 12) 142650000000 0 = true :=
    take_step (n := 2) (t := 12) (b := 27790) rfl rfl ArealUCore.ArealUK.chunk_13894 s95
  have s93 : leavesOK ctxLitU 285137500000 1 ((leaves.drop 27786).take 14) 142650000000 0 = true :=
    take_step (n := 2) (t := 14) (b := 27788) rfl rfl ArealUCore.ArealUK.chunk_13893 s94
  have s92 : leavesOK ctxLitU 285125000000 1 ((leaves.drop 27784).take 16) 142650000000 0 = true :=
    take_step (n := 2) (t := 16) (b := 27786) rfl rfl ArealUCore.ArealUK.chunk_13892 s93
  have s91 : leavesOK ctxLitU 142550000000 0 ((leaves.drop 27782).take 18) 142650000000 0 = true :=
    take_step (n := 2) (t := 18) (b := 27784) rfl rfl ArealUCore.ArealUK.chunk_13891 s92
  have s90 : leavesOK ctxLitU 142537500000 0 ((leaves.drop 27780).take 20) 142650000000 0 = true :=
    take_step (n := 2) (t := 20) (b := 27782) rfl rfl ArealUCore.ArealUK.chunk_13890 s91
  have s89 : leavesOK ctxLitU 142525000000 0 ((leaves.drop 27778).take 22) 142650000000 0 = true :=
    take_step (n := 2) (t := 22) (b := 27780) rfl rfl ArealUCore.ArealUK.chunk_13889 s90
  have s88 : leavesOK ctxLitU 285025000000 1 ((leaves.drop 27776).take 24) 142650000000 0 = true :=
    take_step (n := 2) (t := 24) (b := 27778) rfl rfl ArealUCore.ArealUK.chunk_13888 s89
  have s87 : leavesOK ctxLitU 285000000000 1 ((leaves.drop 27774).take 26) 142650000000 0 = true :=
    take_step (n := 2) (t := 26) (b := 27776) rfl rfl ArealUCore.ArealUK.chunk_13887 s88
  have s86 : leavesOK ctxLitU 284975000000 1 ((leaves.drop 27772).take 28) 142650000000 0 = true :=
    take_step (n := 2) (t := 28) (b := 27774) rfl rfl ArealUCore.ArealUK.chunk_13886 s87
  have s85 : leavesOK ctxLitU 284950000000 1 ((leaves.drop 27770).take 30) 142650000000 0 = true :=
    take_step (n := 2) (t := 30) (b := 27772) rfl rfl ArealUCore.ArealUK.chunk_13885 s86
  have s84 : leavesOK ctxLitU 142462500000 0 ((leaves.drop 27768).take 32) 142650000000 0 = true :=
    take_step (n := 2) (t := 32) (b := 27770) rfl rfl ArealUCore.ArealUK.chunk_13884 s85
  have s83 : leavesOK ctxLitU 142450000000 0 ((leaves.drop 27766).take 34) 142650000000 0 = true :=
    take_step (n := 2) (t := 34) (b := 27768) rfl rfl ArealUCore.ArealUK.chunk_13883 s84
  have s82 : leavesOK ctxLitU 142437500000 0 ((leaves.drop 27764).take 36) 142650000000 0 = true :=
    take_step (n := 2) (t := 36) (b := 27766) rfl rfl ArealUCore.ArealUK.chunk_13882 s83
  have s81 : leavesOK ctxLitU 142425000000 0 ((leaves.drop 27762).take 38) 142650000000 0 = true :=
    take_step (n := 2) (t := 38) (b := 27764) rfl rfl ArealUCore.ArealUK.chunk_13881 s82
  have s80 : leavesOK ctxLitU 284825000000 1 ((leaves.drop 27760).take 40) 142650000000 0 = true :=
    take_step (n := 2) (t := 40) (b := 27762) rfl rfl ArealUCore.ArealUK.chunk_13880 s81
  have s79 : leavesOK ctxLitU 284800000000 1 ((leaves.drop 27758).take 42) 142650000000 0 = true :=
    take_step (n := 2) (t := 42) (b := 27760) rfl rfl ArealUCore.ArealUK.chunk_13879 s80
  have s78 : leavesOK ctxLitU 569550000000 2 ((leaves.drop 27756).take 44) 142650000000 0 = true :=
    take_step (n := 2) (t := 44) (b := 27758) rfl rfl ArealUCore.ArealUK.chunk_13878 s79
  have s77 : leavesOK ctxLitU 569500000000 2 ((leaves.drop 27754).take 46) 142650000000 0 = true :=
    take_step (n := 2) (t := 46) (b := 27756) rfl rfl ArealUCore.ArealUK.chunk_13877 s78
  have s76 : leavesOK ctxLitU 569450000000 2 ((leaves.drop 27752).take 48) 142650000000 0 = true :=
    take_step (n := 2) (t := 48) (b := 27754) rfl rfl ArealUCore.ArealUK.chunk_13876 s77
  have s75 : leavesOK ctxLitU 569400000000 2 ((leaves.drop 27750).take 50) 142650000000 0 = true :=
    take_step (n := 2) (t := 50) (b := 27752) rfl rfl ArealUCore.ArealUK.chunk_13875 s76
  have s74 : leavesOK ctxLitU 569350000000 2 ((leaves.drop 27748).take 52) 142650000000 0 = true :=
    take_step (n := 2) (t := 52) (b := 27750) rfl rfl ArealUCore.ArealUK.chunk_13874 s75
  have s73 : leavesOK ctxLitU 569300000000 2 ((leaves.drop 27746).take 54) 142650000000 0 = true :=
    take_step (n := 2) (t := 54) (b := 27748) rfl rfl ArealUCore.ArealUK.chunk_13873 s74
  have s72 : leavesOK ctxLitU 569250000000 2 ((leaves.drop 27744).take 56) 142650000000 0 = true :=
    take_step (n := 2) (t := 56) (b := 27746) rfl rfl ArealUCore.ArealUK.chunk_13872 s73
  have s71 : leavesOK ctxLitU 569200000000 2 ((leaves.drop 27742).take 58) 142650000000 0 = true :=
    take_step (n := 2) (t := 58) (b := 27744) rfl rfl ArealUCore.ArealUK.chunk_13871 s72
  have s70 : leavesOK ctxLitU 284575000000 1 ((leaves.drop 27740).take 60) 142650000000 0 = true :=
    take_step (n := 2) (t := 60) (b := 27742) rfl rfl ArealUCore.ArealUK.chunk_13870 s71
  have s69 : leavesOK ctxLitU 284550000000 1 ((leaves.drop 27738).take 62) 142650000000 0 = true :=
    take_step (n := 2) (t := 62) (b := 27740) rfl rfl ArealUCore.ArealUK.chunk_13869 s70
  have s68 : leavesOK ctxLitU 284537500000 1 ((leaves.drop 27736).take 64) 142650000000 0 = true :=
    take_step (n := 2) (t := 64) (b := 27738) rfl rfl ArealUCore.ArealUK.chunk_13868 s69
  have s67 : leavesOK ctxLitU 284525000000 1 ((leaves.drop 27734).take 66) 142650000000 0 = true :=
    take_step (n := 2) (t := 66) (b := 27736) rfl rfl ArealUCore.ArealUK.chunk_13867 s68
  have s66 : leavesOK ctxLitU 142250000000 0 ((leaves.drop 27732).take 68) 142650000000 0 = true :=
    take_step (n := 2) (t := 68) (b := 27734) rfl rfl ArealUCore.ArealUK.chunk_13866 s67
  have s65 : leavesOK ctxLitU 142237500000 0 ((leaves.drop 27730).take 70) 142650000000 0 = true :=
    take_step (n := 2) (t := 70) (b := 27732) rfl rfl ArealUCore.ArealUK.chunk_13865 s66
  have s64 : leavesOK ctxLitU 284462500000 1 ((leaves.drop 27728).take 72) 142650000000 0 = true :=
    take_step (n := 2) (t := 72) (b := 27730) rfl rfl ArealUCore.ArealUK.chunk_13864 s65
  have s63 : leavesOK ctxLitU 284450000000 1 ((leaves.drop 27726).take 74) 142650000000 0 = true :=
    take_step (n := 2) (t := 74) (b := 27728) rfl rfl ArealUCore.ArealUK.chunk_13863 s64
  have s62 : leavesOK ctxLitU 284425000000 1 ((leaves.drop 27724).take 76) 142650000000 0 = true :=
    take_step (n := 2) (t := 76) (b := 27726) rfl rfl ArealUCore.ArealUK.chunk_13862 s63
  have s61 : leavesOK ctxLitU 284400000000 1 ((leaves.drop 27722).take 78) 142650000000 0 = true :=
    take_step (n := 2) (t := 78) (b := 27724) rfl rfl ArealUCore.ArealUK.chunk_13861 s62
  have s60 : leavesOK ctxLitU 284375000000 1 ((leaves.drop 27720).take 80) 142650000000 0 = true :=
    take_step (n := 2) (t := 80) (b := 27722) rfl rfl ArealUCore.ArealUK.chunk_13860 s61
  have s59 : leavesOK ctxLitU 284350000000 1 ((leaves.drop 27718).take 82) 142650000000 0 = true :=
    take_step (n := 2) (t := 82) (b := 27720) rfl rfl ArealUCore.ArealUK.chunk_13859 s60
  have s58 : leavesOK ctxLitU 284337500000 1 ((leaves.drop 27716).take 84) 142650000000 0 = true :=
    take_step (n := 2) (t := 84) (b := 27718) rfl rfl ArealUCore.ArealUK.chunk_13858 s59
  have s57 : leavesOK ctxLitU 284325000000 1 ((leaves.drop 27714).take 86) 142650000000 0 = true :=
    take_step (n := 2) (t := 86) (b := 27716) rfl rfl ArealUCore.ArealUK.chunk_13857 s58
  have s56 : leavesOK ctxLitU 142150000000 0 ((leaves.drop 27712).take 88) 142650000000 0 = true :=
    take_step (n := 2) (t := 88) (b := 27714) rfl rfl ArealUCore.ArealUK.chunk_13856 s57
  have s55 : leavesOK ctxLitU 284275000000 1 ((leaves.drop 27710).take 90) 142650000000 0 = true :=
    take_step (n := 2) (t := 90) (b := 27712) rfl rfl ArealUCore.ArealUK.chunk_13855 s56
  have s54 : leavesOK ctxLitU 284250000000 1 ((leaves.drop 27708).take 92) 142650000000 0 = true :=
    take_step (n := 2) (t := 92) (b := 27710) rfl rfl ArealUCore.ArealUK.chunk_13854 s55
  have s53 : leavesOK ctxLitU 568450000000 2 ((leaves.drop 27706).take 94) 142650000000 0 = true :=
    take_step (n := 2) (t := 94) (b := 27708) rfl rfl ArealUCore.ArealUK.chunk_13853 s54
  have s52 : leavesOK ctxLitU 568400000000 2 ((leaves.drop 27704).take 96) 142650000000 0 = true :=
    take_step (n := 2) (t := 96) (b := 27706) rfl rfl ArealUCore.ArealUK.chunk_13852 s53
  have s51 : leavesOK ctxLitU 284175000000 1 ((leaves.drop 27702).take 98) 142650000000 0 = true :=
    take_step (n := 2) (t := 98) (b := 27704) rfl rfl ArealUCore.ArealUK.chunk_13851 s52
  have s50 : leavesOK ctxLitU 284150000000 1 ((leaves.drop 27700).take 100) 142650000000 0 = true :=
    take_step (n := 2) (t := 100) (b := 27702) rfl rfl ArealUCore.ArealUK.chunk_13850 s51
  have s49 : leavesOK ctxLitU 142062500000 0 ((leaves.drop 27698).take 102) 142650000000 0 = true :=
    take_step (n := 2) (t := 102) (b := 27700) rfl rfl ArealUCore.ArealUK.chunk_13849 s50
  have s48 : leavesOK ctxLitU 142050000000 0 ((leaves.drop 27696).take 104) 142650000000 0 = true :=
    take_step (n := 2) (t := 104) (b := 27698) rfl rfl ArealUCore.ArealUK.chunk_13848 s49
  have s47 : leavesOK ctxLitU 142037500000 0 ((leaves.drop 27694).take 106) 142650000000 0 = true :=
    take_step (n := 2) (t := 106) (b := 27696) rfl rfl ArealUCore.ArealUK.chunk_13847 s48
  have s46 : leavesOK ctxLitU 142025000000 0 ((leaves.drop 27692).take 108) 142650000000 0 = true :=
    take_step (n := 2) (t := 108) (b := 27694) rfl rfl ArealUCore.ArealUK.chunk_13846 s47
  have s45 : leavesOK ctxLitU 284025000000 1 ((leaves.drop 27690).take 110) 142650000000 0 = true :=
    take_step (n := 2) (t := 110) (b := 27692) rfl rfl ArealUCore.ArealUK.chunk_13845 s46
  have s44 : leavesOK ctxLitU 284000000000 1 ((leaves.drop 27688).take 112) 142650000000 0 = true :=
    take_step (n := 2) (t := 112) (b := 27690) rfl rfl ArealUCore.ArealUK.chunk_13844 s45
  have s43 : leavesOK ctxLitU 283975000000 1 ((leaves.drop 27686).take 114) 142650000000 0 = true :=
    take_step (n := 2) (t := 114) (b := 27688) rfl rfl ArealUCore.ArealUK.chunk_13843 s44
  have s42 : leavesOK ctxLitU 283950000000 1 ((leaves.drop 27684).take 116) 142650000000 0 = true :=
    take_step (n := 2) (t := 116) (b := 27686) rfl rfl ArealUCore.ArealUK.chunk_13842 s43
  have s41 : leavesOK ctxLitU 283937500000 1 ((leaves.drop 27682).take 118) 142650000000 0 = true :=
    take_step (n := 2) (t := 118) (b := 27684) rfl rfl ArealUCore.ArealUK.chunk_13841 s42
  have s40 : leavesOK ctxLitU 141956250000 0 ((leaves.drop 27680).take 120) 142650000000 0 = true :=
    take_step (n := 2) (t := 120) (b := 27682) rfl rfl ArealUCore.ArealUK.chunk_13840 s41
  have s39 : leavesOK ctxLitU 141943750000 0 ((leaves.drop 27678).take 122) 142650000000 0 = true :=
    take_step (n := 2) (t := 122) (b := 27680) rfl rfl ArealUCore.ArealUK.chunk_13839 s40
  have s38 : leavesOK ctxLitU 141931250000 0 ((leaves.drop 27676).take 124) 142650000000 0 = true :=
    take_step (n := 2) (t := 124) (b := 27678) rfl rfl ArealUCore.ArealUK.chunk_13838 s39
  have s37 : leavesOK ctxLitU 283837500000 1 ((leaves.drop 27674).take 126) 142650000000 0 = true :=
    take_step (n := 2) (t := 126) (b := 27676) rfl rfl ArealUCore.ArealUK.chunk_13837 s38
  have s36 : leavesOK ctxLitU 283812500000 1 ((leaves.drop 27672).take 128) 142650000000 0 = true :=
    take_step (n := 2) (t := 128) (b := 27674) rfl rfl ArealUCore.ArealUK.chunk_13836 s37
  have s35 : leavesOK ctxLitU 283787500000 1 ((leaves.drop 27670).take 130) 142650000000 0 = true :=
    take_step (n := 2) (t := 130) (b := 27672) rfl rfl ArealUCore.ArealUK.chunk_13835 s36
  have s34 : leavesOK ctxLitU 283762500000 1 ((leaves.drop 27668).take 132) 142650000000 0 = true :=
    take_step (n := 2) (t := 132) (b := 27670) rfl rfl ArealUCore.ArealUK.chunk_13834 s35
  have s33 : leavesOK ctxLitU 141868750000 0 ((leaves.drop 27666).take 134) 142650000000 0 = true :=
    take_step (n := 2) (t := 134) (b := 27668) rfl rfl ArealUCore.ArealUK.chunk_13833 s34
  have s32 : leavesOK ctxLitU 141856250000 0 ((leaves.drop 27664).take 136) 142650000000 0 = true :=
    take_step (n := 2) (t := 136) (b := 27666) rfl rfl ArealUCore.ArealUK.chunk_13832 s33
  have s31 : leavesOK ctxLitU 141843750000 0 ((leaves.drop 27662).take 138) 142650000000 0 = true :=
    take_step (n := 2) (t := 138) (b := 27664) rfl rfl ArealUCore.ArealUK.chunk_13831 s32
  have s30 : leavesOK ctxLitU 141831250000 0 ((leaves.drop 27660).take 140) 142650000000 0 = true :=
    take_step (n := 2) (t := 140) (b := 27662) rfl rfl ArealUCore.ArealUK.chunk_13830 s31
  have s29 : leavesOK ctxLitU 283637500000 1 ((leaves.drop 27658).take 142) 142650000000 0 = true :=
    take_step (n := 2) (t := 142) (b := 27660) rfl rfl ArealUCore.ArealUK.chunk_13829 s30
  have s28 : leavesOK ctxLitU 283612500000 1 ((leaves.drop 27656).take 144) 142650000000 0 = true :=
    take_step (n := 2) (t := 144) (b := 27658) rfl rfl ArealUCore.ArealUK.chunk_13828 s29
  have s27 : leavesOK ctxLitU 567175000000 2 ((leaves.drop 27654).take 146) 142650000000 0 = true :=
    take_step (n := 2) (t := 146) (b := 27656) rfl rfl ArealUCore.ArealUK.chunk_13827 s28
  have s26 : leavesOK ctxLitU 567125000000 2 ((leaves.drop 27652).take 148) 142650000000 0 = true :=
    take_step (n := 2) (t := 148) (b := 27654) rfl rfl ArealUCore.ArealUK.chunk_13826 s27
  have s25 : leavesOK ctxLitU 567075000000 2 ((leaves.drop 27650).take 150) 142650000000 0 = true :=
    take_step (n := 2) (t := 150) (b := 27652) rfl rfl ArealUCore.ArealUK.chunk_13825 s26
  have s24 : leavesOK ctxLitU 567025000000 2 ((leaves.drop 27648).take 152) 142650000000 0 = true :=
    take_step (n := 2) (t := 152) (b := 27650) rfl rfl ArealUCore.ArealUK.chunk_13824 s25
  have s23 : leavesOK ctxLitU 566975000000 2 ((leaves.drop 27646).take 154) 142650000000 0 = true :=
    take_step (n := 2) (t := 154) (b := 27648) rfl rfl ArealUCore.ArealUK.chunk_13823 s24
  have s22 : leavesOK ctxLitU 566925000000 2 ((leaves.drop 27644).take 156) 142650000000 0 = true :=
    take_step (n := 2) (t := 156) (b := 27646) rfl rfl ArealUCore.ArealUK.chunk_13822 s23
  have s21 : leavesOK ctxLitU 566875000000 2 ((leaves.drop 27642).take 158) 142650000000 0 = true :=
    take_step (n := 2) (t := 158) (b := 27644) rfl rfl ArealUCore.ArealUK.chunk_13821 s22
  have s20 : leavesOK ctxLitU 566825000000 2 ((leaves.drop 27640).take 160) 142650000000 0 = true :=
    take_step (n := 2) (t := 160) (b := 27642) rfl rfl ArealUCore.ArealUK.chunk_13820 s21
  have s19 : leavesOK ctxLitU 283387500000 1 ((leaves.drop 27638).take 162) 142650000000 0 = true :=
    take_step (n := 2) (t := 162) (b := 27640) rfl rfl ArealUCore.ArealUK.chunk_13819 s20
  have s18 : leavesOK ctxLitU 283362500000 1 ((leaves.drop 27636).take 164) 142650000000 0 = true :=
    take_step (n := 2) (t := 164) (b := 27638) rfl rfl ArealUCore.ArealUK.chunk_13818 s19
  have s17 : leavesOK ctxLitU 141668750000 0 ((leaves.drop 27634).take 166) 142650000000 0 = true :=
    take_step (n := 2) (t := 166) (b := 27636) rfl rfl ArealUCore.ArealUK.chunk_13817 s18
  have s16 : leavesOK ctxLitU 141656250000 0 ((leaves.drop 27632).take 168) 142650000000 0 = true :=
    take_step (n := 2) (t := 168) (b := 27634) rfl rfl ArealUCore.ArealUK.chunk_13816 s17
  have s15 : leavesOK ctxLitU 141643750000 0 ((leaves.drop 27630).take 170) 142650000000 0 = true :=
    take_step (n := 2) (t := 170) (b := 27632) rfl rfl ArealUCore.ArealUK.chunk_13815 s16
  have s14 : leavesOK ctxLitU 283268750000 1 ((leaves.drop 27628).take 172) 142650000000 0 = true :=
    take_step (n := 2) (t := 172) (b := 27630) rfl rfl ArealUCore.ArealUK.chunk_13814 s15
  have s13 : leavesOK ctxLitU 283256250000 1 ((leaves.drop 27626).take 174) 142650000000 0 = true :=
    take_step (n := 2) (t := 174) (b := 27628) rfl rfl ArealUCore.ArealUK.chunk_13813 s14
  have s12 : leavesOK ctxLitU 283237500000 1 ((leaves.drop 27624).take 176) 142650000000 0 = true :=
    take_step (n := 2) (t := 176) (b := 27626) rfl rfl ArealUCore.ArealUK.chunk_13812 s13
  have s11 : leavesOK ctxLitU 283212500000 1 ((leaves.drop 27622).take 178) 142650000000 0 = true :=
    take_step (n := 2) (t := 178) (b := 27624) rfl rfl ArealUCore.ArealUK.chunk_13811 s12
  have s10 : leavesOK ctxLitU 566375000000 2 ((leaves.drop 27620).take 180) 142650000000 0 = true :=
    take_step (n := 2) (t := 180) (b := 27622) rfl rfl ArealUCore.ArealUK.chunk_13810 s11
  have s9 : leavesOK ctxLitU 566325000000 2 ((leaves.drop 27618).take 182) 142650000000 0 = true :=
    take_step (n := 2) (t := 182) (b := 27620) rfl rfl ArealUCore.ArealUK.chunk_13809 s10
  have s8 : leavesOK ctxLitU 566275000000 2 ((leaves.drop 27616).take 184) 142650000000 0 = true :=
    take_step (n := 2) (t := 184) (b := 27618) rfl rfl ArealUCore.ArealUK.chunk_13808 s9
  have s7 : leavesOK ctxLitU 566225000000 2 ((leaves.drop 27614).take 186) 142650000000 0 = true :=
    take_step (n := 2) (t := 186) (b := 27616) rfl rfl ArealUCore.ArealUK.chunk_13807 s8
  have s6 : leavesOK ctxLitU 566175000000 2 ((leaves.drop 27612).take 188) 142650000000 0 = true :=
    take_step (n := 2) (t := 188) (b := 27614) rfl rfl ArealUCore.ArealUK.chunk_13806 s7
  have s5 : leavesOK ctxLitU 566125000000 2 ((leaves.drop 27610).take 190) 142650000000 0 = true :=
    take_step (n := 2) (t := 190) (b := 27612) rfl rfl ArealUCore.ArealUK.chunk_13805 s6
  have s4 : leavesOK ctxLitU 566075000000 2 ((leaves.drop 27608).take 192) 142650000000 0 = true :=
    take_step (n := 2) (t := 192) (b := 27610) rfl rfl ArealUCore.ArealUK.chunk_13804 s5
  have s3 : leavesOK ctxLitU 566025000000 2 ((leaves.drop 27606).take 194) 142650000000 0 = true :=
    take_step (n := 2) (t := 194) (b := 27608) rfl rfl ArealUCore.ArealUK.chunk_13803 s4
  have s2 : leavesOK ctxLitU 282987500000 1 ((leaves.drop 27604).take 196) 142650000000 0 = true :=
    take_step (n := 2) (t := 196) (b := 27606) rfl rfl ArealUCore.ArealUK.chunk_13802 s3
  have s1 : leavesOK ctxLitU 565950000000 2 ((leaves.drop 27602).take 198) 142650000000 0 = true :=
    take_step (n := 2) (t := 198) (b := 27604) rfl rfl ArealUCore.ArealUK.chunk_13801 s2
  have s0 : leavesOK ctxLitU 565925000000 2 ((leaves.drop 27600).take 200) 142650000000 0 = true :=
    take_step (n := 2) (t := 200) (b := 27602) rfl rfl ArealUCore.ArealUK.chunk_13800 s1
  exact s0

end Areal.UCert

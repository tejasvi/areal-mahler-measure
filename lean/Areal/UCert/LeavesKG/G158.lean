import ArealUK.Chunk15800
import ArealUK.Chunk15801
import ArealUK.Chunk15802
import ArealUK.Chunk15803
import ArealUK.Chunk15804
import ArealUK.Chunk15805
import ArealUK.Chunk15806
import ArealUK.Chunk15807
import ArealUK.Chunk15808
import ArealUK.Chunk15809
import ArealUK.Chunk15810
import ArealUK.Chunk15811
import ArealUK.Chunk15812
import ArealUK.Chunk15813
import ArealUK.Chunk15814
import ArealUK.Chunk15815
import ArealUK.Chunk15816
import ArealUK.Chunk15817
import ArealUK.Chunk15818
import ArealUK.Chunk15819
import ArealUK.Chunk15820
import ArealUK.Chunk15821
import ArealUK.Chunk15822
import ArealUK.Chunk15823
import ArealUK.Chunk15824
import ArealUK.Chunk15825
import ArealUK.Chunk15826
import ArealUK.Chunk15827
import ArealUK.Chunk15828
import ArealUK.Chunk15829
import ArealUK.Chunk15830
import ArealUK.Chunk15831
import ArealUK.Chunk15832
import ArealUK.Chunk15833
import ArealUK.Chunk15834
import ArealUK.Chunk15835
import ArealUK.Chunk15836
import ArealUK.Chunk15837
import ArealUK.Chunk15838
import ArealUK.Chunk15839
import ArealUK.Chunk15840
import ArealUK.Chunk15841
import ArealUK.Chunk15842
import ArealUK.Chunk15843
import ArealUK.Chunk15844
import ArealUK.Chunk15845
import ArealUK.Chunk15846
import ArealUK.Chunk15847
import ArealUK.Chunk15848
import ArealUK.Chunk15849
import ArealUK.Chunk15850
import ArealUK.Chunk15851
import ArealUK.Chunk15852
import ArealUK.Chunk15853
import ArealUK.Chunk15854
import ArealUK.Chunk15855
import ArealUK.Chunk15856
import ArealUK.Chunk15857
import ArealUK.Chunk15858
import ArealUK.Chunk15859
import ArealUK.Chunk15860
import ArealUK.Chunk15861
import ArealUK.Chunk15862
import ArealUK.Chunk15863
import ArealUK.Chunk15864
import ArealUK.Chunk15865
import ArealUK.Chunk15866
import ArealUK.Chunk15867
import ArealUK.Chunk15868
import ArealUK.Chunk15869
import ArealUK.Chunk15870
import ArealUK.Chunk15871
import ArealUK.Chunk15872
import ArealUK.Chunk15873
import ArealUK.Chunk15874
import ArealUK.Chunk15875
import ArealUK.Chunk15876
import ArealUK.Chunk15877
import ArealUK.Chunk15878
import ArealUK.Chunk15879
import ArealUK.Chunk15880
import ArealUK.Chunk15881
import ArealUK.Chunk15882
import ArealUK.Chunk15883
import ArealUK.Chunk15884
import ArealUK.Chunk15885
import ArealUK.Chunk15886
import ArealUK.Chunk15887
import ArealUK.Chunk15888
import ArealUK.Chunk15889
import ArealUK.Chunk15890
import ArealUK.Chunk15891
import ArealUK.Chunk15892
import ArealUK.Chunk15893
import ArealUK.Chunk15894
import ArealUK.Chunk15895
import ArealUK.Chunk15896
import ArealUK.Chunk15897
import ArealUK.Chunk15898
import ArealUK.Chunk15899
import Areal.UCert.LeavesKGen

/-! Group 158 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_158 : leavesOK ctxLitU 168168750000 0 ((leaves.drop 31600).take 200) 169625000000 0 = true := by
  have s99 := ArealUCore.ArealUK.chunk_15899
  have s98 : leavesOK ctxLitU 169575000000 0 ((leaves.drop 31796).take 4) 169625000000 0 = true :=
    take_step (n := 2) (t := 4) (b := 31798) rfl rfl ArealUCore.ArealUK.chunk_15898 s99
  have s97 : leavesOK ctxLitU 169562500000 0 ((leaves.drop 31794).take 6) 169625000000 0 = true :=
    take_step (n := 2) (t := 6) (b := 31796) rfl rfl ArealUCore.ArealUK.chunk_15897 s98
  have s96 : leavesOK ctxLitU 169550000000 0 ((leaves.drop 31792).take 8) 169625000000 0 = true :=
    take_step (n := 2) (t := 8) (b := 31794) rfl rfl ArealUCore.ArealUK.chunk_15896 s97
  have s95 : leavesOK ctxLitU 169537500000 0 ((leaves.drop 31790).take 10) 169625000000 0 = true :=
    take_step (n := 2) (t := 10) (b := 31792) rfl rfl ArealUCore.ArealUK.chunk_15895 s96
  have s94 : leavesOK ctxLitU 169525000000 0 ((leaves.drop 31788).take 12) 169625000000 0 = true :=
    take_step (n := 2) (t := 12) (b := 31790) rfl rfl ArealUCore.ArealUK.chunk_15894 s95
  have s93 : leavesOK ctxLitU 169500000000 0 ((leaves.drop 31786).take 14) 169625000000 0 = true :=
    take_step (n := 2) (t := 14) (b := 31788) rfl rfl ArealUCore.ArealUK.chunk_15893 s94
  have s92 : leavesOK ctxLitU 338975000000 1 ((leaves.drop 31784).take 16) 169625000000 0 = true :=
    take_step (n := 2) (t := 16) (b := 31786) rfl rfl ArealUCore.ArealUK.chunk_15892 s93
  have s91 : leavesOK ctxLitU 338950000000 1 ((leaves.drop 31782).take 18) 169625000000 0 = true :=
    take_step (n := 2) (t := 18) (b := 31784) rfl rfl ArealUCore.ArealUK.chunk_15891 s92
  have s90 : leavesOK ctxLitU 169462500000 0 ((leaves.drop 31780).take 20) 169625000000 0 = true :=
    take_step (n := 2) (t := 20) (b := 31782) rfl rfl ArealUCore.ArealUK.chunk_15890 s91
  have s89 : leavesOK ctxLitU 169450000000 0 ((leaves.drop 31778).take 22) 169625000000 0 = true :=
    take_step (n := 2) (t := 22) (b := 31780) rfl rfl ArealUCore.ArealUK.chunk_15889 s90
  have s88 : leavesOK ctxLitU 169437500000 0 ((leaves.drop 31776).take 24) 169625000000 0 = true :=
    take_step (n := 2) (t := 24) (b := 31778) rfl rfl ArealUCore.ArealUK.chunk_15888 s89
  have s87 : leavesOK ctxLitU 169425000000 0 ((leaves.drop 31774).take 26) 169625000000 0 = true :=
    take_step (n := 2) (t := 26) (b := 31776) rfl rfl ArealUCore.ArealUK.chunk_15887 s88
  have s86 : leavesOK ctxLitU 169412500000 0 ((leaves.drop 31772).take 28) 169625000000 0 = true :=
    take_step (n := 2) (t := 28) (b := 31774) rfl rfl ArealUCore.ArealUK.chunk_15886 s87
  have s85 : leavesOK ctxLitU 169400000000 0 ((leaves.drop 31770).take 30) 169625000000 0 = true :=
    take_step (n := 2) (t := 30) (b := 31772) rfl rfl ArealUCore.ArealUK.chunk_15885 s86
  have s84 : leavesOK ctxLitU 169375000000 0 ((leaves.drop 31768).take 32) 169625000000 0 = true :=
    take_step (n := 2) (t := 32) (b := 31770) rfl rfl ArealUCore.ArealUK.chunk_15884 s85
  have s83 : leavesOK ctxLitU 169362500000 0 ((leaves.drop 31766).take 34) 169625000000 0 = true :=
    take_step (n := 2) (t := 34) (b := 31768) rfl rfl ArealUCore.ArealUK.chunk_15883 s84
  have s82 : leavesOK ctxLitU 169350000000 0 ((leaves.drop 31764).take 36) 169625000000 0 = true :=
    take_step (n := 2) (t := 36) (b := 31766) rfl rfl ArealUCore.ArealUK.chunk_15882 s83
  have s81 : leavesOK ctxLitU 169337500000 0 ((leaves.drop 31762).take 38) 169625000000 0 = true :=
    take_step (n := 2) (t := 38) (b := 31764) rfl rfl ArealUCore.ArealUK.chunk_15881 s82
  have s80 : leavesOK ctxLitU 169325000000 0 ((leaves.drop 31760).take 40) 169625000000 0 = true :=
    take_step (n := 2) (t := 40) (b := 31762) rfl rfl ArealUCore.ArealUK.chunk_15880 s81
  have s79 : leavesOK ctxLitU 169300000000 0 ((leaves.drop 31758).take 42) 169625000000 0 = true :=
    take_step (n := 2) (t := 42) (b := 31760) rfl rfl ArealUCore.ArealUK.chunk_15879 s80
  have s78 : leavesOK ctxLitU 169287500000 0 ((leaves.drop 31756).take 44) 169625000000 0 = true :=
    take_step (n := 2) (t := 44) (b := 31758) rfl rfl ArealUCore.ArealUK.chunk_15878 s79
  have s77 : leavesOK ctxLitU 169275000000 0 ((leaves.drop 31754).take 46) 169625000000 0 = true :=
    take_step (n := 2) (t := 46) (b := 31756) rfl rfl ArealUCore.ArealUK.chunk_15877 s78
  have s76 : leavesOK ctxLitU 169262500000 0 ((leaves.drop 31752).take 48) 169625000000 0 = true :=
    take_step (n := 2) (t := 48) (b := 31754) rfl rfl ArealUCore.ArealUK.chunk_15876 s77
  have s75 : leavesOK ctxLitU 169250000000 0 ((leaves.drop 31750).take 50) 169625000000 0 = true :=
    take_step (n := 2) (t := 50) (b := 31752) rfl rfl ArealUCore.ArealUK.chunk_15875 s76
  have s74 : leavesOK ctxLitU 169225000000 0 ((leaves.drop 31748).take 52) 169625000000 0 = true :=
    take_step (n := 2) (t := 52) (b := 31750) rfl rfl ArealUCore.ArealUK.chunk_15874 s75
  have s73 : leavesOK ctxLitU 338400000000 1 ((leaves.drop 31746).take 54) 169625000000 0 = true :=
    take_step (n := 2) (t := 54) (b := 31748) rfl rfl ArealUCore.ArealUK.chunk_15873 s74
  have s72 : leavesOK ctxLitU 169175000000 0 ((leaves.drop 31744).take 56) 169625000000 0 = true :=
    take_step (n := 2) (t := 56) (b := 31746) rfl rfl ArealUCore.ArealUK.chunk_15872 s73
  have s71 : leavesOK ctxLitU 169162500000 0 ((leaves.drop 31742).take 58) 169625000000 0 = true :=
    take_step (n := 2) (t := 58) (b := 31744) rfl rfl ArealUCore.ArealUK.chunk_15871 s72
  have s70 : leavesOK ctxLitU 169150000000 0 ((leaves.drop 31740).take 60) 169625000000 0 = true :=
    take_step (n := 2) (t := 60) (b := 31742) rfl rfl ArealUCore.ArealUK.chunk_15870 s71
  have s69 : leavesOK ctxLitU 169137500000 0 ((leaves.drop 31738).take 62) 169625000000 0 = true :=
    take_step (n := 2) (t := 62) (b := 31740) rfl rfl ArealUCore.ArealUK.chunk_15869 s70
  have s68 : leavesOK ctxLitU 169125000000 0 ((leaves.drop 31736).take 64) 169625000000 0 = true :=
    take_step (n := 2) (t := 64) (b := 31738) rfl rfl ArealUCore.ArealUK.chunk_15868 s69
  have s67 : leavesOK ctxLitU 338212500000 1 ((leaves.drop 31734).take 66) 169625000000 0 = true :=
    take_step (n := 2) (t := 66) (b := 31736) rfl rfl ArealUCore.ArealUK.chunk_15867 s68
  have s66 : leavesOK ctxLitU 169087500000 0 ((leaves.drop 31732).take 68) 169625000000 0 = true :=
    take_step (n := 2) (t := 68) (b := 31734) rfl rfl ArealUCore.ArealUK.chunk_15866 s67
  have s65 : leavesOK ctxLitU 169068750000 0 ((leaves.drop 31730).take 70) 169625000000 0 = true :=
    take_step (n := 2) (t := 70) (b := 31732) rfl rfl ArealUCore.ArealUK.chunk_15865 s66
  have s64 : leavesOK ctxLitU 169056250000 0 ((leaves.drop 31728).take 72) 169625000000 0 = true :=
    take_step (n := 2) (t := 72) (b := 31730) rfl rfl ArealUCore.ArealUK.chunk_15864 s65
  have s63 : leavesOK ctxLitU 169043750000 0 ((leaves.drop 31726).take 74) 169625000000 0 = true :=
    take_step (n := 2) (t := 74) (b := 31728) rfl rfl ArealUCore.ArealUK.chunk_15863 s64
  have s62 : leavesOK ctxLitU 169031250000 0 ((leaves.drop 31724).take 76) 169625000000 0 = true :=
    take_step (n := 2) (t := 76) (b := 31726) rfl rfl ArealUCore.ArealUK.chunk_15862 s63
  have s61 : leavesOK ctxLitU 169018750000 0 ((leaves.drop 31722).take 78) 169625000000 0 = true :=
    take_step (n := 2) (t := 78) (b := 31724) rfl rfl ArealUCore.ArealUK.chunk_15861 s62
  have s60 : leavesOK ctxLitU 169006250000 0 ((leaves.drop 31720).take 80) 169625000000 0 = true :=
    take_step (n := 2) (t := 80) (b := 31722) rfl rfl ArealUCore.ArealUK.chunk_15860 s61
  have s59 : leavesOK ctxLitU 168993750000 0 ((leaves.drop 31718).take 82) 169625000000 0 = true :=
    take_step (n := 2) (t := 82) (b := 31720) rfl rfl ArealUCore.ArealUK.chunk_15859 s60
  have s58 : leavesOK ctxLitU 168981250000 0 ((leaves.drop 31716).take 84) 169625000000 0 = true :=
    take_step (n := 2) (t := 84) (b := 31718) rfl rfl ArealUCore.ArealUK.chunk_15858 s59
  have s57 : leavesOK ctxLitU 168968750000 0 ((leaves.drop 31714).take 86) 169625000000 0 = true :=
    take_step (n := 2) (t := 86) (b := 31716) rfl rfl ArealUCore.ArealUK.chunk_15857 s58
  have s56 : leavesOK ctxLitU 168956250000 0 ((leaves.drop 31712).take 88) 169625000000 0 = true :=
    take_step (n := 2) (t := 88) (b := 31714) rfl rfl ArealUCore.ArealUK.chunk_15856 s57
  have s55 : leavesOK ctxLitU 168943750000 0 ((leaves.drop 31710).take 90) 169625000000 0 = true :=
    take_step (n := 2) (t := 90) (b := 31712) rfl rfl ArealUCore.ArealUK.chunk_15855 s56
  have s54 : leavesOK ctxLitU 168931250000 0 ((leaves.drop 31708).take 92) 169625000000 0 = true :=
    take_step (n := 2) (t := 92) (b := 31710) rfl rfl ArealUCore.ArealUK.chunk_15854 s55
  have s53 : leavesOK ctxLitU 168912500000 0 ((leaves.drop 31706).take 94) 169625000000 0 = true :=
    take_step (n := 2) (t := 94) (b := 31708) rfl rfl ArealUCore.ArealUK.chunk_15853 s54
  have s52 : leavesOK ctxLitU 168887500000 0 ((leaves.drop 31704).take 96) 169625000000 0 = true :=
    take_step (n := 2) (t := 96) (b := 31706) rfl rfl ArealUCore.ArealUK.chunk_15852 s53
  have s51 : leavesOK ctxLitU 168868750000 0 ((leaves.drop 31702).take 98) 169625000000 0 = true :=
    take_step (n := 2) (t := 98) (b := 31704) rfl rfl ArealUCore.ArealUK.chunk_15851 s52
  have s50 : leavesOK ctxLitU 168856250000 0 ((leaves.drop 31700).take 100) 169625000000 0 = true :=
    take_step (n := 2) (t := 100) (b := 31702) rfl rfl ArealUCore.ArealUK.chunk_15850 s51
  have s49 : leavesOK ctxLitU 168843750000 0 ((leaves.drop 31698).take 102) 169625000000 0 = true :=
    take_step (n := 2) (t := 102) (b := 31700) rfl rfl ArealUCore.ArealUK.chunk_15849 s50
  have s48 : leavesOK ctxLitU 168831250000 0 ((leaves.drop 31696).take 104) 169625000000 0 = true :=
    take_step (n := 2) (t := 104) (b := 31698) rfl rfl ArealUCore.ArealUK.chunk_15848 s49
  have s47 : leavesOK ctxLitU 168818750000 0 ((leaves.drop 31694).take 106) 169625000000 0 = true :=
    take_step (n := 2) (t := 106) (b := 31696) rfl rfl ArealUCore.ArealUK.chunk_15847 s48
  have s46 : leavesOK ctxLitU 168806250000 0 ((leaves.drop 31692).take 108) 169625000000 0 = true :=
    take_step (n := 2) (t := 108) (b := 31694) rfl rfl ArealUCore.ArealUK.chunk_15846 s47
  have s45 : leavesOK ctxLitU 168793750000 0 ((leaves.drop 31690).take 110) 169625000000 0 = true :=
    take_step (n := 2) (t := 110) (b := 31692) rfl rfl ArealUCore.ArealUK.chunk_15845 s46
  have s44 : leavesOK ctxLitU 168781250000 0 ((leaves.drop 31688).take 112) 169625000000 0 = true :=
    take_step (n := 2) (t := 112) (b := 31690) rfl rfl ArealUCore.ArealUK.chunk_15844 s45
  have s43 : leavesOK ctxLitU 168768750000 0 ((leaves.drop 31686).take 114) 169625000000 0 = true :=
    take_step (n := 2) (t := 114) (b := 31688) rfl rfl ArealUCore.ArealUK.chunk_15843 s44
  have s42 : leavesOK ctxLitU 168756250000 0 ((leaves.drop 31684).take 116) 169625000000 0 = true :=
    take_step (n := 2) (t := 116) (b := 31686) rfl rfl ArealUCore.ArealUK.chunk_15842 s43
  have s41 : leavesOK ctxLitU 168743750000 0 ((leaves.drop 31682).take 118) 169625000000 0 = true :=
    take_step (n := 2) (t := 118) (b := 31684) rfl rfl ArealUCore.ArealUK.chunk_15841 s42
  have s40 : leavesOK ctxLitU 168731250000 0 ((leaves.drop 31680).take 120) 169625000000 0 = true :=
    take_step (n := 2) (t := 120) (b := 31682) rfl rfl ArealUCore.ArealUK.chunk_15840 s41
  have s39 : leavesOK ctxLitU 168718750000 0 ((leaves.drop 31678).take 122) 169625000000 0 = true :=
    take_step (n := 2) (t := 122) (b := 31680) rfl rfl ArealUCore.ArealUK.chunk_15839 s40
  have s38 : leavesOK ctxLitU 168706250000 0 ((leaves.drop 31676).take 124) 169625000000 0 = true :=
    take_step (n := 2) (t := 124) (b := 31678) rfl rfl ArealUCore.ArealUK.chunk_15838 s39
  have s37 : leavesOK ctxLitU 168693750000 0 ((leaves.drop 31674).take 126) 169625000000 0 = true :=
    take_step (n := 2) (t := 126) (b := 31676) rfl rfl ArealUCore.ArealUK.chunk_15837 s38
  have s36 : leavesOK ctxLitU 168681250000 0 ((leaves.drop 31672).take 128) 169625000000 0 = true :=
    take_step (n := 2) (t := 128) (b := 31674) rfl rfl ArealUCore.ArealUK.chunk_15836 s37
  have s35 : leavesOK ctxLitU 168668750000 0 ((leaves.drop 31670).take 130) 169625000000 0 = true :=
    take_step (n := 2) (t := 130) (b := 31672) rfl rfl ArealUCore.ArealUK.chunk_15835 s36
  have s34 : leavesOK ctxLitU 168656250000 0 ((leaves.drop 31668).take 132) 169625000000 0 = true :=
    take_step (n := 2) (t := 132) (b := 31670) rfl rfl ArealUCore.ArealUK.chunk_15834 s35
  have s33 : leavesOK ctxLitU 168643750000 0 ((leaves.drop 31666).take 134) 169625000000 0 = true :=
    take_step (n := 2) (t := 134) (b := 31668) rfl rfl ArealUCore.ArealUK.chunk_15833 s34
  have s32 : leavesOK ctxLitU 168631250000 0 ((leaves.drop 31664).take 136) 169625000000 0 = true :=
    take_step (n := 2) (t := 136) (b := 31666) rfl rfl ArealUCore.ArealUK.chunk_15832 s33
  have s31 : leavesOK ctxLitU 168618750000 0 ((leaves.drop 31662).take 138) 169625000000 0 = true :=
    take_step (n := 2) (t := 138) (b := 31664) rfl rfl ArealUCore.ArealUK.chunk_15831 s32
  have s30 : leavesOK ctxLitU 168606250000 0 ((leaves.drop 31660).take 140) 169625000000 0 = true :=
    take_step (n := 2) (t := 140) (b := 31662) rfl rfl ArealUCore.ArealUK.chunk_15830 s31
  have s29 : leavesOK ctxLitU 168587500000 0 ((leaves.drop 31658).take 142) 169625000000 0 = true :=
    take_step (n := 2) (t := 142) (b := 31660) rfl rfl ArealUCore.ArealUK.chunk_15829 s30
  have s28 : leavesOK ctxLitU 168568750000 0 ((leaves.drop 31656).take 144) 169625000000 0 = true :=
    take_step (n := 2) (t := 144) (b := 31658) rfl rfl ArealUCore.ArealUK.chunk_15828 s29
  have s27 : leavesOK ctxLitU 168556250000 0 ((leaves.drop 31654).take 146) 169625000000 0 = true :=
    take_step (n := 2) (t := 146) (b := 31656) rfl rfl ArealUCore.ArealUK.chunk_15827 s28
  have s26 : leavesOK ctxLitU 168543750000 0 ((leaves.drop 31652).take 148) 169625000000 0 = true :=
    take_step (n := 2) (t := 148) (b := 31654) rfl rfl ArealUCore.ArealUK.chunk_15826 s27
  have s25 : leavesOK ctxLitU 168531250000 0 ((leaves.drop 31650).take 150) 169625000000 0 = true :=
    take_step (n := 2) (t := 150) (b := 31652) rfl rfl ArealUCore.ArealUK.chunk_15825 s26
  have s24 : leavesOK ctxLitU 168512500000 0 ((leaves.drop 31648).take 152) 169625000000 0 = true :=
    take_step (n := 2) (t := 152) (b := 31650) rfl rfl ArealUCore.ArealUK.chunk_15824 s25
  have s23 : leavesOK ctxLitU 336987500000 1 ((leaves.drop 31646).take 154) 169625000000 0 = true :=
    take_step (n := 2) (t := 154) (b := 31648) rfl rfl ArealUCore.ArealUK.chunk_15823 s24
  have s22 : leavesOK ctxLitU 336962500000 1 ((leaves.drop 31644).take 156) 169625000000 0 = true :=
    take_step (n := 2) (t := 156) (b := 31646) rfl rfl ArealUCore.ArealUK.chunk_15822 s23
  have s21 : leavesOK ctxLitU 168468750000 0 ((leaves.drop 31642).take 158) 169625000000 0 = true :=
    take_step (n := 2) (t := 158) (b := 31644) rfl rfl ArealUCore.ArealUK.chunk_15821 s22
  have s20 : leavesOK ctxLitU 168456250000 0 ((leaves.drop 31640).take 160) 169625000000 0 = true :=
    take_step (n := 2) (t := 160) (b := 31642) rfl rfl ArealUCore.ArealUK.chunk_15820 s21
  have s19 : leavesOK ctxLitU 168443750000 0 ((leaves.drop 31638).take 162) 169625000000 0 = true :=
    take_step (n := 2) (t := 162) (b := 31640) rfl rfl ArealUCore.ArealUK.chunk_15819 s20
  have s18 : leavesOK ctxLitU 168431250000 0 ((leaves.drop 31636).take 164) 169625000000 0 = true :=
    take_step (n := 2) (t := 164) (b := 31638) rfl rfl ArealUCore.ArealUK.chunk_15818 s19
  have s17 : leavesOK ctxLitU 168418750000 0 ((leaves.drop 31634).take 166) 169625000000 0 = true :=
    take_step (n := 2) (t := 166) (b := 31636) rfl rfl ArealUCore.ArealUK.chunk_15817 s18
  have s16 : leavesOK ctxLitU 168406250000 0 ((leaves.drop 31632).take 168) 169625000000 0 = true :=
    take_step (n := 2) (t := 168) (b := 31634) rfl rfl ArealUCore.ArealUK.chunk_15816 s17
  have s15 : leavesOK ctxLitU 168387500000 0 ((leaves.drop 31630).take 170) 169625000000 0 = true :=
    take_step (n := 2) (t := 170) (b := 31632) rfl rfl ArealUCore.ArealUK.chunk_15815 s16
  have s14 : leavesOK ctxLitU 168362500000 0 ((leaves.drop 31628).take 172) 169625000000 0 = true :=
    take_step (n := 2) (t := 172) (b := 31630) rfl rfl ArealUCore.ArealUK.chunk_15814 s15
  have s13 : leavesOK ctxLitU 168343750000 0 ((leaves.drop 31626).take 174) 169625000000 0 = true :=
    take_step (n := 2) (t := 174) (b := 31628) rfl rfl ArealUCore.ArealUK.chunk_15813 s14
  have s12 : leavesOK ctxLitU 168331250000 0 ((leaves.drop 31624).take 176) 169625000000 0 = true :=
    take_step (n := 2) (t := 176) (b := 31626) rfl rfl ArealUCore.ArealUK.chunk_15812 s13
  have s11 : leavesOK ctxLitU 168318750000 0 ((leaves.drop 31622).take 178) 169625000000 0 = true :=
    take_step (n := 2) (t := 178) (b := 31624) rfl rfl ArealUCore.ArealUK.chunk_15811 s12
  have s10 : leavesOK ctxLitU 168306250000 0 ((leaves.drop 31620).take 180) 169625000000 0 = true :=
    take_step (n := 2) (t := 180) (b := 31622) rfl rfl ArealUCore.ArealUK.chunk_15810 s11
  have s9 : leavesOK ctxLitU 168293750000 0 ((leaves.drop 31618).take 182) 169625000000 0 = true :=
    take_step (n := 2) (t := 182) (b := 31620) rfl rfl ArealUCore.ArealUK.chunk_15809 s10
  have s8 : leavesOK ctxLitU 168281250000 0 ((leaves.drop 31616).take 184) 169625000000 0 = true :=
    take_step (n := 2) (t := 184) (b := 31618) rfl rfl ArealUCore.ArealUK.chunk_15808 s9
  have s7 : leavesOK ctxLitU 168268750000 0 ((leaves.drop 31614).take 186) 169625000000 0 = true :=
    take_step (n := 2) (t := 186) (b := 31616) rfl rfl ArealUCore.ArealUK.chunk_15807 s8
  have s6 : leavesOK ctxLitU 168256250000 0 ((leaves.drop 31612).take 188) 169625000000 0 = true :=
    take_step (n := 2) (t := 188) (b := 31614) rfl rfl ArealUCore.ArealUK.chunk_15806 s7
  have s5 : leavesOK ctxLitU 168243750000 0 ((leaves.drop 31610).take 190) 169625000000 0 = true :=
    take_step (n := 2) (t := 190) (b := 31612) rfl rfl ArealUCore.ArealUK.chunk_15805 s6
  have s4 : leavesOK ctxLitU 168231250000 0 ((leaves.drop 31608).take 192) 169625000000 0 = true :=
    take_step (n := 2) (t := 192) (b := 31610) rfl rfl ArealUCore.ArealUK.chunk_15804 s5
  have s3 : leavesOK ctxLitU 168218750000 0 ((leaves.drop 31606).take 194) 169625000000 0 = true :=
    take_step (n := 2) (t := 194) (b := 31608) rfl rfl ArealUCore.ArealUK.chunk_15803 s4
  have s2 : leavesOK ctxLitU 168206250000 0 ((leaves.drop 31604).take 196) 169625000000 0 = true :=
    take_step (n := 2) (t := 196) (b := 31606) rfl rfl ArealUCore.ArealUK.chunk_15802 s3
  have s1 : leavesOK ctxLitU 168187500000 0 ((leaves.drop 31602).take 198) 169625000000 0 = true :=
    take_step (n := 2) (t := 198) (b := 31604) rfl rfl ArealUCore.ArealUK.chunk_15801 s2
  have s0 : leavesOK ctxLitU 168168750000 0 ((leaves.drop 31600).take 200) 169625000000 0 = true :=
    take_step (n := 2) (t := 200) (b := 31602) rfl rfl ArealUCore.ArealUK.chunk_15800 s1
  exact s0

end Areal.UCert

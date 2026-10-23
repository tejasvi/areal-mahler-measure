import ArealUK.Chunk9800
import ArealUK.Chunk9801
import ArealUK.Chunk9802
import ArealUK.Chunk9803
import ArealUK.Chunk9804
import ArealUK.Chunk9805
import ArealUK.Chunk9806
import ArealUK.Chunk9807
import ArealUK.Chunk9808
import ArealUK.Chunk9809
import ArealUK.Chunk9810
import ArealUK.Chunk9811
import ArealUK.Chunk9812
import ArealUK.Chunk9813
import ArealUK.Chunk9814
import ArealUK.Chunk9815
import ArealUK.Chunk9816
import ArealUK.Chunk9817
import ArealUK.Chunk9818
import ArealUK.Chunk9819
import ArealUK.Chunk9820
import ArealUK.Chunk9821
import ArealUK.Chunk9822
import ArealUK.Chunk9823
import ArealUK.Chunk9824
import ArealUK.Chunk9825
import ArealUK.Chunk9826
import ArealUK.Chunk9827
import ArealUK.Chunk9828
import ArealUK.Chunk9829
import ArealUK.Chunk9830
import ArealUK.Chunk9831
import ArealUK.Chunk9832
import ArealUK.Chunk9833
import ArealUK.Chunk9834
import ArealUK.Chunk9835
import ArealUK.Chunk9836
import ArealUK.Chunk9837
import ArealUK.Chunk9838
import ArealUK.Chunk9839
import ArealUK.Chunk9840
import ArealUK.Chunk9841
import ArealUK.Chunk9842
import ArealUK.Chunk9843
import ArealUK.Chunk9844
import ArealUK.Chunk9845
import ArealUK.Chunk9846
import ArealUK.Chunk9847
import ArealUK.Chunk9848
import ArealUK.Chunk9849
import ArealUK.Chunk9850
import ArealUK.Chunk9851
import ArealUK.Chunk9852
import ArealUK.Chunk9853
import ArealUK.Chunk9854
import ArealUK.Chunk9855
import ArealUK.Chunk9856
import ArealUK.Chunk9857
import ArealUK.Chunk9858
import ArealUK.Chunk9859
import ArealUK.Chunk9860
import ArealUK.Chunk9861
import ArealUK.Chunk9862
import ArealUK.Chunk9863
import ArealUK.Chunk9864
import ArealUK.Chunk9865
import ArealUK.Chunk9866
import ArealUK.Chunk9867
import ArealUK.Chunk9868
import ArealUK.Chunk9869
import ArealUK.Chunk9870
import ArealUK.Chunk9871
import ArealUK.Chunk9872
import ArealUK.Chunk9873
import ArealUK.Chunk9874
import ArealUK.Chunk9875
import ArealUK.Chunk9876
import ArealUK.Chunk9877
import ArealUK.Chunk9878
import ArealUK.Chunk9879
import ArealUK.Chunk9880
import ArealUK.Chunk9881
import ArealUK.Chunk9882
import ArealUK.Chunk9883
import ArealUK.Chunk9884
import ArealUK.Chunk9885
import ArealUK.Chunk9886
import ArealUK.Chunk9887
import ArealUK.Chunk9888
import ArealUK.Chunk9889
import ArealUK.Chunk9890
import ArealUK.Chunk9891
import ArealUK.Chunk9892
import ArealUK.Chunk9893
import ArealUK.Chunk9894
import ArealUK.Chunk9895
import ArealUK.Chunk9896
import ArealUK.Chunk9897
import ArealUK.Chunk9898
import ArealUK.Chunk9899
import Areal.UCert.LeavesKGen

/-! Group 98 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_98 : leavesOK ctxLitU 345100000000 2 ((leaves.drop 19600).take 200) 699075000000 3 = true := by
  have s99 := ArealUCore.ArealUK.chunk_9899
  have s98 : leavesOK ctxLitU 349475000000 2 ((leaves.drop 19796).take 4) 699075000000 3 = true :=
    take_step (n := 2) (t := 4) (b := 19798) rfl rfl ArealUCore.ArealUK.chunk_9898 s99
  have s97 : leavesOK ctxLitU 349425000000 2 ((leaves.drop 19794).take 6) 699075000000 3 = true :=
    take_step (n := 2) (t := 6) (b := 19796) rfl rfl ArealUCore.ArealUK.chunk_9897 s98
  have s96 : leavesOK ctxLitU 349375000000 2 ((leaves.drop 19792).take 8) 699075000000 3 = true :=
    take_step (n := 2) (t := 8) (b := 19794) rfl rfl ArealUCore.ArealUK.chunk_9896 s97
  have s95 : leavesOK ctxLitU 698700000000 3 ((leaves.drop 19790).take 10) 699075000000 3 = true :=
    take_step (n := 2) (t := 10) (b := 19792) rfl rfl ArealUCore.ArealUK.chunk_9895 s96
  have s94 : leavesOK ctxLitU 698650000000 3 ((leaves.drop 19788).take 12) 699075000000 3 = true :=
    take_step (n := 2) (t := 12) (b := 19790) rfl rfl ArealUCore.ArealUK.chunk_9894 s95
  have s93 : leavesOK ctxLitU 698600000000 3 ((leaves.drop 19786).take 14) 699075000000 3 = true :=
    take_step (n := 2) (t := 14) (b := 19788) rfl rfl ArealUCore.ArealUK.chunk_9893 s94
  have s92 : leavesOK ctxLitU 349250000000 2 ((leaves.drop 19784).take 16) 699075000000 3 = true :=
    take_step (n := 2) (t := 16) (b := 19786) rfl rfl ArealUCore.ArealUK.chunk_9892 s93
  have s91 : leavesOK ctxLitU 357551381710281 12 ((leaves.drop 19782).take 18) 699075000000 3 = true :=
    take_step (n := 2) (t := 18) (b := 19784) rfl rfl ArealUCore.ArealUK.chunk_9891 s92
  have s90 : leavesOK ctxLitU 357478400000000 12 ((leaves.drop 19780).take 20) 699075000000 3 = true :=
    take_step (n := 2) (t := 20) (b := 19782) rfl rfl ArealUCore.ArealUK.chunk_9890 s91
  have s89 : leavesOK ctxLitU 698150000000 3 ((leaves.drop 19778).take 22) 699075000000 3 = true :=
    take_step (n := 2) (t := 22) (b := 19780) rfl rfl ArealUCore.ArealUK.chunk_9889 s90
  have s88 : leavesOK ctxLitU 698075000000 3 ((leaves.drop 19776).take 24) 699075000000 3 = true :=
    take_step (n := 2) (t := 24) (b := 19778) rfl rfl ArealUCore.ArealUK.chunk_9888 s89
  have s87 : leavesOK ctxLitU 1396100000000 4 ((leaves.drop 19774).take 26) 699075000000 3 = true :=
    take_step (n := 2) (t := 26) (b := 19776) rfl rfl ArealUCore.ArealUK.chunk_9887 s88
  have s86 : leavesOK ctxLitU 348975000000 2 ((leaves.drop 19772).take 28) 699075000000 3 = true :=
    take_step (n := 2) (t := 28) (b := 19774) rfl rfl ArealUCore.ArealUK.chunk_9886 s87
  have s85 : leavesOK ctxLitU 348925000000 2 ((leaves.drop 19770).take 30) 699075000000 3 = true :=
    take_step (n := 2) (t := 30) (b := 19772) rfl rfl ArealUCore.ArealUK.chunk_9885 s86
  have s84 : leavesOK ctxLitU 697800000000 3 ((leaves.drop 19768).take 32) 699075000000 3 = true :=
    take_step (n := 2) (t := 32) (b := 19770) rfl rfl ArealUCore.ArealUK.chunk_9884 s85
  have s83 : leavesOK ctxLitU 697750000000 3 ((leaves.drop 19766).take 34) 699075000000 3 = true :=
    take_step (n := 2) (t := 34) (b := 19768) rfl rfl ArealUCore.ArealUK.chunk_9883 s84
  have s82 : leavesOK ctxLitU 697700000000 3 ((leaves.drop 19764).take 36) 699075000000 3 = true :=
    take_step (n := 2) (t := 36) (b := 19766) rfl rfl ArealUCore.ArealUK.chunk_9882 s83
  have s81 : leavesOK ctxLitU 697650000000 3 ((leaves.drop 19762).take 38) 699075000000 3 = true :=
    take_step (n := 2) (t := 38) (b := 19764) rfl rfl ArealUCore.ArealUK.chunk_9881 s82
  have s80 : leavesOK ctxLitU 697600000000 3 ((leaves.drop 19760).take 40) 699075000000 3 = true :=
    take_step (n := 2) (t := 40) (b := 19762) rfl rfl ArealUCore.ArealUK.chunk_9880 s81
  have s79 : leavesOK ctxLitU 697550000000 3 ((leaves.drop 19758).take 42) 699075000000 3 = true :=
    take_step (n := 2) (t := 42) (b := 19760) rfl rfl ArealUCore.ArealUK.chunk_9879 s80
  have s78 : leavesOK ctxLitU 697500000000 3 ((leaves.drop 19756).take 44) 699075000000 3 = true :=
    take_step (n := 2) (t := 44) (b := 19758) rfl rfl ArealUCore.ArealUK.chunk_9878 s79
  have s77 : leavesOK ctxLitU 697450000000 3 ((leaves.drop 19754).take 46) 699075000000 3 = true :=
    take_step (n := 2) (t := 46) (b := 19756) rfl rfl ArealUCore.ArealUK.chunk_9877 s78
  have s76 : leavesOK ctxLitU 697400000000 3 ((leaves.drop 19752).take 48) 699075000000 3 = true :=
    take_step (n := 2) (t := 48) (b := 19754) rfl rfl ArealUCore.ArealUK.chunk_9876 s77
  have s75 : leavesOK ctxLitU 697350000000 3 ((leaves.drop 19750).take 50) 699075000000 3 = true :=
    take_step (n := 2) (t := 50) (b := 19752) rfl rfl ArealUCore.ArealUK.chunk_9875 s76
  have s74 : leavesOK ctxLitU 697300000000 3 ((leaves.drop 19748).take 52) 699075000000 3 = true :=
    take_step (n := 2) (t := 52) (b := 19750) rfl rfl ArealUCore.ArealUK.chunk_9874 s75
  have s73 : leavesOK ctxLitU 348600000000 2 ((leaves.drop 19746).take 54) 699075000000 3 = true :=
    take_step (n := 2) (t := 54) (b := 19748) rfl rfl ArealUCore.ArealUK.chunk_9873 s74
  have s72 : leavesOK ctxLitU 348550000000 2 ((leaves.drop 19744).take 56) 699075000000 3 = true :=
    take_step (n := 2) (t := 56) (b := 19746) rfl rfl ArealUCore.ArealUK.chunk_9872 s73
  have s71 : leavesOK ctxLitU 697025000000 3 ((leaves.drop 19742).take 58) 699075000000 3 = true :=
    take_step (n := 2) (t := 58) (b := 19744) rfl rfl ArealUCore.ArealUK.chunk_9871 s72
  have s70 : leavesOK ctxLitU 696975000000 3 ((leaves.drop 19740).take 60) 699075000000 3 = true :=
    take_step (n := 2) (t := 60) (b := 19742) rfl rfl ArealUCore.ArealUK.chunk_9870 s71
  have s69 : leavesOK ctxLitU 696925000000 3 ((leaves.drop 19738).take 62) 699075000000 3 = true :=
    take_step (n := 2) (t := 62) (b := 19740) rfl rfl ArealUCore.ArealUK.chunk_9869 s70
  have s68 : leavesOK ctxLitU 696875000000 3 ((leaves.drop 19736).take 64) 699075000000 3 = true :=
    take_step (n := 2) (t := 64) (b := 19738) rfl rfl ArealUCore.ArealUK.chunk_9868 s69
  have s67 : leavesOK ctxLitU 696825000000 3 ((leaves.drop 19734).take 66) 699075000000 3 = true :=
    take_step (n := 2) (t := 66) (b := 19736) rfl rfl ArealUCore.ArealUK.chunk_9867 s68
  have s66 : leavesOK ctxLitU 696775000000 3 ((leaves.drop 19732).take 68) 699075000000 3 = true :=
    take_step (n := 2) (t := 68) (b := 19734) rfl rfl ArealUCore.ArealUK.chunk_9866 s67
  have s65 : leavesOK ctxLitU 348350000000 2 ((leaves.drop 19730).take 70) 699075000000 3 = true :=
    take_step (n := 2) (t := 70) (b := 19732) rfl rfl ArealUCore.ArealUK.chunk_9865 s66
  have s64 : leavesOK ctxLitU 348300000000 2 ((leaves.drop 19728).take 72) 699075000000 3 = true :=
    take_step (n := 2) (t := 72) (b := 19730) rfl rfl ArealUCore.ArealUK.chunk_9864 s65
  have s63 : leavesOK ctxLitU 348250000000 2 ((leaves.drop 19726).take 74) 699075000000 3 = true :=
    take_step (n := 2) (t := 74) (b := 19728) rfl rfl ArealUCore.ArealUK.chunk_9863 s64
  have s62 : leavesOK ctxLitU 348200000000 2 ((leaves.drop 19724).take 76) 699075000000 3 = true :=
    take_step (n := 2) (t := 76) (b := 19726) rfl rfl ArealUCore.ArealUK.chunk_9862 s63
  have s61 : leavesOK ctxLitU 348150000000 2 ((leaves.drop 19722).take 78) 699075000000 3 = true :=
    take_step (n := 2) (t := 78) (b := 19724) rfl rfl ArealUCore.ArealUK.chunk_9861 s62
  have s60 : leavesOK ctxLitU 348100000000 2 ((leaves.drop 19720).take 80) 699075000000 3 = true :=
    take_step (n := 2) (t := 80) (b := 19722) rfl rfl ArealUCore.ArealUK.chunk_9860 s61
  have s59 : leavesOK ctxLitU 348050000000 2 ((leaves.drop 19718).take 82) 699075000000 3 = true :=
    take_step (n := 2) (t := 82) (b := 19720) rfl rfl ArealUCore.ArealUK.chunk_9859 s60
  have s58 : leavesOK ctxLitU 348000000000 2 ((leaves.drop 19716).take 84) 699075000000 3 = true :=
    take_step (n := 2) (t := 84) (b := 19718) rfl rfl ArealUCore.ArealUK.chunk_9858 s59
  have s57 : leavesOK ctxLitU 347950000000 2 ((leaves.drop 19714).take 86) 699075000000 3 = true :=
    take_step (n := 2) (t := 86) (b := 19716) rfl rfl ArealUCore.ArealUK.chunk_9857 s58
  have s56 : leavesOK ctxLitU 347900000000 2 ((leaves.drop 19712).take 88) 699075000000 3 = true :=
    take_step (n := 2) (t := 88) (b := 19714) rfl rfl ArealUCore.ArealUK.chunk_9856 s57
  have s55 : leavesOK ctxLitU 347850000000 2 ((leaves.drop 19710).take 90) 699075000000 3 = true :=
    take_step (n := 2) (t := 90) (b := 19712) rfl rfl ArealUCore.ArealUK.chunk_9855 s56
  have s54 : leavesOK ctxLitU 347800000000 2 ((leaves.drop 19708).take 92) 699075000000 3 = true :=
    take_step (n := 2) (t := 92) (b := 19710) rfl rfl ArealUCore.ArealUK.chunk_9854 s55
  have s53 : leavesOK ctxLitU 347750000000 2 ((leaves.drop 19706).take 94) 699075000000 3 = true :=
    take_step (n := 2) (t := 94) (b := 19708) rfl rfl ArealUCore.ArealUK.chunk_9853 s54
  have s52 : leavesOK ctxLitU 347700000000 2 ((leaves.drop 19704).take 96) 699075000000 3 = true :=
    take_step (n := 2) (t := 96) (b := 19706) rfl rfl ArealUCore.ArealUK.chunk_9852 s53
  have s51 : leavesOK ctxLitU 347650000000 2 ((leaves.drop 19702).take 98) 699075000000 3 = true :=
    take_step (n := 2) (t := 98) (b := 19704) rfl rfl ArealUCore.ArealUK.chunk_9851 s52
  have s50 : leavesOK ctxLitU 347600000000 2 ((leaves.drop 19700).take 100) 699075000000 3 = true :=
    take_step (n := 2) (t := 100) (b := 19702) rfl rfl ArealUCore.ArealUK.chunk_9850 s51
  have s49 : leavesOK ctxLitU 347550000000 2 ((leaves.drop 19698).take 102) 699075000000 3 = true :=
    take_step (n := 2) (t := 102) (b := 19700) rfl rfl ArealUCore.ArealUK.chunk_9849 s50
  have s48 : leavesOK ctxLitU 347500000000 2 ((leaves.drop 19696).take 104) 699075000000 3 = true :=
    take_step (n := 2) (t := 104) (b := 19698) rfl rfl ArealUCore.ArealUK.chunk_9848 s49
  have s47 : leavesOK ctxLitU 347450000000 2 ((leaves.drop 19694).take 106) 699075000000 3 = true :=
    take_step (n := 2) (t := 106) (b := 19696) rfl rfl ArealUCore.ArealUK.chunk_9847 s48
  have s46 : leavesOK ctxLitU 347400000000 2 ((leaves.drop 19692).take 108) 699075000000 3 = true :=
    take_step (n := 2) (t := 108) (b := 19694) rfl rfl ArealUCore.ArealUK.chunk_9846 s47
  have s45 : leavesOK ctxLitU 347350000000 2 ((leaves.drop 19690).take 110) 699075000000 3 = true :=
    take_step (n := 2) (t := 110) (b := 19692) rfl rfl ArealUCore.ArealUK.chunk_9845 s46
  have s44 : leavesOK ctxLitU 347300000000 2 ((leaves.drop 19688).take 112) 699075000000 3 = true :=
    take_step (n := 2) (t := 112) (b := 19690) rfl rfl ArealUCore.ArealUK.chunk_9844 s45
  have s43 : leavesOK ctxLitU 347250000000 2 ((leaves.drop 19686).take 114) 699075000000 3 = true :=
    take_step (n := 2) (t := 114) (b := 19688) rfl rfl ArealUCore.ArealUK.chunk_9843 s44
  have s42 : leavesOK ctxLitU 347200000000 2 ((leaves.drop 19684).take 116) 699075000000 3 = true :=
    take_step (n := 2) (t := 116) (b := 19686) rfl rfl ArealUCore.ArealUK.chunk_9842 s43
  have s41 : leavesOK ctxLitU 347150000000 2 ((leaves.drop 19682).take 118) 699075000000 3 = true :=
    take_step (n := 2) (t := 118) (b := 19684) rfl rfl ArealUCore.ArealUK.chunk_9841 s42
  have s40 : leavesOK ctxLitU 347100000000 2 ((leaves.drop 19680).take 120) 699075000000 3 = true :=
    take_step (n := 2) (t := 120) (b := 19682) rfl rfl ArealUCore.ArealUK.chunk_9840 s41
  have s39 : leavesOK ctxLitU 347050000000 2 ((leaves.drop 19678).take 122) 699075000000 3 = true :=
    take_step (n := 2) (t := 122) (b := 19680) rfl rfl ArealUCore.ArealUK.chunk_9839 s40
  have s38 : leavesOK ctxLitU 347000000000 2 ((leaves.drop 19676).take 124) 699075000000 3 = true :=
    take_step (n := 2) (t := 124) (b := 19678) rfl rfl ArealUCore.ArealUK.chunk_9838 s39
  have s37 : leavesOK ctxLitU 346950000000 2 ((leaves.drop 19674).take 126) 699075000000 3 = true :=
    take_step (n := 2) (t := 126) (b := 19676) rfl rfl ArealUCore.ArealUK.chunk_9837 s38
  have s36 : leavesOK ctxLitU 346900000000 2 ((leaves.drop 19672).take 128) 699075000000 3 = true :=
    take_step (n := 2) (t := 128) (b := 19674) rfl rfl ArealUCore.ArealUK.chunk_9836 s37
  have s35 : leavesOK ctxLitU 346850000000 2 ((leaves.drop 19670).take 130) 699075000000 3 = true :=
    take_step (n := 2) (t := 130) (b := 19672) rfl rfl ArealUCore.ArealUK.chunk_9835 s36
  have s34 : leavesOK ctxLitU 346800000000 2 ((leaves.drop 19668).take 132) 699075000000 3 = true :=
    take_step (n := 2) (t := 132) (b := 19670) rfl rfl ArealUCore.ArealUK.chunk_9834 s35
  have s33 : leavesOK ctxLitU 346750000000 2 ((leaves.drop 19666).take 134) 699075000000 3 = true :=
    take_step (n := 2) (t := 134) (b := 19668) rfl rfl ArealUCore.ArealUK.chunk_9833 s34
  have s32 : leavesOK ctxLitU 346700000000 2 ((leaves.drop 19664).take 136) 699075000000 3 = true :=
    take_step (n := 2) (t := 136) (b := 19666) rfl rfl ArealUCore.ArealUK.chunk_9832 s33
  have s31 : leavesOK ctxLitU 346650000000 2 ((leaves.drop 19662).take 138) 699075000000 3 = true :=
    take_step (n := 2) (t := 138) (b := 19664) rfl rfl ArealUCore.ArealUK.chunk_9831 s32
  have s30 : leavesOK ctxLitU 346600000000 2 ((leaves.drop 19660).take 140) 699075000000 3 = true :=
    take_step (n := 2) (t := 140) (b := 19662) rfl rfl ArealUCore.ArealUK.chunk_9830 s31
  have s29 : leavesOK ctxLitU 346550000000 2 ((leaves.drop 19658).take 142) 699075000000 3 = true :=
    take_step (n := 2) (t := 142) (b := 19660) rfl rfl ArealUCore.ArealUK.chunk_9829 s30
  have s28 : leavesOK ctxLitU 346500000000 2 ((leaves.drop 19656).take 144) 699075000000 3 = true :=
    take_step (n := 2) (t := 144) (b := 19658) rfl rfl ArealUCore.ArealUK.chunk_9828 s29
  have s27 : leavesOK ctxLitU 346450000000 2 ((leaves.drop 19654).take 146) 699075000000 3 = true :=
    take_step (n := 2) (t := 146) (b := 19656) rfl rfl ArealUCore.ArealUK.chunk_9827 s28
  have s26 : leavesOK ctxLitU 346400000000 2 ((leaves.drop 19652).take 148) 699075000000 3 = true :=
    take_step (n := 2) (t := 148) (b := 19654) rfl rfl ArealUCore.ArealUK.chunk_9826 s27
  have s25 : leavesOK ctxLitU 346350000000 2 ((leaves.drop 19650).take 150) 699075000000 3 = true :=
    take_step (n := 2) (t := 150) (b := 19652) rfl rfl ArealUCore.ArealUK.chunk_9825 s26
  have s24 : leavesOK ctxLitU 346300000000 2 ((leaves.drop 19648).take 152) 699075000000 3 = true :=
    take_step (n := 2) (t := 152) (b := 19650) rfl rfl ArealUCore.ArealUK.chunk_9824 s25
  have s23 : leavesOK ctxLitU 346250000000 2 ((leaves.drop 19646).take 154) 699075000000 3 = true :=
    take_step (n := 2) (t := 154) (b := 19648) rfl rfl ArealUCore.ArealUK.chunk_9823 s24
  have s22 : leavesOK ctxLitU 346200000000 2 ((leaves.drop 19644).take 156) 699075000000 3 = true :=
    take_step (n := 2) (t := 156) (b := 19646) rfl rfl ArealUCore.ArealUK.chunk_9822 s23
  have s21 : leavesOK ctxLitU 346150000000 2 ((leaves.drop 19642).take 158) 699075000000 3 = true :=
    take_step (n := 2) (t := 158) (b := 19644) rfl rfl ArealUCore.ArealUK.chunk_9821 s22
  have s20 : leavesOK ctxLitU 346100000000 2 ((leaves.drop 19640).take 160) 699075000000 3 = true :=
    take_step (n := 2) (t := 160) (b := 19642) rfl rfl ArealUCore.ArealUK.chunk_9820 s21
  have s19 : leavesOK ctxLitU 346050000000 2 ((leaves.drop 19638).take 162) 699075000000 3 = true :=
    take_step (n := 2) (t := 162) (b := 19640) rfl rfl ArealUCore.ArealUK.chunk_9819 s20
  have s18 : leavesOK ctxLitU 346000000000 2 ((leaves.drop 19636).take 164) 699075000000 3 = true :=
    take_step (n := 2) (t := 164) (b := 19638) rfl rfl ArealUCore.ArealUK.chunk_9818 s19
  have s17 : leavesOK ctxLitU 345950000000 2 ((leaves.drop 19634).take 166) 699075000000 3 = true :=
    take_step (n := 2) (t := 166) (b := 19636) rfl rfl ArealUCore.ArealUK.chunk_9817 s18
  have s16 : leavesOK ctxLitU 345900000000 2 ((leaves.drop 19632).take 168) 699075000000 3 = true :=
    take_step (n := 2) (t := 168) (b := 19634) rfl rfl ArealUCore.ArealUK.chunk_9816 s17
  have s15 : leavesOK ctxLitU 345850000000 2 ((leaves.drop 19630).take 170) 699075000000 3 = true :=
    take_step (n := 2) (t := 170) (b := 19632) rfl rfl ArealUCore.ArealUK.chunk_9815 s16
  have s14 : leavesOK ctxLitU 345800000000 2 ((leaves.drop 19628).take 172) 699075000000 3 = true :=
    take_step (n := 2) (t := 172) (b := 19630) rfl rfl ArealUCore.ArealUK.chunk_9814 s15
  have s13 : leavesOK ctxLitU 345750000000 2 ((leaves.drop 19626).take 174) 699075000000 3 = true :=
    take_step (n := 2) (t := 174) (b := 19628) rfl rfl ArealUCore.ArealUK.chunk_9813 s14
  have s12 : leavesOK ctxLitU 345700000000 2 ((leaves.drop 19624).take 176) 699075000000 3 = true :=
    take_step (n := 2) (t := 176) (b := 19626) rfl rfl ArealUCore.ArealUK.chunk_9812 s13
  have s11 : leavesOK ctxLitU 345650000000 2 ((leaves.drop 19622).take 178) 699075000000 3 = true :=
    take_step (n := 2) (t := 178) (b := 19624) rfl rfl ArealUCore.ArealUK.chunk_9811 s12
  have s10 : leavesOK ctxLitU 345600000000 2 ((leaves.drop 19620).take 180) 699075000000 3 = true :=
    take_step (n := 2) (t := 180) (b := 19622) rfl rfl ArealUCore.ArealUK.chunk_9810 s11
  have s9 : leavesOK ctxLitU 345550000000 2 ((leaves.drop 19618).take 182) 699075000000 3 = true :=
    take_step (n := 2) (t := 182) (b := 19620) rfl rfl ArealUCore.ArealUK.chunk_9809 s10
  have s8 : leavesOK ctxLitU 345500000000 2 ((leaves.drop 19616).take 184) 699075000000 3 = true :=
    take_step (n := 2) (t := 184) (b := 19618) rfl rfl ArealUCore.ArealUK.chunk_9808 s9
  have s7 : leavesOK ctxLitU 345450000000 2 ((leaves.drop 19614).take 186) 699075000000 3 = true :=
    take_step (n := 2) (t := 186) (b := 19616) rfl rfl ArealUCore.ArealUK.chunk_9807 s8
  have s6 : leavesOK ctxLitU 345400000000 2 ((leaves.drop 19612).take 188) 699075000000 3 = true :=
    take_step (n := 2) (t := 188) (b := 19614) rfl rfl ArealUCore.ArealUK.chunk_9806 s7
  have s5 : leavesOK ctxLitU 345350000000 2 ((leaves.drop 19610).take 190) 699075000000 3 = true :=
    take_step (n := 2) (t := 190) (b := 19612) rfl rfl ArealUCore.ArealUK.chunk_9805 s6
  have s4 : leavesOK ctxLitU 345300000000 2 ((leaves.drop 19608).take 192) 699075000000 3 = true :=
    take_step (n := 2) (t := 192) (b := 19610) rfl rfl ArealUCore.ArealUK.chunk_9804 s5
  have s3 : leavesOK ctxLitU 345250000000 2 ((leaves.drop 19606).take 194) 699075000000 3 = true :=
    take_step (n := 2) (t := 194) (b := 19608) rfl rfl ArealUCore.ArealUK.chunk_9803 s4
  have s2 : leavesOK ctxLitU 345200000000 2 ((leaves.drop 19604).take 196) 699075000000 3 = true :=
    take_step (n := 2) (t := 196) (b := 19606) rfl rfl ArealUCore.ArealUK.chunk_9802 s3
  have s1 : leavesOK ctxLitU 345150000000 2 ((leaves.drop 19602).take 198) 699075000000 3 = true :=
    take_step (n := 2) (t := 198) (b := 19604) rfl rfl ArealUCore.ArealUK.chunk_9801 s2
  have s0 : leavesOK ctxLitU 345100000000 2 ((leaves.drop 19600).take 200) 699075000000 3 = true :=
    take_step (n := 2) (t := 200) (b := 19602) rfl rfl ArealUCore.ArealUK.chunk_9800 s1
  exact s0

end Areal.UCert

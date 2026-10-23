import ArealUK.Chunk9000
import ArealUK.Chunk9001
import ArealUK.Chunk9002
import ArealUK.Chunk9003
import ArealUK.Chunk9004
import ArealUK.Chunk9005
import ArealUK.Chunk9006
import ArealUK.Chunk9007
import ArealUK.Chunk9008
import ArealUK.Chunk9009
import ArealUK.Chunk9010
import ArealUK.Chunk9011
import ArealUK.Chunk9012
import ArealUK.Chunk9013
import ArealUK.Chunk9014
import ArealUK.Chunk9015
import ArealUK.Chunk9016
import ArealUK.Chunk9017
import ArealUK.Chunk9018
import ArealUK.Chunk9019
import ArealUK.Chunk9020
import ArealUK.Chunk9021
import ArealUK.Chunk9022
import ArealUK.Chunk9023
import ArealUK.Chunk9024
import ArealUK.Chunk9025
import ArealUK.Chunk9026
import ArealUK.Chunk9027
import ArealUK.Chunk9028
import ArealUK.Chunk9029
import ArealUK.Chunk9030
import ArealUK.Chunk9031
import ArealUK.Chunk9032
import ArealUK.Chunk9033
import ArealUK.Chunk9034
import ArealUK.Chunk9035
import ArealUK.Chunk9036
import ArealUK.Chunk9037
import ArealUK.Chunk9038
import ArealUK.Chunk9039
import ArealUK.Chunk9040
import ArealUK.Chunk9041
import ArealUK.Chunk9042
import ArealUK.Chunk9043
import ArealUK.Chunk9044
import ArealUK.Chunk9045
import ArealUK.Chunk9046
import ArealUK.Chunk9047
import ArealUK.Chunk9048
import ArealUK.Chunk9049
import ArealUK.Chunk9050
import ArealUK.Chunk9051
import ArealUK.Chunk9052
import ArealUK.Chunk9053
import ArealUK.Chunk9054
import ArealUK.Chunk9055
import ArealUK.Chunk9056
import ArealUK.Chunk9057
import ArealUK.Chunk9058
import ArealUK.Chunk9059
import ArealUK.Chunk9060
import ArealUK.Chunk9061
import ArealUK.Chunk9062
import ArealUK.Chunk9063
import ArealUK.Chunk9064
import ArealUK.Chunk9065
import ArealUK.Chunk9066
import ArealUK.Chunk9067
import ArealUK.Chunk9068
import ArealUK.Chunk9069
import ArealUK.Chunk9070
import ArealUK.Chunk9071
import ArealUK.Chunk9072
import ArealUK.Chunk9073
import ArealUK.Chunk9074
import ArealUK.Chunk9075
import ArealUK.Chunk9076
import ArealUK.Chunk9077
import ArealUK.Chunk9078
import ArealUK.Chunk9079
import ArealUK.Chunk9080
import ArealUK.Chunk9081
import ArealUK.Chunk9082
import ArealUK.Chunk9083
import ArealUK.Chunk9084
import ArealUK.Chunk9085
import ArealUK.Chunk9086
import ArealUK.Chunk9087
import ArealUK.Chunk9088
import ArealUK.Chunk9089
import ArealUK.Chunk9090
import ArealUK.Chunk9091
import ArealUK.Chunk9092
import ArealUK.Chunk9093
import ArealUK.Chunk9094
import ArealUK.Chunk9095
import ArealUK.Chunk9096
import ArealUK.Chunk9097
import ArealUK.Chunk9098
import ArealUK.Chunk9099
import Areal.UCert.LeavesKGen

/-! Group 90 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_90 : leavesOK ctxLitU 296400000000 2 ((leaves.drop 18000).take 200) 76750000000 0 = true := by
  have s99 := ArealUCore.ArealUK.chunk_9099
  have s98 : leavesOK ctxLitU 76650000000 0 ((leaves.drop 18196).take 4) 76750000000 0 = true :=
    take_step (n := 2) (t := 4) (b := 18198) rfl rfl ArealUCore.ArealUK.chunk_9098 s99
  have s97 : leavesOK ctxLitU 76600000000 0 ((leaves.drop 18194).take 6) 76750000000 0 = true :=
    take_step (n := 2) (t := 6) (b := 18196) rfl rfl ArealUCore.ArealUK.chunk_9097 s98
  have s96 : leavesOK ctxLitU 76550000000 0 ((leaves.drop 18192).take 8) 76750000000 0 = true :=
    take_step (n := 2) (t := 8) (b := 18194) rfl rfl ArealUCore.ArealUK.chunk_9096 s97
  have s95 : leavesOK ctxLitU 76500000000 0 ((leaves.drop 18190).take 10) 76750000000 0 = true :=
    take_step (n := 2) (t := 10) (b := 18192) rfl rfl ArealUCore.ArealUK.chunk_9095 s96
  have s94 : leavesOK ctxLitU 76450000000 0 ((leaves.drop 18188).take 12) 76750000000 0 = true :=
    take_step (n := 2) (t := 12) (b := 18190) rfl rfl ArealUCore.ArealUK.chunk_9094 s95
  have s93 : leavesOK ctxLitU 76400000000 0 ((leaves.drop 18186).take 14) 76750000000 0 = true :=
    take_step (n := 2) (t := 14) (b := 18188) rfl rfl ArealUCore.ArealUK.chunk_9093 s94
  have s92 : leavesOK ctxLitU 76362500000 0 ((leaves.drop 18184).take 16) 76750000000 0 = true :=
    take_step (n := 2) (t := 16) (b := 18186) rfl rfl ArealUCore.ArealUK.chunk_9092 s93
  have s91 : leavesOK ctxLitU 76343750000 0 ((leaves.drop 18182).take 18) 76750000000 0 = true :=
    take_step (n := 2) (t := 18) (b := 18184) rfl rfl ArealUCore.ArealUK.chunk_9091 s92
  have s90 : leavesOK ctxLitU 76331250000 0 ((leaves.drop 18180).take 20) 76750000000 0 = true :=
    take_step (n := 2) (t := 20) (b := 18182) rfl rfl ArealUCore.ArealUK.chunk_9090 s91
  have s89 : leavesOK ctxLitU 76312500000 0 ((leaves.drop 18178).take 22) 76750000000 0 = true :=
    take_step (n := 2) (t := 22) (b := 18180) rfl rfl ArealUCore.ArealUK.chunk_9089 s90
  have s88 : leavesOK ctxLitU 76275000000 0 ((leaves.drop 18176).take 24) 76750000000 0 = true :=
    take_step (n := 2) (t := 24) (b := 18178) rfl rfl ArealUCore.ArealUK.chunk_9088 s89
  have s87 : leavesOK ctxLitU 312246712451669 12 ((leaves.drop 18174).take 26) 76750000000 0 = true :=
    take_step (n := 2) (t := 26) (b := 18176) rfl rfl ArealUCore.ArealUK.chunk_9087 s88
  have s86 : leavesOK ctxLitU 312217600000000 12 ((leaves.drop 18172).take 28) 76750000000 0 = true :=
    take_step (n := 2) (t := 28) (b := 18174) rfl rfl ArealUCore.ArealUK.chunk_9086 s87
  have s85 : leavesOK ctxLitU 76175000000 0 ((leaves.drop 18170).take 30) 76750000000 0 = true :=
    take_step (n := 2) (t := 30) (b := 18172) rfl rfl ArealUCore.ArealUK.chunk_9085 s86
  have s84 : leavesOK ctxLitU 76150000000 0 ((leaves.drop 18168).take 32) 76750000000 0 = true :=
    take_step (n := 2) (t := 32) (b := 18170) rfl rfl ArealUCore.ArealUK.chunk_9084 s85
  have s83 : leavesOK ctxLitU 76137500000 0 ((leaves.drop 18166).take 34) 76750000000 0 = true :=
    take_step (n := 2) (t := 34) (b := 18168) rfl rfl ArealUCore.ArealUK.chunk_9083 s84
  have s82 : leavesOK ctxLitU 76125000000 0 ((leaves.drop 18164).take 36) 76750000000 0 = true :=
    take_step (n := 2) (t := 36) (b := 18166) rfl rfl ArealUCore.ArealUK.chunk_9082 s83
  have s81 : leavesOK ctxLitU 76100000000 0 ((leaves.drop 18162).take 38) 76750000000 0 = true :=
    take_step (n := 2) (t := 38) (b := 18164) rfl rfl ArealUCore.ArealUK.chunk_9081 s82
  have s80 : leavesOK ctxLitU 76050000000 0 ((leaves.drop 18160).take 40) 76750000000 0 = true :=
    take_step (n := 2) (t := 40) (b := 18162) rfl rfl ArealUCore.ArealUK.chunk_9080 s81
  have s79 : leavesOK ctxLitU 76000000000 0 ((leaves.drop 18158).take 42) 76750000000 0 = true :=
    take_step (n := 2) (t := 42) (b := 18160) rfl rfl ArealUCore.ArealUK.chunk_9079 s80
  have s78 : leavesOK ctxLitU 75950000000 0 ((leaves.drop 18156).take 44) 76750000000 0 = true :=
    take_step (n := 2) (t := 44) (b := 18158) rfl rfl ArealUCore.ArealUK.chunk_9078 s79
  have s77 : leavesOK ctxLitU 75900000000 0 ((leaves.drop 18154).take 46) 76750000000 0 = true :=
    take_step (n := 2) (t := 46) (b := 18156) rfl rfl ArealUCore.ArealUK.chunk_9077 s78
  have s76 : leavesOK ctxLitU 75850000000 0 ((leaves.drop 18152).take 48) 76750000000 0 = true :=
    take_step (n := 2) (t := 48) (b := 18154) rfl rfl ArealUCore.ArealUK.chunk_9076 s77
  have s75 : leavesOK ctxLitU 75800000000 0 ((leaves.drop 18150).take 50) 76750000000 0 = true :=
    take_step (n := 2) (t := 50) (b := 18152) rfl rfl ArealUCore.ArealUK.chunk_9075 s76
  have s74 : leavesOK ctxLitU 75750000000 0 ((leaves.drop 18148).take 52) 76750000000 0 = true :=
    take_step (n := 2) (t := 52) (b := 18150) rfl rfl ArealUCore.ArealUK.chunk_9074 s75
  have s73 : leavesOK ctxLitU 310268716206041 12 ((leaves.drop 18146).take 54) 76750000000 0 = true :=
    take_step (n := 2) (t := 54) (b := 18148) rfl rfl ArealUCore.ArealUK.chunk_9073 s74
  have s72 : leavesOK ctxLitU 75700000000 0 ((leaves.drop 18144).take 56) 76750000000 0 = true :=
    take_step (n := 2) (t := 56) (b := 18146) rfl rfl ArealUCore.ArealUK.chunk_9072 s73
  have s71 : leavesOK ctxLitU 75650000000 0 ((leaves.drop 18142).take 58) 76750000000 0 = true :=
    take_step (n := 2) (t := 58) (b := 18144) rfl rfl ArealUCore.ArealUK.chunk_9071 s72
  have s70 : leavesOK ctxLitU 75600000000 0 ((leaves.drop 18140).take 60) 76750000000 0 = true :=
    take_step (n := 2) (t := 60) (b := 18142) rfl rfl ArealUCore.ArealUK.chunk_9070 s71
  have s69 : leavesOK ctxLitU 75550000000 0 ((leaves.drop 18138).take 62) 76750000000 0 = true :=
    take_step (n := 2) (t := 62) (b := 18140) rfl rfl ArealUCore.ArealUK.chunk_9069 s70
  have s68 : leavesOK ctxLitU 75500000000 0 ((leaves.drop 18136).take 64) 76750000000 0 = true :=
    take_step (n := 2) (t := 64) (b := 18138) rfl rfl ArealUCore.ArealUK.chunk_9068 s69
  have s67 : leavesOK ctxLitU 75450000000 0 ((leaves.drop 18134).take 66) 76750000000 0 = true :=
    take_step (n := 2) (t := 66) (b := 18136) rfl rfl ArealUCore.ArealUK.chunk_9067 s68
  have s66 : leavesOK ctxLitU 75400000000 0 ((leaves.drop 18132).take 68) 76750000000 0 = true :=
    take_step (n := 2) (t := 68) (b := 18134) rfl rfl ArealUCore.ArealUK.chunk_9066 s67
  have s65 : leavesOK ctxLitU 75350000000 0 ((leaves.drop 18130).take 70) 76750000000 0 = true :=
    take_step (n := 2) (t := 70) (b := 18132) rfl rfl ArealUCore.ArealUK.chunk_9065 s66
  have s64 : leavesOK ctxLitU 75300000000 0 ((leaves.drop 18128).take 72) 76750000000 0 = true :=
    take_step (n := 2) (t := 72) (b := 18130) rfl rfl ArealUCore.ArealUK.chunk_9064 s65
  have s63 : leavesOK ctxLitU 75250000000 0 ((leaves.drop 18126).take 74) 76750000000 0 = true :=
    take_step (n := 2) (t := 74) (b := 18128) rfl rfl ArealUCore.ArealUK.chunk_9063 s64
  have s62 : leavesOK ctxLitU 75200000000 0 ((leaves.drop 18124).take 76) 76750000000 0 = true :=
    take_step (n := 2) (t := 76) (b := 18126) rfl rfl ArealUCore.ArealUK.chunk_9062 s63
  have s61 : leavesOK ctxLitU 75150000000 0 ((leaves.drop 18122).take 78) 76750000000 0 = true :=
    take_step (n := 2) (t := 78) (b := 18124) rfl rfl ArealUCore.ArealUK.chunk_9061 s62
  have s60 : leavesOK ctxLitU 75100000000 0 ((leaves.drop 18120).take 80) 76750000000 0 = true :=
    take_step (n := 2) (t := 80) (b := 18122) rfl rfl ArealUCore.ArealUK.chunk_9060 s61
  have s59 : leavesOK ctxLitU 75050000000 0 ((leaves.drop 18118).take 82) 76750000000 0 = true :=
    take_step (n := 2) (t := 82) (b := 18120) rfl rfl ArealUCore.ArealUK.chunk_9059 s60
  have s58 : leavesOK ctxLitU 75000000000 0 ((leaves.drop 18116).take 84) 76750000000 0 = true :=
    take_step (n := 2) (t := 84) (b := 18118) rfl rfl ArealUCore.ArealUK.chunk_9058 s59
  have s57 : leavesOK ctxLitU 74950000000 0 ((leaves.drop 18114).take 86) 76750000000 0 = true :=
    take_step (n := 2) (t := 86) (b := 18116) rfl rfl ArealUCore.ArealUK.chunk_9057 s58
  have s56 : leavesOK ctxLitU 74900000000 0 ((leaves.drop 18112).take 88) 76750000000 0 = true :=
    take_step (n := 2) (t := 88) (b := 18114) rfl rfl ArealUCore.ArealUK.chunk_9056 s57
  have s55 : leavesOK ctxLitU 74850000000 0 ((leaves.drop 18110).take 90) 76750000000 0 = true :=
    take_step (n := 2) (t := 90) (b := 18112) rfl rfl ArealUCore.ArealUK.chunk_9055 s56
  have s54 : leavesOK ctxLitU 74812500000 0 ((leaves.drop 18108).take 92) 76750000000 0 = true :=
    take_step (n := 2) (t := 92) (b := 18110) rfl rfl ArealUCore.ArealUK.chunk_9054 s55
  have s53 : leavesOK ctxLitU 74793750000 0 ((leaves.drop 18106).take 94) 76750000000 0 = true :=
    take_step (n := 2) (t := 94) (b := 18108) rfl rfl ArealUCore.ArealUK.chunk_9053 s54
  have s52 : leavesOK ctxLitU 74781250000 0 ((leaves.drop 18104).take 96) 76750000000 0 = true :=
    take_step (n := 2) (t := 96) (b := 18106) rfl rfl ArealUCore.ArealUK.chunk_9052 s53
  have s51 : leavesOK ctxLitU 74768750000 0 ((leaves.drop 18102).take 98) 76750000000 0 = true :=
    take_step (n := 2) (t := 98) (b := 18104) rfl rfl ArealUCore.ArealUK.chunk_9051 s52
  have s50 : leavesOK ctxLitU 74756250000 0 ((leaves.drop 18100).take 100) 76750000000 0 = true :=
    take_step (n := 2) (t := 100) (b := 18102) rfl rfl ArealUCore.ArealUK.chunk_9050 s51
  have s49 : leavesOK ctxLitU 74737500000 0 ((leaves.drop 18098).take 102) 76750000000 0 = true :=
    take_step (n := 2) (t := 102) (b := 18100) rfl rfl ArealUCore.ArealUK.chunk_9049 s50
  have s48 : leavesOK ctxLitU 74700000000 0 ((leaves.drop 18096).take 104) 76750000000 0 = true :=
    take_step (n := 2) (t := 104) (b := 18098) rfl rfl ArealUCore.ArealUK.chunk_9048 s49
  have s47 : leavesOK ctxLitU 149350000000 1 ((leaves.drop 18094).take 106) 76750000000 0 = true :=
    take_step (n := 2) (t := 106) (b := 18096) rfl rfl ArealUCore.ArealUK.chunk_9047 s48
  have s46 : leavesOK ctxLitU 597350000000 3 ((leaves.drop 18092).take 108) 76750000000 0 = true :=
    take_step (n := 2) (t := 108) (b := 18094) rfl rfl ArealUCore.ArealUK.chunk_9046 s47
  have s45 : leavesOK ctxLitU 298625000000 2 ((leaves.drop 18090).take 110) 76750000000 0 = true :=
    take_step (n := 2) (t := 110) (b := 18092) rfl rfl ArealUCore.ArealUK.chunk_9045 s46
  have s44 : leavesOK ctxLitU 298575000000 2 ((leaves.drop 18088).take 112) 76750000000 0 = true :=
    take_step (n := 2) (t := 112) (b := 18090) rfl rfl ArealUCore.ArealUK.chunk_9044 s45
  have s43 : leavesOK ctxLitU 298525000000 2 ((leaves.drop 18086).take 114) 76750000000 0 = true :=
    take_step (n := 2) (t := 114) (b := 18088) rfl rfl ArealUCore.ArealUK.chunk_9043 s44
  have s42 : leavesOK ctxLitU 298475000000 2 ((leaves.drop 18084).take 116) 76750000000 0 = true :=
    take_step (n := 2) (t := 116) (b := 18086) rfl rfl ArealUCore.ArealUK.chunk_9042 s43
  have s41 : leavesOK ctxLitU 298425000000 2 ((leaves.drop 18082).take 118) 76750000000 0 = true :=
    take_step (n := 2) (t := 118) (b := 18084) rfl rfl ArealUCore.ArealUK.chunk_9041 s42
  have s40 : leavesOK ctxLitU 298375000000 2 ((leaves.drop 18080).take 120) 76750000000 0 = true :=
    take_step (n := 2) (t := 120) (b := 18082) rfl rfl ArealUCore.ArealUK.chunk_9040 s41
  have s39 : leavesOK ctxLitU 298325000000 2 ((leaves.drop 18078).take 122) 76750000000 0 = true :=
    take_step (n := 2) (t := 122) (b := 18080) rfl rfl ArealUCore.ArealUK.chunk_9039 s40
  have s38 : leavesOK ctxLitU 298275000000 2 ((leaves.drop 18076).take 124) 76750000000 0 = true :=
    take_step (n := 2) (t := 124) (b := 18078) rfl rfl ArealUCore.ArealUK.chunk_9038 s39
  have s37 : leavesOK ctxLitU 298225000000 2 ((leaves.drop 18074).take 126) 76750000000 0 = true :=
    take_step (n := 2) (t := 126) (b := 18076) rfl rfl ArealUCore.ArealUK.chunk_9037 s38
  have s36 : leavesOK ctxLitU 298175000000 2 ((leaves.drop 18072).take 128) 76750000000 0 = true :=
    take_step (n := 2) (t := 128) (b := 18074) rfl rfl ArealUCore.ArealUK.chunk_9036 s37
  have s35 : leavesOK ctxLitU 298125000000 2 ((leaves.drop 18070).take 130) 76750000000 0 = true :=
    take_step (n := 2) (t := 130) (b := 18072) rfl rfl ArealUCore.ArealUK.chunk_9035 s36
  have s34 : leavesOK ctxLitU 298075000000 2 ((leaves.drop 18068).take 132) 76750000000 0 = true :=
    take_step (n := 2) (t := 132) (b := 18070) rfl rfl ArealUCore.ArealUK.chunk_9034 s35
  have s33 : leavesOK ctxLitU 298025000000 2 ((leaves.drop 18066).take 134) 76750000000 0 = true :=
    take_step (n := 2) (t := 134) (b := 18068) rfl rfl ArealUCore.ArealUK.chunk_9033 s34
  have s32 : leavesOK ctxLitU 297975000000 2 ((leaves.drop 18064).take 136) 76750000000 0 = true :=
    take_step (n := 2) (t := 136) (b := 18066) rfl rfl ArealUCore.ArealUK.chunk_9032 s33
  have s31 : leavesOK ctxLitU 297925000000 2 ((leaves.drop 18062).take 138) 76750000000 0 = true :=
    take_step (n := 2) (t := 138) (b := 18064) rfl rfl ArealUCore.ArealUK.chunk_9031 s32
  have s30 : leavesOK ctxLitU 297875000000 2 ((leaves.drop 18060).take 140) 76750000000 0 = true :=
    take_step (n := 2) (t := 140) (b := 18062) rfl rfl ArealUCore.ArealUK.chunk_9030 s31
  have s29 : leavesOK ctxLitU 297825000000 2 ((leaves.drop 18058).take 142) 76750000000 0 = true :=
    take_step (n := 2) (t := 142) (b := 18060) rfl rfl ArealUCore.ArealUK.chunk_9029 s30
  have s28 : leavesOK ctxLitU 297775000000 2 ((leaves.drop 18056).take 144) 76750000000 0 = true :=
    take_step (n := 2) (t := 144) (b := 18058) rfl rfl ArealUCore.ArealUK.chunk_9028 s29
  have s27 : leavesOK ctxLitU 297725000000 2 ((leaves.drop 18054).take 146) 76750000000 0 = true :=
    take_step (n := 2) (t := 146) (b := 18056) rfl rfl ArealUCore.ArealUK.chunk_9027 s28
  have s26 : leavesOK ctxLitU 297675000000 2 ((leaves.drop 18052).take 148) 76750000000 0 = true :=
    take_step (n := 2) (t := 148) (b := 18054) rfl rfl ArealUCore.ArealUK.chunk_9026 s27
  have s25 : leavesOK ctxLitU 297625000000 2 ((leaves.drop 18050).take 150) 76750000000 0 = true :=
    take_step (n := 2) (t := 150) (b := 18052) rfl rfl ArealUCore.ArealUK.chunk_9025 s26
  have s24 : leavesOK ctxLitU 297575000000 2 ((leaves.drop 18048).take 152) 76750000000 0 = true :=
    take_step (n := 2) (t := 152) (b := 18050) rfl rfl ArealUCore.ArealUK.chunk_9024 s25
  have s23 : leavesOK ctxLitU 297525000000 2 ((leaves.drop 18046).take 154) 76750000000 0 = true :=
    take_step (n := 2) (t := 154) (b := 18048) rfl rfl ArealUCore.ArealUK.chunk_9023 s24
  have s22 : leavesOK ctxLitU 297475000000 2 ((leaves.drop 18044).take 156) 76750000000 0 = true :=
    take_step (n := 2) (t := 156) (b := 18046) rfl rfl ArealUCore.ArealUK.chunk_9022 s23
  have s21 : leavesOK ctxLitU 297425000000 2 ((leaves.drop 18042).take 158) 76750000000 0 = true :=
    take_step (n := 2) (t := 158) (b := 18044) rfl rfl ArealUCore.ArealUK.chunk_9021 s22
  have s20 : leavesOK ctxLitU 297375000000 2 ((leaves.drop 18040).take 160) 76750000000 0 = true :=
    take_step (n := 2) (t := 160) (b := 18042) rfl rfl ArealUCore.ArealUK.chunk_9020 s21
  have s19 : leavesOK ctxLitU 297325000000 2 ((leaves.drop 18038).take 162) 76750000000 0 = true :=
    take_step (n := 2) (t := 162) (b := 18040) rfl rfl ArealUCore.ArealUK.chunk_9019 s20
  have s18 : leavesOK ctxLitU 297275000000 2 ((leaves.drop 18036).take 164) 76750000000 0 = true :=
    take_step (n := 2) (t := 164) (b := 18038) rfl rfl ArealUCore.ArealUK.chunk_9018 s19
  have s17 : leavesOK ctxLitU 297225000000 2 ((leaves.drop 18034).take 166) 76750000000 0 = true :=
    take_step (n := 2) (t := 166) (b := 18036) rfl rfl ArealUCore.ArealUK.chunk_9017 s18
  have s16 : leavesOK ctxLitU 297175000000 2 ((leaves.drop 18032).take 168) 76750000000 0 = true :=
    take_step (n := 2) (t := 168) (b := 18034) rfl rfl ArealUCore.ArealUK.chunk_9016 s17
  have s15 : leavesOK ctxLitU 297125000000 2 ((leaves.drop 18030).take 170) 76750000000 0 = true :=
    take_step (n := 2) (t := 170) (b := 18032) rfl rfl ArealUCore.ArealUK.chunk_9015 s16
  have s14 : leavesOK ctxLitU 297075000000 2 ((leaves.drop 18028).take 172) 76750000000 0 = true :=
    take_step (n := 2) (t := 172) (b := 18030) rfl rfl ArealUCore.ArealUK.chunk_9014 s15
  have s13 : leavesOK ctxLitU 297025000000 2 ((leaves.drop 18026).take 174) 76750000000 0 = true :=
    take_step (n := 2) (t := 174) (b := 18028) rfl rfl ArealUCore.ArealUK.chunk_9013 s14
  have s12 : leavesOK ctxLitU 296975000000 2 ((leaves.drop 18024).take 176) 76750000000 0 = true :=
    take_step (n := 2) (t := 176) (b := 18026) rfl rfl ArealUCore.ArealUK.chunk_9012 s13
  have s11 : leavesOK ctxLitU 296925000000 2 ((leaves.drop 18022).take 178) 76750000000 0 = true :=
    take_step (n := 2) (t := 178) (b := 18024) rfl rfl ArealUCore.ArealUK.chunk_9011 s12
  have s10 : leavesOK ctxLitU 296875000000 2 ((leaves.drop 18020).take 180) 76750000000 0 = true :=
    take_step (n := 2) (t := 180) (b := 18022) rfl rfl ArealUCore.ArealUK.chunk_9010 s11
  have s9 : leavesOK ctxLitU 296825000000 2 ((leaves.drop 18018).take 182) 76750000000 0 = true :=
    take_step (n := 2) (t := 182) (b := 18020) rfl rfl ArealUCore.ArealUK.chunk_9009 s10
  have s8 : leavesOK ctxLitU 296775000000 2 ((leaves.drop 18016).take 184) 76750000000 0 = true :=
    take_step (n := 2) (t := 184) (b := 18018) rfl rfl ArealUCore.ArealUK.chunk_9008 s9
  have s7 : leavesOK ctxLitU 296725000000 2 ((leaves.drop 18014).take 186) 76750000000 0 = true :=
    take_step (n := 2) (t := 186) (b := 18016) rfl rfl ArealUCore.ArealUK.chunk_9007 s8
  have s6 : leavesOK ctxLitU 593400000000 3 ((leaves.drop 18012).take 188) 76750000000 0 = true :=
    take_step (n := 2) (t := 188) (b := 18014) rfl rfl ArealUCore.ArealUK.chunk_9006 s7
  have s5 : leavesOK ctxLitU 296650000000 2 ((leaves.drop 18010).take 190) 76750000000 0 = true :=
    take_step (n := 2) (t := 190) (b := 18012) rfl rfl ArealUCore.ArealUK.chunk_9005 s6
  have s4 : leavesOK ctxLitU 296600000000 2 ((leaves.drop 18008).take 192) 76750000000 0 = true :=
    take_step (n := 2) (t := 192) (b := 18010) rfl rfl ArealUCore.ArealUK.chunk_9004 s5
  have s3 : leavesOK ctxLitU 296550000000 2 ((leaves.drop 18006).take 194) 76750000000 0 = true :=
    take_step (n := 2) (t := 194) (b := 18008) rfl rfl ArealUCore.ArealUK.chunk_9003 s4
  have s2 : leavesOK ctxLitU 296500000000 2 ((leaves.drop 18004).take 196) 76750000000 0 = true :=
    take_step (n := 2) (t := 196) (b := 18006) rfl rfl ArealUCore.ArealUK.chunk_9002 s3
  have s1 : leavesOK ctxLitU 296450000000 2 ((leaves.drop 18002).take 198) 76750000000 0 = true :=
    take_step (n := 2) (t := 198) (b := 18004) rfl rfl ArealUCore.ArealUK.chunk_9001 s2
  have s0 : leavesOK ctxLitU 296400000000 2 ((leaves.drop 18000).take 200) 76750000000 0 = true :=
    take_step (n := 2) (t := 200) (b := 18002) rfl rfl ArealUCore.ArealUK.chunk_9000 s1
  exact s0

end Areal.UCert

import ArealUK.Chunk8000
import ArealUK.Chunk8001
import ArealUK.Chunk8002
import ArealUK.Chunk8003
import ArealUK.Chunk8004
import ArealUK.Chunk8005
import ArealUK.Chunk8006
import ArealUK.Chunk8007
import ArealUK.Chunk8008
import ArealUK.Chunk8009
import ArealUK.Chunk8010
import ArealUK.Chunk8011
import ArealUK.Chunk8012
import ArealUK.Chunk8013
import ArealUK.Chunk8014
import ArealUK.Chunk8015
import ArealUK.Chunk8016
import ArealUK.Chunk8017
import ArealUK.Chunk8018
import ArealUK.Chunk8019
import ArealUK.Chunk8020
import ArealUK.Chunk8021
import ArealUK.Chunk8022
import ArealUK.Chunk8023
import ArealUK.Chunk8024
import ArealUK.Chunk8025
import ArealUK.Chunk8026
import ArealUK.Chunk8027
import ArealUK.Chunk8028
import ArealUK.Chunk8029
import ArealUK.Chunk8030
import ArealUK.Chunk8031
import ArealUK.Chunk8032
import ArealUK.Chunk8033
import ArealUK.Chunk8034
import ArealUK.Chunk8035
import ArealUK.Chunk8036
import ArealUK.Chunk8037
import ArealUK.Chunk8038
import ArealUK.Chunk8039
import ArealUK.Chunk8040
import ArealUK.Chunk8041
import ArealUK.Chunk8042
import ArealUK.Chunk8043
import ArealUK.Chunk8044
import ArealUK.Chunk8045
import ArealUK.Chunk8046
import ArealUK.Chunk8047
import ArealUK.Chunk8048
import ArealUK.Chunk8049
import ArealUK.Chunk8050
import ArealUK.Chunk8051
import ArealUK.Chunk8052
import ArealUK.Chunk8053
import ArealUK.Chunk8054
import ArealUK.Chunk8055
import ArealUK.Chunk8056
import ArealUK.Chunk8057
import ArealUK.Chunk8058
import ArealUK.Chunk8059
import ArealUK.Chunk8060
import ArealUK.Chunk8061
import ArealUK.Chunk8062
import ArealUK.Chunk8063
import ArealUK.Chunk8064
import ArealUK.Chunk8065
import ArealUK.Chunk8066
import ArealUK.Chunk8067
import ArealUK.Chunk8068
import ArealUK.Chunk8069
import ArealUK.Chunk8070
import ArealUK.Chunk8071
import ArealUK.Chunk8072
import ArealUK.Chunk8073
import ArealUK.Chunk8074
import ArealUK.Chunk8075
import ArealUK.Chunk8076
import ArealUK.Chunk8077
import ArealUK.Chunk8078
import ArealUK.Chunk8079
import ArealUK.Chunk8080
import ArealUK.Chunk8081
import ArealUK.Chunk8082
import ArealUK.Chunk8083
import ArealUK.Chunk8084
import ArealUK.Chunk8085
import ArealUK.Chunk8086
import ArealUK.Chunk8087
import ArealUK.Chunk8088
import ArealUK.Chunk8089
import ArealUK.Chunk8090
import ArealUK.Chunk8091
import ArealUK.Chunk8092
import ArealUK.Chunk8093
import ArealUK.Chunk8094
import ArealUK.Chunk8095
import ArealUK.Chunk8096
import ArealUK.Chunk8097
import ArealUK.Chunk8098
import ArealUK.Chunk8099
import Areal.UCert.LeavesKGen

/-! Group 80 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_80 : leavesOK ctxLitU 528300000000 3 ((leaves.drop 16000).take 200) 533575000000 3 = true := by
  have s99 := ArealUCore.ArealUK.chunk_8099
  have s98 : leavesOK ctxLitU 533475000000 3 ((leaves.drop 16196).take 4) 533575000000 3 = true :=
    take_step (n := 2) (t := 4) (b := 16198) rfl rfl ArealUCore.ArealUK.chunk_8098 s99
  have s97 : leavesOK ctxLitU 533425000000 3 ((leaves.drop 16194).take 6) 533575000000 3 = true :=
    take_step (n := 2) (t := 6) (b := 16196) rfl rfl ArealUCore.ArealUK.chunk_8097 s98
  have s96 : leavesOK ctxLitU 533375000000 3 ((leaves.drop 16192).take 8) 533575000000 3 = true :=
    take_step (n := 2) (t := 8) (b := 16194) rfl rfl ArealUCore.ArealUK.chunk_8096 s97
  have s95 : leavesOK ctxLitU 533325000000 3 ((leaves.drop 16190).take 10) 533575000000 3 = true :=
    take_step (n := 2) (t := 10) (b := 16192) rfl rfl ArealUCore.ArealUK.chunk_8095 s96
  have s94 : leavesOK ctxLitU 266625000000 2 ((leaves.drop 16188).take 12) 533575000000 3 = true :=
    take_step (n := 2) (t := 12) (b := 16190) rfl rfl ArealUCore.ArealUK.chunk_8094 s95
  have s93 : leavesOK ctxLitU 266575000000 2 ((leaves.drop 16186).take 14) 533575000000 3 = true :=
    take_step (n := 2) (t := 14) (b := 16188) rfl rfl ArealUCore.ArealUK.chunk_8093 s94
  have s92 : leavesOK ctxLitU 533100000000 3 ((leaves.drop 16184).take 16) 533575000000 3 = true :=
    take_step (n := 2) (t := 16) (b := 16186) rfl rfl ArealUCore.ArealUK.chunk_8092 s93
  have s91 : leavesOK ctxLitU 533050000000 3 ((leaves.drop 16182).take 18) 533575000000 3 = true :=
    take_step (n := 2) (t := 18) (b := 16184) rfl rfl ArealUCore.ArealUK.chunk_8091 s92
  have s90 : leavesOK ctxLitU 533000000000 3 ((leaves.drop 16180).take 20) 533575000000 3 = true :=
    take_step (n := 2) (t := 20) (b := 16182) rfl rfl ArealUCore.ArealUK.chunk_8090 s91
  have s89 : leavesOK ctxLitU 532950000000 3 ((leaves.drop 16178).take 22) 533575000000 3 = true :=
    take_step (n := 2) (t := 22) (b := 16180) rfl rfl ArealUCore.ArealUK.chunk_8089 s90
  have s88 : leavesOK ctxLitU 532900000000 3 ((leaves.drop 16176).take 24) 533575000000 3 = true :=
    take_step (n := 2) (t := 24) (b := 16178) rfl rfl ArealUCore.ArealUK.chunk_8088 s89
  have s87 : leavesOK ctxLitU 532850000000 3 ((leaves.drop 16174).take 26) 533575000000 3 = true :=
    take_step (n := 2) (t := 26) (b := 16176) rfl rfl ArealUCore.ArealUK.chunk_8087 s88
  have s86 : leavesOK ctxLitU 532800000000 3 ((leaves.drop 16172).take 28) 533575000000 3 = true :=
    take_step (n := 2) (t := 28) (b := 16174) rfl rfl ArealUCore.ArealUK.chunk_8086 s87
  have s85 : leavesOK ctxLitU 532750000000 3 ((leaves.drop 16170).take 30) 533575000000 3 = true :=
    take_step (n := 2) (t := 30) (b := 16172) rfl rfl ArealUCore.ArealUK.chunk_8085 s86
  have s84 : leavesOK ctxLitU 532700000000 3 ((leaves.drop 16168).take 32) 533575000000 3 = true :=
    take_step (n := 2) (t := 32) (b := 16170) rfl rfl ArealUCore.ArealUK.chunk_8084 s85
  have s83 : leavesOK ctxLitU 532650000000 3 ((leaves.drop 16166).take 34) 533575000000 3 = true :=
    take_step (n := 2) (t := 34) (b := 16168) rfl rfl ArealUCore.ArealUK.chunk_8083 s84
  have s82 : leavesOK ctxLitU 532600000000 3 ((leaves.drop 16164).take 36) 533575000000 3 = true :=
    take_step (n := 2) (t := 36) (b := 16166) rfl rfl ArealUCore.ArealUK.chunk_8082 s83
  have s81 : leavesOK ctxLitU 532550000000 3 ((leaves.drop 16162).take 38) 533575000000 3 = true :=
    take_step (n := 2) (t := 38) (b := 16164) rfl rfl ArealUCore.ArealUK.chunk_8081 s82
  have s80 : leavesOK ctxLitU 532500000000 3 ((leaves.drop 16160).take 40) 533575000000 3 = true :=
    take_step (n := 2) (t := 40) (b := 16162) rfl rfl ArealUCore.ArealUK.chunk_8080 s81
  have s79 : leavesOK ctxLitU 532450000000 3 ((leaves.drop 16158).take 42) 533575000000 3 = true :=
    take_step (n := 2) (t := 42) (b := 16160) rfl rfl ArealUCore.ArealUK.chunk_8079 s80
  have s78 : leavesOK ctxLitU 532400000000 3 ((leaves.drop 16156).take 44) 533575000000 3 = true :=
    take_step (n := 2) (t := 44) (b := 16158) rfl rfl ArealUCore.ArealUK.chunk_8078 s79
  have s77 : leavesOK ctxLitU 532325000000 3 ((leaves.drop 16154).take 46) 533575000000 3 = true :=
    take_step (n := 2) (t := 46) (b := 16156) rfl rfl ArealUCore.ArealUK.chunk_8077 s78
  have s76 : leavesOK ctxLitU 532275000000 3 ((leaves.drop 16152).take 48) 533575000000 3 = true :=
    take_step (n := 2) (t := 48) (b := 16154) rfl rfl ArealUCore.ArealUK.chunk_8076 s77
  have s75 : leavesOK ctxLitU 532225000000 3 ((leaves.drop 16150).take 50) 533575000000 3 = true :=
    take_step (n := 2) (t := 50) (b := 16152) rfl rfl ArealUCore.ArealUK.chunk_8075 s76
  have s74 : leavesOK ctxLitU 532175000000 3 ((leaves.drop 16148).take 52) 533575000000 3 = true :=
    take_step (n := 2) (t := 52) (b := 16150) rfl rfl ArealUCore.ArealUK.chunk_8074 s75
  have s73 : leavesOK ctxLitU 532125000000 3 ((leaves.drop 16146).take 54) 533575000000 3 = true :=
    take_step (n := 2) (t := 54) (b := 16148) rfl rfl ArealUCore.ArealUK.chunk_8073 s74
  have s72 : leavesOK ctxLitU 532075000000 3 ((leaves.drop 16144).take 56) 533575000000 3 = true :=
    take_step (n := 2) (t := 56) (b := 16146) rfl rfl ArealUCore.ArealUK.chunk_8072 s73
  have s71 : leavesOK ctxLitU 532025000000 3 ((leaves.drop 16142).take 58) 533575000000 3 = true :=
    take_step (n := 2) (t := 58) (b := 16144) rfl rfl ArealUCore.ArealUK.chunk_8071 s72
  have s70 : leavesOK ctxLitU 531975000000 3 ((leaves.drop 16140).take 60) 533575000000 3 = true :=
    take_step (n := 2) (t := 60) (b := 16142) rfl rfl ArealUCore.ArealUK.chunk_8070 s71
  have s69 : leavesOK ctxLitU 531925000000 3 ((leaves.drop 16138).take 62) 533575000000 3 = true :=
    take_step (n := 2) (t := 62) (b := 16140) rfl rfl ArealUCore.ArealUK.chunk_8069 s70
  have s68 : leavesOK ctxLitU 531875000000 3 ((leaves.drop 16136).take 64) 533575000000 3 = true :=
    take_step (n := 2) (t := 64) (b := 16138) rfl rfl ArealUCore.ArealUK.chunk_8068 s69
  have s67 : leavesOK ctxLitU 531825000000 3 ((leaves.drop 16134).take 66) 533575000000 3 = true :=
    take_step (n := 2) (t := 66) (b := 16136) rfl rfl ArealUCore.ArealUK.chunk_8067 s68
  have s66 : leavesOK ctxLitU 531775000000 3 ((leaves.drop 16132).take 68) 533575000000 3 = true :=
    take_step (n := 2) (t := 68) (b := 16134) rfl rfl ArealUCore.ArealUK.chunk_8066 s67
  have s65 : leavesOK ctxLitU 531725000000 3 ((leaves.drop 16130).take 70) 533575000000 3 = true :=
    take_step (n := 2) (t := 70) (b := 16132) rfl rfl ArealUCore.ArealUK.chunk_8065 s66
  have s64 : leavesOK ctxLitU 531675000000 3 ((leaves.drop 16128).take 72) 533575000000 3 = true :=
    take_step (n := 2) (t := 72) (b := 16130) rfl rfl ArealUCore.ArealUK.chunk_8064 s65
  have s63 : leavesOK ctxLitU 265800000000 2 ((leaves.drop 16126).take 74) 533575000000 3 = true :=
    take_step (n := 2) (t := 74) (b := 16128) rfl rfl ArealUCore.ArealUK.chunk_8063 s64
  have s62 : leavesOK ctxLitU 531550000000 3 ((leaves.drop 16124).take 76) 533575000000 3 = true :=
    take_step (n := 2) (t := 76) (b := 16126) rfl rfl ArealUCore.ArealUK.chunk_8062 s63
  have s61 : leavesOK ctxLitU 531500000000 3 ((leaves.drop 16122).take 78) 533575000000 3 = true :=
    take_step (n := 2) (t := 78) (b := 16124) rfl rfl ArealUCore.ArealUK.chunk_8061 s62
  have s60 : leavesOK ctxLitU 531450000000 3 ((leaves.drop 16120).take 80) 533575000000 3 = true :=
    take_step (n := 2) (t := 80) (b := 16122) rfl rfl ArealUCore.ArealUK.chunk_8060 s61
  have s59 : leavesOK ctxLitU 531400000000 3 ((leaves.drop 16118).take 82) 533575000000 3 = true :=
    take_step (n := 2) (t := 82) (b := 16120) rfl rfl ArealUCore.ArealUK.chunk_8059 s60
  have s58 : leavesOK ctxLitU 531350000000 3 ((leaves.drop 16116).take 84) 533575000000 3 = true :=
    take_step (n := 2) (t := 84) (b := 16118) rfl rfl ArealUCore.ArealUK.chunk_8058 s59
  have s57 : leavesOK ctxLitU 531300000000 3 ((leaves.drop 16114).take 86) 533575000000 3 = true :=
    take_step (n := 2) (t := 86) (b := 16116) rfl rfl ArealUCore.ArealUK.chunk_8057 s58
  have s56 : leavesOK ctxLitU 531250000000 3 ((leaves.drop 16112).take 88) 533575000000 3 = true :=
    take_step (n := 2) (t := 88) (b := 16114) rfl rfl ArealUCore.ArealUK.chunk_8056 s57
  have s55 : leavesOK ctxLitU 531200000000 3 ((leaves.drop 16110).take 90) 533575000000 3 = true :=
    take_step (n := 2) (t := 90) (b := 16112) rfl rfl ArealUCore.ArealUK.chunk_8055 s56
  have s54 : leavesOK ctxLitU 531150000000 3 ((leaves.drop 16108).take 92) 533575000000 3 = true :=
    take_step (n := 2) (t := 92) (b := 16110) rfl rfl ArealUCore.ArealUK.chunk_8054 s55
  have s53 : leavesOK ctxLitU 531100000000 3 ((leaves.drop 16106).take 94) 533575000000 3 = true :=
    take_step (n := 2) (t := 94) (b := 16108) rfl rfl ArealUCore.ArealUK.chunk_8053 s54
  have s52 : leavesOK ctxLitU 531050000000 3 ((leaves.drop 16104).take 96) 533575000000 3 = true :=
    take_step (n := 2) (t := 96) (b := 16106) rfl rfl ArealUCore.ArealUK.chunk_8052 s53
  have s51 : leavesOK ctxLitU 531000000000 3 ((leaves.drop 16102).take 98) 533575000000 3 = true :=
    take_step (n := 2) (t := 98) (b := 16104) rfl rfl ArealUCore.ArealUK.chunk_8051 s52
  have s50 : leavesOK ctxLitU 530950000000 3 ((leaves.drop 16100).take 100) 533575000000 3 = true :=
    take_step (n := 2) (t := 100) (b := 16102) rfl rfl ArealUCore.ArealUK.chunk_8050 s51
  have s49 : leavesOK ctxLitU 530900000000 3 ((leaves.drop 16098).take 102) 533575000000 3 = true :=
    take_step (n := 2) (t := 102) (b := 16100) rfl rfl ArealUCore.ArealUK.chunk_8049 s50
  have s48 : leavesOK ctxLitU 530850000000 3 ((leaves.drop 16096).take 104) 533575000000 3 = true :=
    take_step (n := 2) (t := 104) (b := 16098) rfl rfl ArealUCore.ArealUK.chunk_8048 s49
  have s47 : leavesOK ctxLitU 265375000000 2 ((leaves.drop 16094).take 106) 533575000000 3 = true :=
    take_step (n := 2) (t := 106) (b := 16096) rfl rfl ArealUCore.ArealUK.chunk_8047 s48
  have s46 : leavesOK ctxLitU 530700000000 3 ((leaves.drop 16092).take 108) 533575000000 3 = true :=
    take_step (n := 2) (t := 108) (b := 16094) rfl rfl ArealUCore.ArealUK.chunk_8046 s47
  have s45 : leavesOK ctxLitU 530650000000 3 ((leaves.drop 16090).take 110) 533575000000 3 = true :=
    take_step (n := 2) (t := 110) (b := 16092) rfl rfl ArealUCore.ArealUK.chunk_8045 s46
  have s44 : leavesOK ctxLitU 530600000000 3 ((leaves.drop 16088).take 112) 533575000000 3 = true :=
    take_step (n := 2) (t := 112) (b := 16090) rfl rfl ArealUCore.ArealUK.chunk_8044 s45
  have s43 : leavesOK ctxLitU 530550000000 3 ((leaves.drop 16086).take 114) 533575000000 3 = true :=
    take_step (n := 2) (t := 114) (b := 16088) rfl rfl ArealUCore.ArealUK.chunk_8043 s44
  have s42 : leavesOK ctxLitU 530500000000 3 ((leaves.drop 16084).take 116) 533575000000 3 = true :=
    take_step (n := 2) (t := 116) (b := 16086) rfl rfl ArealUCore.ArealUK.chunk_8042 s43
  have s41 : leavesOK ctxLitU 530450000000 3 ((leaves.drop 16082).take 118) 533575000000 3 = true :=
    take_step (n := 2) (t := 118) (b := 16084) rfl rfl ArealUCore.ArealUK.chunk_8041 s42
  have s40 : leavesOK ctxLitU 530400000000 3 ((leaves.drop 16080).take 120) 533575000000 3 = true :=
    take_step (n := 2) (t := 120) (b := 16082) rfl rfl ArealUCore.ArealUK.chunk_8040 s41
  have s39 : leavesOK ctxLitU 530350000000 3 ((leaves.drop 16078).take 122) 533575000000 3 = true :=
    take_step (n := 2) (t := 122) (b := 16080) rfl rfl ArealUCore.ArealUK.chunk_8039 s40
  have s38 : leavesOK ctxLitU 530300000000 3 ((leaves.drop 16076).take 124) 533575000000 3 = true :=
    take_step (n := 2) (t := 124) (b := 16078) rfl rfl ArealUCore.ArealUK.chunk_8038 s39
  have s37 : leavesOK ctxLitU 530250000000 3 ((leaves.drop 16074).take 126) 533575000000 3 = true :=
    take_step (n := 2) (t := 126) (b := 16076) rfl rfl ArealUCore.ArealUK.chunk_8037 s38
  have s36 : leavesOK ctxLitU 530200000000 3 ((leaves.drop 16072).take 128) 533575000000 3 = true :=
    take_step (n := 2) (t := 128) (b := 16074) rfl rfl ArealUCore.ArealUK.chunk_8036 s37
  have s35 : leavesOK ctxLitU 530150000000 3 ((leaves.drop 16070).take 130) 533575000000 3 = true :=
    take_step (n := 2) (t := 130) (b := 16072) rfl rfl ArealUCore.ArealUK.chunk_8035 s36
  have s34 : leavesOK ctxLitU 530100000000 3 ((leaves.drop 16068).take 132) 533575000000 3 = true :=
    take_step (n := 2) (t := 132) (b := 16070) rfl rfl ArealUCore.ArealUK.chunk_8034 s35
  have s33 : leavesOK ctxLitU 530050000000 3 ((leaves.drop 16066).take 134) 533575000000 3 = true :=
    take_step (n := 2) (t := 134) (b := 16068) rfl rfl ArealUCore.ArealUK.chunk_8033 s34
  have s32 : leavesOK ctxLitU 264975000000 2 ((leaves.drop 16064).take 136) 533575000000 3 = true :=
    take_step (n := 2) (t := 136) (b := 16066) rfl rfl ArealUCore.ArealUK.chunk_8032 s33
  have s31 : leavesOK ctxLitU 529900000000 3 ((leaves.drop 16062).take 138) 533575000000 3 = true :=
    take_step (n := 2) (t := 138) (b := 16064) rfl rfl ArealUCore.ArealUK.chunk_8031 s32
  have s30 : leavesOK ctxLitU 529850000000 3 ((leaves.drop 16060).take 140) 533575000000 3 = true :=
    take_step (n := 2) (t := 140) (b := 16062) rfl rfl ArealUCore.ArealUK.chunk_8030 s31
  have s29 : leavesOK ctxLitU 529800000000 3 ((leaves.drop 16058).take 142) 533575000000 3 = true :=
    take_step (n := 2) (t := 142) (b := 16060) rfl rfl ArealUCore.ArealUK.chunk_8029 s30
  have s28 : leavesOK ctxLitU 529750000000 3 ((leaves.drop 16056).take 144) 533575000000 3 = true :=
    take_step (n := 2) (t := 144) (b := 16058) rfl rfl ArealUCore.ArealUK.chunk_8028 s29
  have s27 : leavesOK ctxLitU 529700000000 3 ((leaves.drop 16054).take 146) 533575000000 3 = true :=
    take_step (n := 2) (t := 146) (b := 16056) rfl rfl ArealUCore.ArealUK.chunk_8027 s28
  have s26 : leavesOK ctxLitU 529650000000 3 ((leaves.drop 16052).take 148) 533575000000 3 = true :=
    take_step (n := 2) (t := 148) (b := 16054) rfl rfl ArealUCore.ArealUK.chunk_8026 s27
  have s25 : leavesOK ctxLitU 529600000000 3 ((leaves.drop 16050).take 150) 533575000000 3 = true :=
    take_step (n := 2) (t := 150) (b := 16052) rfl rfl ArealUCore.ArealUK.chunk_8025 s26
  have s24 : leavesOK ctxLitU 529550000000 3 ((leaves.drop 16048).take 152) 533575000000 3 = true :=
    take_step (n := 2) (t := 152) (b := 16050) rfl rfl ArealUCore.ArealUK.chunk_8024 s25
  have s23 : leavesOK ctxLitU 529500000000 3 ((leaves.drop 16046).take 154) 533575000000 3 = true :=
    take_step (n := 2) (t := 154) (b := 16048) rfl rfl ArealUCore.ArealUK.chunk_8023 s24
  have s22 : leavesOK ctxLitU 529450000000 3 ((leaves.drop 16044).take 156) 533575000000 3 = true :=
    take_step (n := 2) (t := 156) (b := 16046) rfl rfl ArealUCore.ArealUK.chunk_8022 s23
  have s21 : leavesOK ctxLitU 529400000000 3 ((leaves.drop 16042).take 158) 533575000000 3 = true :=
    take_step (n := 2) (t := 158) (b := 16044) rfl rfl ArealUCore.ArealUK.chunk_8021 s22
  have s20 : leavesOK ctxLitU 529350000000 3 ((leaves.drop 16040).take 160) 533575000000 3 = true :=
    take_step (n := 2) (t := 160) (b := 16042) rfl rfl ArealUCore.ArealUK.chunk_8020 s21
  have s19 : leavesOK ctxLitU 529300000000 3 ((leaves.drop 16038).take 162) 533575000000 3 = true :=
    take_step (n := 2) (t := 162) (b := 16040) rfl rfl ArealUCore.ArealUK.chunk_8019 s20
  have s18 : leavesOK ctxLitU 529250000000 3 ((leaves.drop 16036).take 164) 533575000000 3 = true :=
    take_step (n := 2) (t := 164) (b := 16038) rfl rfl ArealUCore.ArealUK.chunk_8018 s19
  have s17 : leavesOK ctxLitU 529200000000 3 ((leaves.drop 16034).take 166) 533575000000 3 = true :=
    take_step (n := 2) (t := 166) (b := 16036) rfl rfl ArealUCore.ArealUK.chunk_8017 s18
  have s16 : leavesOK ctxLitU 264550000000 2 ((leaves.drop 16032).take 168) 533575000000 3 = true :=
    take_step (n := 2) (t := 168) (b := 16034) rfl rfl ArealUCore.ArealUK.chunk_8016 s17
  have s15 : leavesOK ctxLitU 529050000000 3 ((leaves.drop 16030).take 170) 533575000000 3 = true :=
    take_step (n := 2) (t := 170) (b := 16032) rfl rfl ArealUCore.ArealUK.chunk_8015 s16
  have s14 : leavesOK ctxLitU 529000000000 3 ((leaves.drop 16028).take 172) 533575000000 3 = true :=
    take_step (n := 2) (t := 172) (b := 16030) rfl rfl ArealUCore.ArealUK.chunk_8014 s15
  have s13 : leavesOK ctxLitU 528950000000 3 ((leaves.drop 16026).take 174) 533575000000 3 = true :=
    take_step (n := 2) (t := 174) (b := 16028) rfl rfl ArealUCore.ArealUK.chunk_8013 s14
  have s12 : leavesOK ctxLitU 528900000000 3 ((leaves.drop 16024).take 176) 533575000000 3 = true :=
    take_step (n := 2) (t := 176) (b := 16026) rfl rfl ArealUCore.ArealUK.chunk_8012 s13
  have s11 : leavesOK ctxLitU 528850000000 3 ((leaves.drop 16022).take 178) 533575000000 3 = true :=
    take_step (n := 2) (t := 178) (b := 16024) rfl rfl ArealUCore.ArealUK.chunk_8011 s12
  have s10 : leavesOK ctxLitU 528800000000 3 ((leaves.drop 16020).take 180) 533575000000 3 = true :=
    take_step (n := 2) (t := 180) (b := 16022) rfl rfl ArealUCore.ArealUK.chunk_8010 s11
  have s9 : leavesOK ctxLitU 528750000000 3 ((leaves.drop 16018).take 182) 533575000000 3 = true :=
    take_step (n := 2) (t := 182) (b := 16020) rfl rfl ArealUCore.ArealUK.chunk_8009 s10
  have s8 : leavesOK ctxLitU 528700000000 3 ((leaves.drop 16016).take 184) 533575000000 3 = true :=
    take_step (n := 2) (t := 184) (b := 16018) rfl rfl ArealUCore.ArealUK.chunk_8008 s9
  have s7 : leavesOK ctxLitU 528650000000 3 ((leaves.drop 16014).take 186) 533575000000 3 = true :=
    take_step (n := 2) (t := 186) (b := 16016) rfl rfl ArealUCore.ArealUK.chunk_8007 s8
  have s6 : leavesOK ctxLitU 528600000000 3 ((leaves.drop 16012).take 188) 533575000000 3 = true :=
    take_step (n := 2) (t := 188) (b := 16014) rfl rfl ArealUCore.ArealUK.chunk_8006 s7
  have s5 : leavesOK ctxLitU 528550000000 3 ((leaves.drop 16010).take 190) 533575000000 3 = true :=
    take_step (n := 2) (t := 190) (b := 16012) rfl rfl ArealUCore.ArealUK.chunk_8005 s6
  have s4 : leavesOK ctxLitU 528500000000 3 ((leaves.drop 16008).take 192) 533575000000 3 = true :=
    take_step (n := 2) (t := 192) (b := 16010) rfl rfl ArealUCore.ArealUK.chunk_8004 s5
  have s3 : leavesOK ctxLitU 528450000000 3 ((leaves.drop 16006).take 194) 533575000000 3 = true :=
    take_step (n := 2) (t := 194) (b := 16008) rfl rfl ArealUCore.ArealUK.chunk_8003 s4
  have s2 : leavesOK ctxLitU 528400000000 3 ((leaves.drop 16004).take 196) 533575000000 3 = true :=
    take_step (n := 2) (t := 196) (b := 16006) rfl rfl ArealUCore.ArealUK.chunk_8002 s3
  have s1 : leavesOK ctxLitU 528350000000 3 ((leaves.drop 16002).take 198) 533575000000 3 = true :=
    take_step (n := 2) (t := 198) (b := 16004) rfl rfl ArealUCore.ArealUK.chunk_8001 s2
  have s0 : leavesOK ctxLitU 528300000000 3 ((leaves.drop 16000).take 200) 533575000000 3 = true :=
    take_step (n := 2) (t := 200) (b := 16002) rfl rfl ArealUCore.ArealUK.chunk_8000 s1
  exact s0

end Areal.UCert

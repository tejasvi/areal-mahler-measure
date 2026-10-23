import ArealUK.Chunk1000
import ArealUK.Chunk1001
import ArealUK.Chunk1002
import ArealUK.Chunk1003
import ArealUK.Chunk1004
import ArealUK.Chunk1005
import ArealUK.Chunk1006
import ArealUK.Chunk1007
import ArealUK.Chunk1008
import ArealUK.Chunk1009
import ArealUK.Chunk1010
import ArealUK.Chunk1011
import ArealUK.Chunk1012
import ArealUK.Chunk1013
import ArealUK.Chunk1014
import ArealUK.Chunk1015
import ArealUK.Chunk1016
import ArealUK.Chunk1017
import ArealUK.Chunk1018
import ArealUK.Chunk1019
import ArealUK.Chunk1020
import ArealUK.Chunk1021
import ArealUK.Chunk1022
import ArealUK.Chunk1023
import ArealUK.Chunk1024
import ArealUK.Chunk1025
import ArealUK.Chunk1026
import ArealUK.Chunk1027
import ArealUK.Chunk1028
import ArealUK.Chunk1029
import ArealUK.Chunk1030
import ArealUK.Chunk1031
import ArealUK.Chunk1032
import ArealUK.Chunk1033
import ArealUK.Chunk1034
import ArealUK.Chunk1035
import ArealUK.Chunk1036
import ArealUK.Chunk1037
import ArealUK.Chunk1038
import ArealUK.Chunk1039
import ArealUK.Chunk1040
import ArealUK.Chunk1041
import ArealUK.Chunk1042
import ArealUK.Chunk1043
import ArealUK.Chunk1044
import ArealUK.Chunk1045
import ArealUK.Chunk1046
import ArealUK.Chunk1047
import ArealUK.Chunk1048
import ArealUK.Chunk1049
import ArealUK.Chunk1050
import ArealUK.Chunk1051
import ArealUK.Chunk1052
import ArealUK.Chunk1053
import ArealUK.Chunk1054
import ArealUK.Chunk1055
import ArealUK.Chunk1056
import ArealUK.Chunk1057
import ArealUK.Chunk1058
import ArealUK.Chunk1059
import ArealUK.Chunk1060
import ArealUK.Chunk1061
import ArealUK.Chunk1062
import ArealUK.Chunk1063
import ArealUK.Chunk1064
import ArealUK.Chunk1065
import ArealUK.Chunk1066
import ArealUK.Chunk1067
import ArealUK.Chunk1068
import ArealUK.Chunk1069
import ArealUK.Chunk1070
import ArealUK.Chunk1071
import ArealUK.Chunk1072
import ArealUK.Chunk1073
import ArealUK.Chunk1074
import ArealUK.Chunk1075
import ArealUK.Chunk1076
import ArealUK.Chunk1077
import ArealUK.Chunk1078
import ArealUK.Chunk1079
import ArealUK.Chunk1080
import ArealUK.Chunk1081
import ArealUK.Chunk1082
import ArealUK.Chunk1083
import ArealUK.Chunk1084
import ArealUK.Chunk1085
import ArealUK.Chunk1086
import ArealUK.Chunk1087
import ArealUK.Chunk1088
import ArealUK.Chunk1089
import ArealUK.Chunk1090
import ArealUK.Chunk1091
import ArealUK.Chunk1092
import ArealUK.Chunk1093
import ArealUK.Chunk1094
import ArealUK.Chunk1095
import ArealUK.Chunk1096
import ArealUK.Chunk1097
import ArealUK.Chunk1098
import ArealUK.Chunk1099
import Areal.UCert.LeavesKGen

/-! Group 10 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_10 : leavesOK ctxLitU 37706250000 3 ((leaves.drop 2000).take 200) 43868750000 3 = true := by
  have s99 := ArealUCore.ArealUK.chunk_1099
  have s98 : leavesOK ctxLitU 21918750000 2 ((leaves.drop 2196).take 4) 43868750000 3 = true :=
    take_step (n := 2) (t := 4) (b := 2198) rfl rfl ArealUCore.ArealUK.chunk_1098 s99
  have s97 : leavesOK ctxLitU 10950000000 1 ((leaves.drop 2194).take 6) 43868750000 3 = true :=
    take_step (n := 2) (t := 6) (b := 2196) rfl rfl ArealUCore.ArealUK.chunk_1097 s98
  have s96 : leavesOK ctxLitU 5462500000 0 ((leaves.drop 2192).take 8) 43868750000 3 = true :=
    take_step (n := 2) (t := 8) (b := 2194) rfl rfl ArealUCore.ArealUK.chunk_1096 s97
  have s95 : leavesOK ctxLitU 5450000000 0 ((leaves.drop 2190).take 10) 43868750000 3 = true :=
    take_step (n := 2) (t := 10) (b := 2192) rfl rfl ArealUCore.ArealUK.chunk_1095 s96
  have s94 : leavesOK ctxLitU 22286877486988 12 ((leaves.drop 2188).take 12) 43868750000 3 = true :=
    take_step (n := 2) (t := 12) (b := 2190) rfl rfl ArealUCore.ArealUK.chunk_1094 s95
  have s93 : leavesOK ctxLitU 22272000000000 12 ((leaves.drop 2186).take 14) 43868750000 3 = true :=
    take_step (n := 2) (t := 14) (b := 2188) rfl rfl ArealUCore.ArealUK.chunk_1093 s94
  have s92 : leavesOK ctxLitU 5425000000 0 ((leaves.drop 2184).take 16) 43868750000 3 = true :=
    take_step (n := 2) (t := 16) (b := 2186) rfl rfl ArealUCore.ArealUK.chunk_1092 s93
  have s91 : leavesOK ctxLitU 22174060367764 12 ((leaves.drop 2182).take 18) 43868750000 3 = true :=
    take_step (n := 2) (t := 18) (b := 2184) rfl rfl ArealUCore.ArealUK.chunk_1091 s92
  have s90 : leavesOK ctxLitU 22169600000000 12 ((leaves.drop 2180).take 20) 43868750000 3 = true :=
    take_step (n := 2) (t := 20) (b := 2182) rfl rfl ArealUCore.ArealUK.chunk_1090 s91
  have s89 : leavesOK ctxLitU 10806250000 1 ((leaves.drop 2178).take 22) 43868750000 3 = true :=
    take_step (n := 2) (t := 22) (b := 2180) rfl rfl ArealUCore.ArealUK.chunk_1089 s90
  have s88 : leavesOK ctxLitU 43187500000 3 ((leaves.drop 2176).take 24) 43868750000 3 = true :=
    take_step (n := 2) (t := 24) (b := 2178) rfl rfl ArealUCore.ArealUK.chunk_1088 s89
  have s87 : leavesOK ctxLitU 43162500000 3 ((leaves.drop 2174).take 26) 43868750000 3 = true :=
    take_step (n := 2) (t := 26) (b := 2176) rfl rfl ArealUCore.ArealUK.chunk_1087 s88
  have s86 : leavesOK ctxLitU 86287500000 4 ((leaves.drop 2172).take 28) 43868750000 3 = true :=
    take_step (n := 2) (t := 28) (b := 2174) rfl rfl ArealUCore.ArealUK.chunk_1086 s87
  have s85 : leavesOK ctxLitU 172550000000 5 ((leaves.drop 2170).take 30) 43868750000 3 = true :=
    take_step (n := 2) (t := 30) (b := 2172) rfl rfl ArealUCore.ArealUK.chunk_1085 s86
  have s84 : leavesOK ctxLitU 172525000000 5 ((leaves.drop 2168).take 32) 43868750000 3 = true :=
    take_step (n := 2) (t := 32) (b := 2170) rfl rfl ArealUCore.ArealUK.chunk_1084 s85
  have s83 : leavesOK ctxLitU 43112500000 3 ((leaves.drop 2166).take 34) 43868750000 3 = true :=
    take_step (n := 2) (t := 34) (b := 2168) rfl rfl ArealUCore.ArealUK.chunk_1083 s84
  have s82 : leavesOK ctxLitU 21537500000 2 ((leaves.drop 2164).take 36) 43868750000 3 = true :=
    take_step (n := 2) (t := 36) (b := 2166) rfl rfl ArealUCore.ArealUK.chunk_1082 s83
  have s81 : leavesOK ctxLitU 43037500000 3 ((leaves.drop 2162).take 38) 43868750000 3 = true :=
    take_step (n := 2) (t := 38) (b := 2164) rfl rfl ArealUCore.ArealUK.chunk_1081 s82
  have s80 : leavesOK ctxLitU 86037500000 4 ((leaves.drop 2160).take 40) 43868750000 3 = true :=
    take_step (n := 2) (t := 40) (b := 2162) rfl rfl ArealUCore.ArealUK.chunk_1080 s81
  have s79 : leavesOK ctxLitU 172050000000 5 ((leaves.drop 2158).take 42) 43868750000 3 = true :=
    take_step (n := 2) (t := 42) (b := 2160) rfl rfl ArealUCore.ArealUK.chunk_1079 s80
  have s78 : leavesOK ctxLitU 86000000000 4 ((leaves.drop 2156).take 44) 43868750000 3 = true :=
    take_step (n := 2) (t := 44) (b := 2158) rfl rfl ArealUCore.ArealUK.chunk_1078 s79
  have s77 : leavesOK ctxLitU 175996696382716 15 ((leaves.drop 2154).take 46) 43868750000 3 = true :=
    take_step (n := 2) (t := 46) (b := 2156) rfl rfl ArealUCore.ArealUK.chunk_1077 s78
  have s76 : leavesOK ctxLitU 43900696382716 13 ((leaves.drop 2152).take 48) 43868750000 3 = true :=
    take_step (n := 2) (t := 48) (b := 2154) rfl rfl ArealUCore.ArealUK.chunk_1076 s77
  have s75 : leavesOK ctxLitU 43863948191355 13 ((leaves.drop 2150).take 50) 43868750000 3 = true :=
    take_step (n := 2) (t := 50) (b := 2152) rfl rfl ArealUCore.ArealUK.chunk_1075 s76
  have s74 : leavesOK ctxLitU 42787500000 3 ((leaves.drop 2148).take 52) 43868750000 3 = true :=
    take_step (n := 2) (t := 52) (b := 2150) rfl rfl ArealUCore.ArealUK.chunk_1074 s75
  have s73 : leavesOK ctxLitU 85537500000 4 ((leaves.drop 2146).take 54) 43868750000 3 = true :=
    take_step (n := 2) (t := 54) (b := 2148) rfl rfl ArealUCore.ArealUK.chunk_1073 s74
  have s72 : leavesOK ctxLitU 171037500000 5 ((leaves.drop 2144).take 56) 43868750000 3 = true :=
    take_step (n := 2) (t := 56) (b := 2146) rfl rfl ArealUCore.ArealUK.chunk_1072 s73
  have s71 : leavesOK ctxLitU 85500000000 4 ((leaves.drop 2142).take 58) 43868750000 3 = true :=
    take_step (n := 2) (t := 58) (b := 2144) rfl rfl ArealUCore.ArealUK.chunk_1071 s72
  have s70 : leavesOK ctxLitU 42725000000 3 ((leaves.drop 2140).take 60) 43868750000 3 = true :=
    take_step (n := 2) (t := 60) (b := 2142) rfl rfl ArealUCore.ArealUK.chunk_1070 s71
  have s69 : leavesOK ctxLitU 21337500000 2 ((leaves.drop 2138).take 62) 43868750000 3 = true :=
    take_step (n := 2) (t := 62) (b := 2140) rfl rfl ArealUCore.ArealUK.chunk_1069 s70
  have s68 : leavesOK ctxLitU 21312500000 2 ((leaves.drop 2136).take 64) 43868750000 3 = true :=
    take_step (n := 2) (t := 64) (b := 2138) rfl rfl ArealUCore.ArealUK.chunk_1068 s69
  have s67 : leavesOK ctxLitU 85212500000 4 ((leaves.drop 2134).take 66) 43868750000 3 = true :=
    take_step (n := 2) (t := 66) (b := 2136) rfl rfl ArealUCore.ArealUK.chunk_1067 s68
  have s66 : leavesOK ctxLitU 85193750000 4 ((leaves.drop 2132).take 68) 43868750000 3 = true :=
    take_step (n := 2) (t := 68) (b := 2134) rfl rfl ArealUCore.ArealUK.chunk_1066 s67
  have s65 : leavesOK ctxLitU 42587500000 3 ((leaves.drop 2130).take 70) 43868750000 3 = true :=
    take_step (n := 2) (t := 70) (b := 2132) rfl rfl ArealUCore.ArealUK.chunk_1065 s66
  have s64 : leavesOK ctxLitU 42575000000 3 ((leaves.drop 2128).take 72) 43868750000 3 = true :=
    take_step (n := 2) (t := 72) (b := 2130) rfl rfl ArealUCore.ArealUK.chunk_1064 s65
  have s63 : leavesOK ctxLitU 21275000000 2 ((leaves.drop 2126).take 74) 43868750000 3 = true :=
    take_step (n := 2) (t := 74) (b := 2128) rfl rfl ArealUCore.ArealUK.chunk_1063 s64
  have s62 : leavesOK ctxLitU 21262500000 2 ((leaves.drop 2124).take 76) 43868750000 3 = true :=
    take_step (n := 2) (t := 76) (b := 2126) rfl rfl ArealUCore.ArealUK.chunk_1062 s63
  have s61 : leavesOK ctxLitU 42512500000 3 ((leaves.drop 2122).take 78) 43868750000 3 = true :=
    take_step (n := 2) (t := 78) (b := 2124) rfl rfl ArealUCore.ArealUK.chunk_1061 s62
  have s60 : leavesOK ctxLitU 85006250000 4 ((leaves.drop 2120).take 80) 43868750000 3 = true :=
    take_step (n := 2) (t := 80) (b := 2122) rfl rfl ArealUCore.ArealUK.chunk_1060 s61
  have s59 : leavesOK ctxLitU 42493750000 3 ((leaves.drop 2118).take 82) 43868750000 3 = true :=
    take_step (n := 2) (t := 82) (b := 2120) rfl rfl ArealUCore.ArealUK.chunk_1059 s60
  have s58 : leavesOK ctxLitU 21237500000 2 ((leaves.drop 2116).take 84) 43868750000 3 = true :=
    take_step (n := 2) (t := 84) (b := 2118) rfl rfl ArealUCore.ArealUK.chunk_1058 s59
  have s57 : leavesOK ctxLitU 21225000000 2 ((leaves.drop 2114).take 86) 43868750000 3 = true :=
    take_step (n := 2) (t := 86) (b := 2116) rfl rfl ArealUCore.ArealUK.chunk_1057 s58
  have s56 : leavesOK ctxLitU 42431250000 3 ((leaves.drop 2112).take 88) 43868750000 3 = true :=
    take_step (n := 2) (t := 88) (b := 2114) rfl rfl ArealUCore.ArealUK.chunk_1056 s57
  have s55 : leavesOK ctxLitU 84843750000 4 ((leaves.drop 2110).take 90) 43868750000 3 = true :=
    take_step (n := 2) (t := 90) (b := 2112) rfl rfl ArealUCore.ArealUK.chunk_1055 s56
  have s54 : leavesOK ctxLitU 42412500000 3 ((leaves.drop 2108).take 92) 43868750000 3 = true :=
    take_step (n := 2) (t := 92) (b := 2110) rfl rfl ArealUCore.ArealUK.chunk_1054 s55
  have s53 : leavesOK ctxLitU 42400000000 3 ((leaves.drop 2106).take 94) 43868750000 3 = true :=
    take_step (n := 2) (t := 94) (b := 2108) rfl rfl ArealUCore.ArealUK.chunk_1053 s54
  have s52 : leavesOK ctxLitU 43345064280340 13 ((leaves.drop 2104).take 96) 43868750000 3 = true :=
    take_step (n := 2) (t := 96) (b := 2106) rfl rfl ArealUCore.ArealUK.chunk_1052 s53
  have s51 : leavesOK ctxLitU 21657600000000 12 ((leaves.drop 2102).take 98) 43868750000 3 = true :=
    take_step (n := 2) (t := 98) (b := 2104) rfl rfl ArealUCore.ArealUK.chunk_1051 s52
  have s50 : leavesOK ctxLitU 42275000000 3 ((leaves.drop 2100).take 100) 43868750000 3 = true :=
    take_step (n := 2) (t := 100) (b := 2102) rfl rfl ArealUCore.ArealUK.chunk_1050 s51
  have s49 : leavesOK ctxLitU 84512500000 4 ((leaves.drop 2098).take 102) 43868750000 3 = true :=
    take_step (n := 2) (t := 102) (b := 2100) rfl rfl ArealUCore.ArealUK.chunk_1049 s50
  have s48 : leavesOK ctxLitU 168987500000 5 ((leaves.drop 2096).take 104) 43868750000 3 = true :=
    take_step (n := 2) (t := 104) (b := 2098) rfl rfl ArealUCore.ArealUK.chunk_1048 s49
  have s47 : leavesOK ctxLitU 84475000000 4 ((leaves.drop 2094).take 106) 43868750000 3 = true :=
    take_step (n := 2) (t := 106) (b := 2096) rfl rfl ArealUCore.ArealUK.chunk_1047 s48
  have s46 : leavesOK ctxLitU 21100000000 2 ((leaves.drop 2092).take 108) 43868750000 3 = true :=
    take_step (n := 2) (t := 108) (b := 2094) rfl rfl ArealUCore.ArealUK.chunk_1046 s47
  have s45 : leavesOK ctxLitU 21081250000 2 ((leaves.drop 2090).take 110) 43868750000 3 = true :=
    take_step (n := 2) (t := 110) (b := 2092) rfl rfl ArealUCore.ArealUK.chunk_1045 s46
  have s44 : leavesOK ctxLitU 42143750000 3 ((leaves.drop 2088).take 112) 43868750000 3 = true :=
    take_step (n := 2) (t := 112) (b := 2090) rfl rfl ArealUCore.ArealUK.chunk_1044 s45
  have s43 : leavesOK ctxLitU 42131250000 3 ((leaves.drop 2086).take 114) 43868750000 3 = true :=
    take_step (n := 2) (t := 114) (b := 2088) rfl rfl ArealUCore.ArealUK.chunk_1043 s44
  have s42 : leavesOK ctxLitU 42118750000 3 ((leaves.drop 2084).take 116) 43868750000 3 = true :=
    take_step (n := 2) (t := 116) (b := 2086) rfl rfl ArealUCore.ArealUK.chunk_1042 s43
  have s41 : leavesOK ctxLitU 21050000000 2 ((leaves.drop 2082).take 118) 43868750000 3 = true :=
    take_step (n := 2) (t := 118) (b := 2084) rfl rfl ArealUCore.ArealUK.chunk_1041 s42
  have s40 : leavesOK ctxLitU 42087500000 3 ((leaves.drop 2080).take 120) 43868750000 3 = true :=
    take_step (n := 2) (t := 120) (b := 2082) rfl rfl ArealUCore.ArealUK.chunk_1040 s41
  have s39 : leavesOK ctxLitU 42075000000 3 ((leaves.drop 2078).take 122) 43868750000 3 = true :=
    take_step (n := 2) (t := 122) (b := 2080) rfl rfl ArealUCore.ArealUK.chunk_1039 s40
  have s38 : leavesOK ctxLitU 42062500000 3 ((leaves.drop 2076).take 124) 43868750000 3 = true :=
    take_step (n := 2) (t := 124) (b := 2078) rfl rfl ArealUCore.ArealUK.chunk_1038 s39
  have s37 : leavesOK ctxLitU 42050000000 3 ((leaves.drop 2074).take 126) 43868750000 3 = true :=
    take_step (n := 2) (t := 126) (b := 2076) rfl rfl ArealUCore.ArealUK.chunk_1037 s38
  have s36 : leavesOK ctxLitU 21012500000 2 ((leaves.drop 2072).take 128) 43868750000 3 = true :=
    take_step (n := 2) (t := 128) (b := 2074) rfl rfl ArealUCore.ArealUK.chunk_1036 s37
  have s35 : leavesOK ctxLitU 5243750000 0 ((leaves.drop 2070).take 130) 43868750000 3 = true :=
    take_step (n := 2) (t := 130) (b := 2072) rfl rfl ArealUCore.ArealUK.chunk_1035 s36
  have s34 : leavesOK ctxLitU 5231250000 0 ((leaves.drop 2068).take 132) 43868750000 3 = true :=
    take_step (n := 2) (t := 132) (b := 2070) rfl rfl ArealUCore.ArealUK.chunk_1034 s35
  have s33 : leavesOK ctxLitU 5218750000 0 ((leaves.drop 2066).take 134) 43868750000 3 = true :=
    take_step (n := 2) (t := 134) (b := 2068) rfl rfl ArealUCore.ArealUK.chunk_1033 s34
  have s32 : leavesOK ctxLitU 5206250000 0 ((leaves.drop 2064).take 136) 43868750000 3 = true :=
    take_step (n := 2) (t := 136) (b := 2066) rfl rfl ArealUCore.ArealUK.chunk_1032 s33
  have s31 : leavesOK ctxLitU 5193750000 0 ((leaves.drop 2062).take 138) 43868750000 3 = true :=
    take_step (n := 2) (t := 138) (b := 2064) rfl rfl ArealUCore.ArealUK.chunk_1031 s32
  have s30 : leavesOK ctxLitU 5181250000 0 ((leaves.drop 2060).take 140) 43868750000 3 = true :=
    take_step (n := 2) (t := 140) (b := 2062) rfl rfl ArealUCore.ArealUK.chunk_1030 s31
  have s29 : leavesOK ctxLitU 5162500000 0 ((leaves.drop 2058).take 142) 43868750000 3 = true :=
    take_step (n := 2) (t := 142) (b := 2060) rfl rfl ArealUCore.ArealUK.chunk_1029 s30
  have s28 : leavesOK ctxLitU 5125000000 0 ((leaves.drop 2056).take 144) 43868750000 3 = true :=
    take_step (n := 2) (t := 144) (b := 2058) rfl rfl ArealUCore.ArealUK.chunk_1028 s29
  have s27 : leavesOK ctxLitU 5075000000 0 ((leaves.drop 2054).take 146) 43868750000 3 = true :=
    take_step (n := 2) (t := 146) (b := 2056) rfl rfl ArealUCore.ArealUK.chunk_1027 s28
  have s26 : leavesOK ctxLitU 5025000000 0 ((leaves.drop 2052).take 148) 43868750000 3 = true :=
    take_step (n := 2) (t := 148) (b := 2054) rfl rfl ArealUCore.ArealUK.chunk_1026 s27
  have s25 : leavesOK ctxLitU 20479999999999 12 ((leaves.drop 2050).take 150) 43868750000 3 = true :=
    take_step (n := 2) (t := 150) (b := 2052) rfl rfl ArealUCore.ArealUK.chunk_1025 s26
  have s24 : leavesOK ctxLitU 4950000000 0 ((leaves.drop 2048).take 152) 43868750000 3 = true :=
    take_step (n := 2) (t := 152) (b := 2050) rfl rfl ArealUCore.ArealUK.chunk_1024 s25
  have s23 : leavesOK ctxLitU 4900000000 0 ((leaves.drop 2046).take 154) 43868750000 3 = true :=
    take_step (n := 2) (t := 154) (b := 2048) rfl rfl ArealUCore.ArealUK.chunk_1023 s24
  have s22 : leavesOK ctxLitU 4850000000 0 ((leaves.drop 2044).take 156) 43868750000 3 = true :=
    take_step (n := 2) (t := 156) (b := 2046) rfl rfl ArealUCore.ArealUK.chunk_1022 s23
  have s21 : leavesOK ctxLitU 4825000000 0 ((leaves.drop 2042).take 158) 43868750000 3 = true :=
    take_step (n := 2) (t := 158) (b := 2044) rfl rfl ArealUCore.ArealUK.chunk_1021 s22
  have s20 : leavesOK ctxLitU 4812500000 0 ((leaves.drop 2040).take 160) 43868750000 3 = true :=
    take_step (n := 2) (t := 160) (b := 2042) rfl rfl ArealUCore.ArealUK.chunk_1020 s21
  have s19 : leavesOK ctxLitU 4800000000 0 ((leaves.drop 2038).take 162) 43868750000 3 = true :=
    take_step (n := 2) (t := 162) (b := 2040) rfl rfl ArealUCore.ArealUK.chunk_1019 s20
  have s18 : leavesOK ctxLitU 4787500000 0 ((leaves.drop 2036).take 164) 43868750000 3 = true :=
    take_step (n := 2) (t := 164) (b := 2038) rfl rfl ArealUCore.ArealUK.chunk_1018 s19
  have s17 : leavesOK ctxLitU 4775000000 0 ((leaves.drop 2034).take 166) 43868750000 3 = true :=
    take_step (n := 2) (t := 166) (b := 2036) rfl rfl ArealUCore.ArealUK.chunk_1017 s18
  have s16 : leavesOK ctxLitU 4762500000 0 ((leaves.drop 2032).take 168) 43868750000 3 = true :=
    take_step (n := 2) (t := 168) (b := 2034) rfl rfl ArealUCore.ArealUK.chunk_1016 s17
  have s15 : leavesOK ctxLitU 4750000000 0 ((leaves.drop 2030).take 170) 43868750000 3 = true :=
    take_step (n := 2) (t := 170) (b := 2032) rfl rfl ArealUCore.ArealUK.chunk_1015 s16
  have s14 : leavesOK ctxLitU 19406947202075 12 ((leaves.drop 2028).take 172) 43868750000 3 = true :=
    take_step (n := 2) (t := 172) (b := 2030) rfl rfl ArealUCore.ArealUK.chunk_1014 s15
  have s13 : leavesOK ctxLitU 19404800000000 12 ((leaves.drop 2026).take 174) 43868750000 3 = true :=
    take_step (n := 2) (t := 174) (b := 2028) rfl rfl ArealUCore.ArealUK.chunk_1013 s14
  have s12 : leavesOK ctxLitU 9462500000 1 ((leaves.drop 2024).take 176) 43868750000 3 = true :=
    take_step (n := 2) (t := 176) (b := 2026) rfl rfl ArealUCore.ArealUK.chunk_1012 s13
  have s11 : leavesOK ctxLitU 37837500000 3 ((leaves.drop 2022).take 178) 43868750000 3 = true :=
    take_step (n := 2) (t := 178) (b := 2024) rfl rfl ArealUCore.ArealUK.chunk_1011 s12
  have s10 : leavesOK ctxLitU 37818750000 3 ((leaves.drop 2020).take 180) 43868750000 3 = true :=
    take_step (n := 2) (t := 180) (b := 2022) rfl rfl ArealUCore.ArealUK.chunk_1010 s11
  have s9 : leavesOK ctxLitU 75625000000 4 ((leaves.drop 2018).take 182) 43868750000 3 = true :=
    take_step (n := 2) (t := 182) (b := 2020) rfl rfl ArealUCore.ArealUK.chunk_1009 s10
  have s8 : leavesOK ctxLitU 75612500000 4 ((leaves.drop 2016).take 184) 43868750000 3 = true :=
    take_step (n := 2) (t := 184) (b := 2018) rfl rfl ArealUCore.ArealUK.chunk_1008 s9
  have s7 : leavesOK ctxLitU 18893750000 2 ((leaves.drop 2014).take 186) 43868750000 3 = true :=
    take_step (n := 2) (t := 186) (b := 2016) rfl rfl ArealUCore.ArealUK.chunk_1007 s8
  have s6 : leavesOK ctxLitU 37775000000 3 ((leaves.drop 2012).take 188) 43868750000 3 = true :=
    take_step (n := 2) (t := 188) (b := 2014) rfl rfl ArealUCore.ArealUK.chunk_1006 s7
  have s5 : leavesOK ctxLitU 75531250000 4 ((leaves.drop 2010).take 190) 43868750000 3 = true :=
    take_step (n := 2) (t := 190) (b := 2012) rfl rfl ArealUCore.ArealUK.chunk_1005 s6
  have s4 : leavesOK ctxLitU 37756250000 3 ((leaves.drop 2008).take 192) 43868750000 3 = true :=
    take_step (n := 2) (t := 192) (b := 2010) rfl rfl ArealUCore.ArealUK.chunk_1004 s5
  have s3 : leavesOK ctxLitU 37743750000 3 ((leaves.drop 2006).take 194) 43868750000 3 = true :=
    take_step (n := 2) (t := 194) (b := 2008) rfl rfl ArealUCore.ArealUK.chunk_1003 s4
  have s2 : leavesOK ctxLitU 37731250000 3 ((leaves.drop 2004).take 196) 43868750000 3 = true :=
    take_step (n := 2) (t := 196) (b := 2006) rfl rfl ArealUCore.ArealUK.chunk_1002 s3
  have s1 : leavesOK ctxLitU 37718750000 3 ((leaves.drop 2002).take 198) 43868750000 3 = true :=
    take_step (n := 2) (t := 198) (b := 2004) rfl rfl ArealUCore.ArealUK.chunk_1001 s2
  have s0 : leavesOK ctxLitU 37706250000 3 ((leaves.drop 2000).take 200) 43868750000 3 = true :=
    take_step (n := 2) (t := 200) (b := 2002) rfl rfl ArealUCore.ArealUK.chunk_1000 s1
  exact s0

end Areal.UCert

import ArealUK.Chunk0000
import ArealUK.Chunk0001
import ArealUK.Chunk0002
import ArealUK.Chunk0003
import ArealUK.Chunk0004
import ArealUK.Chunk0005
import ArealUK.Chunk0006
import ArealUK.Chunk0007
import ArealUK.Chunk0008
import ArealUK.Chunk0009
import ArealUK.Chunk0010
import ArealUK.Chunk0011
import ArealUK.Chunk0012
import ArealUK.Chunk0013
import ArealUK.Chunk0014
import ArealUK.Chunk0015
import ArealUK.Chunk0016
import ArealUK.Chunk0017
import ArealUK.Chunk0018
import ArealUK.Chunk0019
import ArealUK.Chunk0020
import ArealUK.Chunk0021
import ArealUK.Chunk0022
import ArealUK.Chunk0023
import ArealUK.Chunk0024
import ArealUK.Chunk0025
import ArealUK.Chunk0026
import ArealUK.Chunk0027
import ArealUK.Chunk0028
import ArealUK.Chunk0029
import ArealUK.Chunk0030
import ArealUK.Chunk0031
import ArealUK.Chunk0032
import ArealUK.Chunk0033
import ArealUK.Chunk0034
import ArealUK.Chunk0035
import ArealUK.Chunk0036
import ArealUK.Chunk0037
import ArealUK.Chunk0038
import ArealUK.Chunk0039
import ArealUK.Chunk0040
import ArealUK.Chunk0041
import ArealUK.Chunk0042
import ArealUK.Chunk0043
import ArealUK.Chunk0044
import ArealUK.Chunk0045
import ArealUK.Chunk0046
import ArealUK.Chunk0047
import ArealUK.Chunk0048
import ArealUK.Chunk0049
import ArealUK.Chunk0050
import ArealUK.Chunk0051
import ArealUK.Chunk0052
import ArealUK.Chunk0053
import ArealUK.Chunk0054
import ArealUK.Chunk0055
import ArealUK.Chunk0056
import ArealUK.Chunk0057
import ArealUK.Chunk0058
import ArealUK.Chunk0059
import ArealUK.Chunk0060
import ArealUK.Chunk0061
import ArealUK.Chunk0062
import ArealUK.Chunk0063
import ArealUK.Chunk0064
import ArealUK.Chunk0065
import ArealUK.Chunk0066
import ArealUK.Chunk0067
import ArealUK.Chunk0068
import ArealUK.Chunk0069
import ArealUK.Chunk0070
import ArealUK.Chunk0071
import ArealUK.Chunk0072
import ArealUK.Chunk0073
import ArealUK.Chunk0074
import ArealUK.Chunk0075
import ArealUK.Chunk0076
import ArealUK.Chunk0077
import ArealUK.Chunk0078
import ArealUK.Chunk0079
import ArealUK.Chunk0080
import ArealUK.Chunk0081
import ArealUK.Chunk0082
import ArealUK.Chunk0083
import ArealUK.Chunk0084
import ArealUK.Chunk0085
import ArealUK.Chunk0086
import ArealUK.Chunk0087
import ArealUK.Chunk0088
import ArealUK.Chunk0089
import ArealUK.Chunk0090
import ArealUK.Chunk0091
import ArealUK.Chunk0092
import ArealUK.Chunk0093
import ArealUK.Chunk0094
import ArealUK.Chunk0095
import ArealUK.Chunk0096
import ArealUK.Chunk0097
import ArealUK.Chunk0098
import ArealUK.Chunk0099
import Areal.UCert.LeavesKGen

/-! Group 0 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_00 : leavesOK ctxLitU 1481250000 0 ((leaves.drop 0).take 200) 29075000000 4 = true := by
  have s99 := ArealUCore.ArealUK.chunk_0099
  have s98 : leavesOK ctxLitU 29025000000 4 ((leaves.drop 196).take 4) 29075000000 4 = true :=
    take_step (n := 2) (t := 4) (b := 198) rfl rfl ArealUCore.ArealUK.chunk_0098 s99
  have s97 : leavesOK ctxLitU 29000000000 4 ((leaves.drop 194).take 6) 29075000000 4 = true :=
    take_step (n := 2) (t := 6) (b := 196) rfl rfl ArealUCore.ArealUK.chunk_0097 s98
  have s96 : leavesOK ctxLitU 28975000000 4 ((leaves.drop 192).take 8) 29075000000 4 = true :=
    take_step (n := 2) (t := 8) (b := 194) rfl rfl ArealUCore.ArealUK.chunk_0096 s97
  have s95 : leavesOK ctxLitU 28950000000 4 ((leaves.drop 190).take 10) 29075000000 4 = true :=
    take_step (n := 2) (t := 10) (b := 192) rfl rfl ArealUCore.ArealUK.chunk_0095 s96
  have s94 : leavesOK ctxLitU 28925000000 4 ((leaves.drop 188).take 12) 29075000000 4 = true :=
    take_step (n := 2) (t := 12) (b := 190) rfl rfl ArealUCore.ArealUK.chunk_0094 s95
  have s93 : leavesOK ctxLitU 28900000000 4 ((leaves.drop 186).take 14) 29075000000 4 = true :=
    take_step (n := 2) (t := 14) (b := 188) rfl rfl ArealUCore.ArealUK.chunk_0093 s94
  have s92 : leavesOK ctxLitU 28875000000 4 ((leaves.drop 184).take 16) 29075000000 4 = true :=
    take_step (n := 2) (t := 16) (b := 186) rfl rfl ArealUCore.ArealUK.chunk_0092 s93
  have s91 : leavesOK ctxLitU 28850000000 4 ((leaves.drop 182).take 18) 29075000000 4 = true :=
    take_step (n := 2) (t := 18) (b := 184) rfl rfl ArealUCore.ArealUK.chunk_0091 s92
  have s90 : leavesOK ctxLitU 28825000000 4 ((leaves.drop 180).take 20) 29075000000 4 = true :=
    take_step (n := 2) (t := 20) (b := 182) rfl rfl ArealUCore.ArealUK.chunk_0090 s91
  have s89 : leavesOK ctxLitU 28800000000 4 ((leaves.drop 178).take 22) 29075000000 4 = true :=
    take_step (n := 2) (t := 22) (b := 180) rfl rfl ArealUCore.ArealUK.chunk_0089 s90
  have s88 : leavesOK ctxLitU 14387500000 3 ((leaves.drop 176).take 24) 29075000000 4 = true :=
    take_step (n := 2) (t := 24) (b := 178) rfl rfl ArealUCore.ArealUK.chunk_0088 s89
  have s87 : leavesOK ctxLitU 14375000000 3 ((leaves.drop 174).take 26) 29075000000 4 = true :=
    take_step (n := 2) (t := 26) (b := 176) rfl rfl ArealUCore.ArealUK.chunk_0087 s88
  have s86 : leavesOK ctxLitU 14362500000 3 ((leaves.drop 172).take 28) 29075000000 4 = true :=
    take_step (n := 2) (t := 28) (b := 174) rfl rfl ArealUCore.ArealUK.chunk_0086 s87
  have s85 : leavesOK ctxLitU 14350000000 3 ((leaves.drop 170).take 30) 29075000000 4 = true :=
    take_step (n := 2) (t := 30) (b := 172) rfl rfl ArealUCore.ArealUK.chunk_0085 s86
  have s84 : leavesOK ctxLitU 14337500000 3 ((leaves.drop 168).take 32) 29075000000 4 = true :=
    take_step (n := 2) (t := 32) (b := 170) rfl rfl ArealUCore.ArealUK.chunk_0084 s85
  have s83 : leavesOK ctxLitU 14325000000 3 ((leaves.drop 166).take 34) 29075000000 4 = true :=
    take_step (n := 2) (t := 34) (b := 168) rfl rfl ArealUCore.ArealUK.chunk_0083 s84
  have s82 : leavesOK ctxLitU 14312500000 3 ((leaves.drop 164).take 36) 29075000000 4 = true :=
    take_step (n := 2) (t := 36) (b := 166) rfl rfl ArealUCore.ArealUK.chunk_0082 s83
  have s81 : leavesOK ctxLitU 14300000000 3 ((leaves.drop 162).take 38) 29075000000 4 = true :=
    take_step (n := 2) (t := 38) (b := 164) rfl rfl ArealUCore.ArealUK.chunk_0081 s82
  have s80 : leavesOK ctxLitU 14287500000 3 ((leaves.drop 160).take 40) 29075000000 4 = true :=
    take_step (n := 2) (t := 40) (b := 162) rfl rfl ArealUCore.ArealUK.chunk_0080 s81
  have s79 : leavesOK ctxLitU 14275000000 3 ((leaves.drop 158).take 42) 29075000000 4 = true :=
    take_step (n := 2) (t := 42) (b := 160) rfl rfl ArealUCore.ArealUK.chunk_0079 s80
  have s78 : leavesOK ctxLitU 14262500000 3 ((leaves.drop 156).take 44) 29075000000 4 = true :=
    take_step (n := 2) (t := 44) (b := 158) rfl rfl ArealUCore.ArealUK.chunk_0078 s79
  have s77 : leavesOK ctxLitU 14250000000 3 ((leaves.drop 154).take 46) 29075000000 4 = true :=
    take_step (n := 2) (t := 46) (b := 156) rfl rfl ArealUCore.ArealUK.chunk_0077 s78
  have s76 : leavesOK ctxLitU 14237500000 3 ((leaves.drop 152).take 48) 29075000000 4 = true :=
    take_step (n := 2) (t := 48) (b := 154) rfl rfl ArealUCore.ArealUK.chunk_0076 s77
  have s75 : leavesOK ctxLitU 14225000000 3 ((leaves.drop 150).take 50) 29075000000 4 = true :=
    take_step (n := 2) (t := 50) (b := 152) rfl rfl ArealUCore.ArealUK.chunk_0075 s76
  have s74 : leavesOK ctxLitU 28437500000 4 ((leaves.drop 148).take 52) 29075000000 4 = true :=
    take_step (n := 2) (t := 52) (b := 150) rfl rfl ArealUCore.ArealUK.chunk_0074 s75
  have s73 : leavesOK ctxLitU 14206250000 3 ((leaves.drop 146).take 54) 29075000000 4 = true :=
    take_step (n := 2) (t := 54) (b := 148) rfl rfl ArealUCore.ArealUK.chunk_0073 s74
  have s72 : leavesOK ctxLitU 7093750000 2 ((leaves.drop 144).take 56) 29075000000 4 = true :=
    take_step (n := 2) (t := 56) (b := 146) rfl rfl ArealUCore.ArealUK.chunk_0072 s73
  have s71 : leavesOK ctxLitU 7081250000 2 ((leaves.drop 142).take 58) 29075000000 4 = true :=
    take_step (n := 2) (t := 58) (b := 144) rfl rfl ArealUCore.ArealUK.chunk_0071 s72
  have s70 : leavesOK ctxLitU 7068750000 2 ((leaves.drop 140).take 60) 29075000000 4 = true :=
    take_step (n := 2) (t := 60) (b := 142) rfl rfl ArealUCore.ArealUK.chunk_0070 s71
  have s69 : leavesOK ctxLitU 28262500000 4 ((leaves.drop 138).take 62) 29075000000 4 = true :=
    take_step (n := 2) (t := 62) (b := 140) rfl rfl ArealUCore.ArealUK.chunk_0069 s70
  have s68 : leavesOK ctxLitU 28250000000 4 ((leaves.drop 136).take 64) 29075000000 4 = true :=
    take_step (n := 2) (t := 64) (b := 138) rfl rfl ArealUCore.ArealUK.chunk_0068 s69
  have s67 : leavesOK ctxLitU 14112500000 3 ((leaves.drop 134).take 66) 29075000000 4 = true :=
    take_step (n := 2) (t := 66) (b := 136) rfl rfl ArealUCore.ArealUK.chunk_0067 s68
  have s66 : leavesOK ctxLitU 14100000000 3 ((leaves.drop 132).take 68) 29075000000 4 = true :=
    take_step (n := 2) (t := 68) (b := 134) rfl rfl ArealUCore.ArealUK.chunk_0066 s67
  have s65 : leavesOK ctxLitU 7037500000 2 ((leaves.drop 130).take 70) 29075000000 4 = true :=
    take_step (n := 2) (t := 70) (b := 132) rfl rfl ArealUCore.ArealUK.chunk_0065 s66
  have s64 : leavesOK ctxLitU 1750000000 0 ((leaves.drop 128).take 72) 29075000000 4 = true :=
    take_step (n := 2) (t := 72) (b := 130) rfl rfl ArealUCore.ArealUK.chunk_0064 s65
  have s63 : leavesOK ctxLitU 7160068093493 12 ((leaves.drop 126).take 74) 29075000000 4 = true :=
    take_step (n := 2) (t := 74) (b := 128) rfl rfl ArealUCore.ArealUK.chunk_0063 s64
  have s62 : leavesOK ctxLitU 3481250000 1 ((leaves.drop 124).take 76) 29075000000 4 = true :=
    take_step (n := 2) (t := 76) (b := 126) rfl rfl ArealUCore.ArealUK.chunk_0062 s63
  have s61 : leavesOK ctxLitU 13893750000 3 ((leaves.drop 122).take 78) 29075000000 4 = true :=
    take_step (n := 2) (t := 78) (b := 124) rfl rfl ArealUCore.ArealUK.chunk_0061 s62
  have s60 : leavesOK ctxLitU 6937500000 2 ((leaves.drop 120).take 80) 29075000000 4 = true :=
    take_step (n := 2) (t := 80) (b := 122) rfl rfl ArealUCore.ArealUK.chunk_0060 s61
  have s59 : leavesOK ctxLitU 13862500000 3 ((leaves.drop 118).take 82) 29075000000 4 = true :=
    take_step (n := 2) (t := 82) (b := 120) rfl rfl ArealUCore.ArealUK.chunk_0059 s60
  have s58 : leavesOK ctxLitU 13850000000 3 ((leaves.drop 116).take 84) 29075000000 4 = true :=
    take_step (n := 2) (t := 84) (b := 118) rfl rfl ArealUCore.ArealUK.chunk_0058 s59
  have s57 : leavesOK ctxLitU 27681250000 4 ((leaves.drop 114).take 86) 29075000000 4 = true :=
    take_step (n := 2) (t := 86) (b := 116) rfl rfl ArealUCore.ArealUK.chunk_0057 s58
  have s56 : leavesOK ctxLitU 27668750000 4 ((leaves.drop 112).take 88) 29075000000 4 = true :=
    take_step (n := 2) (t := 88) (b := 114) rfl rfl ArealUCore.ArealUK.chunk_0056 s57
  have s55 : leavesOK ctxLitU 13825000000 3 ((leaves.drop 110).take 90) 29075000000 4 = true :=
    take_step (n := 2) (t := 90) (b := 112) rfl rfl ArealUCore.ArealUK.chunk_0055 s56
  have s54 : leavesOK ctxLitU 6900000000 2 ((leaves.drop 108).take 92) 29075000000 4 = true :=
    take_step (n := 2) (t := 92) (b := 110) rfl rfl ArealUCore.ArealUK.chunk_0054 s55
  have s53 : leavesOK ctxLitU 13775000000 3 ((leaves.drop 106).take 94) 29075000000 4 = true :=
    take_step (n := 2) (t := 94) (b := 108) rfl rfl ArealUCore.ArealUK.chunk_0053 s54
  have s52 : leavesOK ctxLitU 13750000000 3 ((leaves.drop 104).take 96) 29075000000 4 = true :=
    take_step (n := 2) (t := 96) (b := 106) rfl rfl ArealUCore.ArealUK.chunk_0052 s53
  have s51 : leavesOK ctxLitU 27475000000 4 ((leaves.drop 102).take 98) 29075000000 4 = true :=
    take_step (n := 2) (t := 98) (b := 104) rfl rfl ArealUCore.ArealUK.chunk_0051 s52
  have s50 : leavesOK ctxLitU 54925000000 5 ((leaves.drop 100).take 100) 29075000000 4 = true :=
    take_step (n := 2) (t := 100) (b := 102) rfl rfl ArealUCore.ArealUK.chunk_0050 s51
  have s49 : leavesOK ctxLitU 13712500000 3 ((leaves.drop 98).take 102) 29075000000 4 = true :=
    take_step (n := 2) (t := 102) (b := 100) rfl rfl ArealUCore.ArealUK.chunk_0049 s50
  have s48 : leavesOK ctxLitU 13687500000 3 ((leaves.drop 96).take 104) 29075000000 4 = true :=
    take_step (n := 2) (t := 104) (b := 98) rfl rfl ArealUCore.ArealUK.chunk_0048 s49
  have s47 : leavesOK ctxLitU 6825000000 2 ((leaves.drop 94).take 106) 29075000000 4 = true :=
    take_step (n := 2) (t := 106) (b := 96) rfl rfl ArealUCore.ArealUK.chunk_0047 s48
  have s46 : leavesOK ctxLitU 6800000000 2 ((leaves.drop 92).take 108) 29075000000 4 = true :=
    take_step (n := 2) (t := 108) (b := 94) rfl rfl ArealUCore.ArealUK.chunk_0046 s47
  have s45 : leavesOK ctxLitU 6954071428951 12 ((leaves.drop 90).take 110) 29075000000 4 = true :=
    take_step (n := 2) (t := 110) (b := 92) rfl rfl ArealUCore.ArealUK.chunk_0045 s46
  have s44 : leavesOK ctxLitU 55352757144755 15 ((leaves.drop 88).take 112) 29075000000 4 = true :=
    take_step (n := 2) (t := 112) (b := 90) rfl rfl ArealUCore.ArealUK.chunk_0044 s45
  have s43 : leavesOK ctxLitU 110425700002657 16 ((leaves.drop 86).take 114) 29075000000 4 = true :=
    take_step (n := 2) (t := 114) (b := 88) rfl rfl ArealUCore.ArealUK.chunk_0043 s44
  have s42 : leavesOK ctxLitU 220571585718461 17 ((leaves.drop 84).take 116) 29075000000 4 = true :=
    take_step (n := 2) (t := 116) (b := 86) rfl rfl ArealUCore.ArealUK.chunk_0042 s43
  have s41 : leavesOK ctxLitU 220385042860559 17 ((leaves.drop 82).take 118) 29075000000 4 = true :=
    take_step (n := 2) (t := 118) (b := 84) rfl rfl ArealUCore.ArealUK.chunk_0041 s42
  have s40 : leavesOK ctxLitU 110052614286853 16 ((leaves.drop 80).take 120) 29075000000 4 = true :=
    take_step (n := 2) (t := 120) (b := 82) rfl rfl ArealUCore.ArealUK.chunk_0040 s41
  have s39 : leavesOK ctxLitU 54886400000000 15 ((leaves.drop 78).take 122) 29075000000 4 = true :=
    take_step (n := 2) (t := 122) (b := 80) rfl rfl ArealUCore.ArealUK.chunk_0039 s40
  have s38 : leavesOK ctxLitU 13350000000 3 ((leaves.drop 76).take 124) 29075000000 4 = true :=
    take_step (n := 2) (t := 124) (b := 78) rfl rfl ArealUCore.ArealUK.chunk_0038 s39
  have s37 : leavesOK ctxLitU 13300000000 3 ((leaves.drop 74).take 126) 29075000000 4 = true :=
    take_step (n := 2) (t := 126) (b := 76) rfl rfl ArealUCore.ArealUK.chunk_0037 s38
  have s36 : leavesOK ctxLitU 13250000000 3 ((leaves.drop 72).take 128) 29075000000 4 = true :=
    take_step (n := 2) (t := 128) (b := 74) rfl rfl ArealUCore.ArealUK.chunk_0036 s37
  have s35 : leavesOK ctxLitU 26450000000 4 ((leaves.drop 70).take 130) 29075000000 4 = true :=
    take_step (n := 2) (t := 130) (b := 72) rfl rfl ArealUCore.ArealUK.chunk_0035 s36
  have s34 : leavesOK ctxLitU 26400000000 4 ((leaves.drop 68).take 132) 29075000000 4 = true :=
    take_step (n := 2) (t := 132) (b := 70) rfl rfl ArealUCore.ArealUK.chunk_0034 s35
  have s33 : leavesOK ctxLitU 26350000000 4 ((leaves.drop 66).take 134) 29075000000 4 = true :=
    take_step (n := 2) (t := 134) (b := 68) rfl rfl ArealUCore.ArealUK.chunk_0033 s34
  have s32 : leavesOK ctxLitU 52625000000 5 ((leaves.drop 64).take 136) 29075000000 4 = true :=
    take_step (n := 2) (t := 136) (b := 66) rfl rfl ArealUCore.ArealUK.chunk_0032 s33
  have s31 : leavesOK ctxLitU 52575000000 5 ((leaves.drop 62).take 138) 29075000000 4 = true :=
    take_step (n := 2) (t := 138) (b := 64) rfl rfl ArealUCore.ArealUK.chunk_0031 s32
  have s30 : leavesOK ctxLitU 52525000000 5 ((leaves.drop 60).take 140) 29075000000 4 = true :=
    take_step (n := 2) (t := 140) (b := 62) rfl rfl ArealUCore.ArealUK.chunk_0030 s31
  have s29 : leavesOK ctxLitU 52475000000 5 ((leaves.drop 58).take 142) 29075000000 4 = true :=
    take_step (n := 2) (t := 142) (b := 60) rfl rfl ArealUCore.ArealUK.chunk_0029 s30
  have s28 : leavesOK ctxLitU 26200000000 4 ((leaves.drop 56).take 144) 29075000000 4 = true :=
    take_step (n := 2) (t := 144) (b := 58) rfl rfl ArealUCore.ArealUK.chunk_0028 s29
  have s27 : leavesOK ctxLitU 26150000000 4 ((leaves.drop 54).take 146) 29075000000 4 = true :=
    take_step (n := 2) (t := 146) (b := 56) rfl rfl ArealUCore.ArealUK.chunk_0027 s28
  have s26 : leavesOK ctxLitU 26100000000 4 ((leaves.drop 52).take 148) 29075000000 4 = true :=
    take_step (n := 2) (t := 148) (b := 54) rfl rfl ArealUCore.ArealUK.chunk_0026 s27
  have s25 : leavesOK ctxLitU 13000000000 3 ((leaves.drop 50).take 150) 29075000000 4 = true :=
    take_step (n := 2) (t := 150) (b := 52) rfl rfl ArealUCore.ArealUK.chunk_0025 s26
  have s24 : leavesOK ctxLitU 12962500000 3 ((leaves.drop 48).take 152) 29075000000 4 = true :=
    take_step (n := 2) (t := 152) (b := 50) rfl rfl ArealUCore.ArealUK.chunk_0024 s25
  have s23 : leavesOK ctxLitU 12937500000 3 ((leaves.drop 46).take 154) 29075000000 4 = true :=
    take_step (n := 2) (t := 154) (b := 48) rfl rfl ArealUCore.ArealUK.chunk_0023 s24
  have s22 : leavesOK ctxLitU 12912500000 3 ((leaves.drop 44).take 156) 29075000000 4 = true :=
    take_step (n := 2) (t := 156) (b := 46) rfl rfl ArealUCore.ArealUK.chunk_0022 s23
  have s21 : leavesOK ctxLitU 25787500000 4 ((leaves.drop 42).take 158) 29075000000 4 = true :=
    take_step (n := 2) (t := 158) (b := 44) rfl rfl ArealUCore.ArealUK.chunk_0021 s22
  have s20 : leavesOK ctxLitU 25762500000 4 ((leaves.drop 40).take 160) 29075000000 4 = true :=
    take_step (n := 2) (t := 160) (b := 42) rfl rfl ArealUCore.ArealUK.chunk_0020 s21
  have s19 : leavesOK ctxLitU 25737500000 4 ((leaves.drop 38).take 162) 29075000000 4 = true :=
    take_step (n := 2) (t := 162) (b := 40) rfl rfl ArealUCore.ArealUK.chunk_0019 s20
  have s18 : leavesOK ctxLitU 12850000000 3 ((leaves.drop 36).take 164) 29075000000 4 = true :=
    take_step (n := 2) (t := 164) (b := 38) rfl rfl ArealUCore.ArealUK.chunk_0018 s19
  have s17 : leavesOK ctxLitU 12825000000 3 ((leaves.drop 34).take 166) 29075000000 4 = true :=
    take_step (n := 2) (t := 166) (b := 36) rfl rfl ArealUCore.ArealUK.chunk_0017 s18
  have s16 : leavesOK ctxLitU 6393750000 2 ((leaves.drop 32).take 168) 29075000000 4 = true :=
    take_step (n := 2) (t := 168) (b := 34) rfl rfl ArealUCore.ArealUK.chunk_0016 s17
  have s15 : leavesOK ctxLitU 12768750000 3 ((leaves.drop 30).take 170) 29075000000 4 = true :=
    take_step (n := 2) (t := 170) (b := 32) rfl rfl ArealUCore.ArealUK.chunk_0015 s16
  have s14 : leavesOK ctxLitU 12756250000 3 ((leaves.drop 28).take 172) 29075000000 4 = true :=
    take_step (n := 2) (t := 172) (b := 30) rfl rfl ArealUCore.ArealUK.chunk_0014 s15
  have s13 : leavesOK ctxLitU 12743750000 3 ((leaves.drop 26).take 174) 29075000000 4 = true :=
    take_step (n := 2) (t := 174) (b := 28) rfl rfl ArealUCore.ArealUK.chunk_0013 s14
  have s12 : leavesOK ctxLitU 25475000000 4 ((leaves.drop 24).take 176) 29075000000 4 = true :=
    take_step (n := 2) (t := 176) (b := 26) rfl rfl ArealUCore.ArealUK.chunk_0012 s13
  have s11 : leavesOK ctxLitU 12725000000 3 ((leaves.drop 22).take 178) 29075000000 4 = true :=
    take_step (n := 2) (t := 178) (b := 24) rfl rfl ArealUCore.ArealUK.chunk_0011 s12
  have s10 : leavesOK ctxLitU 12706250000 3 ((leaves.drop 20).take 180) 29075000000 4 = true :=
    take_step (n := 2) (t := 180) (b := 22) rfl rfl ArealUCore.ArealUK.chunk_0010 s11
  have s9 : leavesOK ctxLitU 6343750000 2 ((leaves.drop 18).take 182) 29075000000 4 = true :=
    take_step (n := 2) (t := 182) (b := 20) rfl rfl ArealUCore.ArealUK.chunk_0009 s10
  have s8 : leavesOK ctxLitU 3162500000 1 ((leaves.drop 16).take 184) 29075000000 4 = true :=
    take_step (n := 2) (t := 184) (b := 18) rfl rfl ArealUCore.ArealUK.chunk_0008 s9
  have s7 : leavesOK ctxLitU 1568750000 0 ((leaves.drop 14).take 186) 29075000000 4 = true :=
    take_step (n := 2) (t := 186) (b := 16) rfl rfl ArealUCore.ArealUK.chunk_0007 s8
  have s6 : leavesOK ctxLitU 1556250000 0 ((leaves.drop 12).take 188) 29075000000 4 = true :=
    take_step (n := 2) (t := 188) (b := 14) rfl rfl ArealUCore.ArealUK.chunk_0006 s7
  have s5 : leavesOK ctxLitU 1543750000 0 ((leaves.drop 10).take 190) 29075000000 4 = true :=
    take_step (n := 2) (t := 190) (b := 12) rfl rfl ArealUCore.ArealUK.chunk_0005 s6
  have s4 : leavesOK ctxLitU 1531250000 0 ((leaves.drop 8).take 192) 29075000000 4 = true :=
    take_step (n := 2) (t := 192) (b := 10) rfl rfl ArealUCore.ArealUK.chunk_0004 s5
  have s3 : leavesOK ctxLitU 1518750000 0 ((leaves.drop 6).take 194) 29075000000 4 = true :=
    take_step (n := 2) (t := 194) (b := 8) rfl rfl ArealUCore.ArealUK.chunk_0003 s4
  have s2 : leavesOK ctxLitU 1506250000 0 ((leaves.drop 4).take 196) 29075000000 4 = true :=
    take_step (n := 2) (t := 196) (b := 6) rfl rfl ArealUCore.ArealUK.chunk_0002 s3
  have s1 : leavesOK ctxLitU 1493750000 0 ((leaves.drop 2).take 198) 29075000000 4 = true :=
    take_step (n := 2) (t := 198) (b := 4) rfl rfl ArealUCore.ArealUK.chunk_0001 s2
  have s0 : leavesOK ctxLitU 1481250000 0 ((leaves.drop 0).take 200) 29075000000 4 = true :=
    take_step (n := 2) (t := 200) (b := 2) rfl rfl ArealUCore.ArealUK.chunk_0000 s1
  exact s0

end Areal.UCert

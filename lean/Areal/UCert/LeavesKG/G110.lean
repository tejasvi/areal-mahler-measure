import ArealUK.Chunk11000
import ArealUK.Chunk11001
import ArealUK.Chunk11002
import ArealUK.Chunk11003
import ArealUK.Chunk11004
import ArealUK.Chunk11005
import ArealUK.Chunk11006
import ArealUK.Chunk11007
import ArealUK.Chunk11008
import ArealUK.Chunk11009
import ArealUK.Chunk11010
import ArealUK.Chunk11011
import ArealUK.Chunk11012
import ArealUK.Chunk11013
import ArealUK.Chunk11014
import ArealUK.Chunk11015
import ArealUK.Chunk11016
import ArealUK.Chunk11017
import ArealUK.Chunk11018
import ArealUK.Chunk11019
import ArealUK.Chunk11020
import ArealUK.Chunk11021
import ArealUK.Chunk11022
import ArealUK.Chunk11023
import ArealUK.Chunk11024
import ArealUK.Chunk11025
import ArealUK.Chunk11026
import ArealUK.Chunk11027
import ArealUK.Chunk11028
import ArealUK.Chunk11029
import ArealUK.Chunk11030
import ArealUK.Chunk11031
import ArealUK.Chunk11032
import ArealUK.Chunk11033
import ArealUK.Chunk11034
import ArealUK.Chunk11035
import ArealUK.Chunk11036
import ArealUK.Chunk11037
import ArealUK.Chunk11038
import ArealUK.Chunk11039
import ArealUK.Chunk11040
import ArealUK.Chunk11041
import ArealUK.Chunk11042
import ArealUK.Chunk11043
import ArealUK.Chunk11044
import ArealUK.Chunk11045
import ArealUK.Chunk11046
import ArealUK.Chunk11047
import ArealUK.Chunk11048
import ArealUK.Chunk11049
import ArealUK.Chunk11050
import ArealUK.Chunk11051
import ArealUK.Chunk11052
import ArealUK.Chunk11053
import ArealUK.Chunk11054
import ArealUK.Chunk11055
import ArealUK.Chunk11056
import ArealUK.Chunk11057
import ArealUK.Chunk11058
import ArealUK.Chunk11059
import ArealUK.Chunk11060
import ArealUK.Chunk11061
import ArealUK.Chunk11062
import ArealUK.Chunk11063
import ArealUK.Chunk11064
import ArealUK.Chunk11065
import ArealUK.Chunk11066
import ArealUK.Chunk11067
import ArealUK.Chunk11068
import ArealUK.Chunk11069
import ArealUK.Chunk11070
import ArealUK.Chunk11071
import ArealUK.Chunk11072
import ArealUK.Chunk11073
import ArealUK.Chunk11074
import ArealUK.Chunk11075
import ArealUK.Chunk11076
import ArealUK.Chunk11077
import ArealUK.Chunk11078
import ArealUK.Chunk11079
import ArealUK.Chunk11080
import ArealUK.Chunk11081
import ArealUK.Chunk11082
import ArealUK.Chunk11083
import ArealUK.Chunk11084
import ArealUK.Chunk11085
import ArealUK.Chunk11086
import ArealUK.Chunk11087
import ArealUK.Chunk11088
import ArealUK.Chunk11089
import ArealUK.Chunk11090
import ArealUK.Chunk11091
import ArealUK.Chunk11092
import ArealUK.Chunk11093
import ArealUK.Chunk11094
import ArealUK.Chunk11095
import ArealUK.Chunk11096
import ArealUK.Chunk11097
import ArealUK.Chunk11098
import ArealUK.Chunk11099
import Areal.UCert.LeavesKGen

/-! Group 110 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_110 : leavesOK ctxLitU 204281250000 1 ((leaves.drop 22000).take 200) 412900000000 2 = true := by
  have s99 := ArealUCore.ArealUK.chunk_11099
  have s98 : leavesOK ctxLitU 412800000000 2 ((leaves.drop 22196).take 4) 412900000000 2 = true :=
    take_step (n := 2) (t := 4) (b := 22198) rfl rfl ArealUCore.ArealUK.chunk_11098 s99
  have s97 : leavesOK ctxLitU 412750000000 2 ((leaves.drop 22194).take 6) 412900000000 2 = true :=
    take_step (n := 2) (t := 6) (b := 22196) rfl rfl ArealUCore.ArealUK.chunk_11097 s98
  have s96 : leavesOK ctxLitU 412700000000 2 ((leaves.drop 22192).take 8) 412900000000 2 = true :=
    take_step (n := 2) (t := 8) (b := 22194) rfl rfl ArealUCore.ArealUK.chunk_11096 s97
  have s95 : leavesOK ctxLitU 412650000000 2 ((leaves.drop 22190).take 10) 412900000000 2 = true :=
    take_step (n := 2) (t := 10) (b := 22192) rfl rfl ArealUCore.ArealUK.chunk_11095 s96
  have s94 : leavesOK ctxLitU 412600000000 2 ((leaves.drop 22188).take 12) 412900000000 2 = true :=
    take_step (n := 2) (t := 12) (b := 22190) rfl rfl ArealUCore.ArealUK.chunk_11094 s95
  have s93 : leavesOK ctxLitU 412550000000 2 ((leaves.drop 22186).take 14) 412900000000 2 = true :=
    take_step (n := 2) (t := 14) (b := 22188) rfl rfl ArealUCore.ArealUK.chunk_11093 s94
  have s92 : leavesOK ctxLitU 412500000000 2 ((leaves.drop 22184).take 16) 412900000000 2 = true :=
    take_step (n := 2) (t := 16) (b := 22186) rfl rfl ArealUCore.ArealUK.chunk_11092 s93
  have s91 : leavesOK ctxLitU 412450000000 2 ((leaves.drop 22182).take 18) 412900000000 2 = true :=
    take_step (n := 2) (t := 18) (b := 22184) rfl rfl ArealUCore.ArealUK.chunk_11091 s92
  have s90 : leavesOK ctxLitU 412400000000 2 ((leaves.drop 22180).take 20) 412900000000 2 = true :=
    take_step (n := 2) (t := 20) (b := 22182) rfl rfl ArealUCore.ArealUK.chunk_11090 s91
  have s89 : leavesOK ctxLitU 412350000000 2 ((leaves.drop 22178).take 22) 412900000000 2 = true :=
    take_step (n := 2) (t := 22) (b := 22180) rfl rfl ArealUCore.ArealUK.chunk_11089 s90
  have s88 : leavesOK ctxLitU 412300000000 2 ((leaves.drop 22176).take 24) 412900000000 2 = true :=
    take_step (n := 2) (t := 24) (b := 22178) rfl rfl ArealUCore.ArealUK.chunk_11088 s89
  have s87 : leavesOK ctxLitU 412250000000 2 ((leaves.drop 22174).take 26) 412900000000 2 = true :=
    take_step (n := 2) (t := 26) (b := 22176) rfl rfl ArealUCore.ArealUK.chunk_11087 s88
  have s86 : leavesOK ctxLitU 412200000000 2 ((leaves.drop 22172).take 28) 412900000000 2 = true :=
    take_step (n := 2) (t := 28) (b := 22174) rfl rfl ArealUCore.ArealUK.chunk_11086 s87
  have s85 : leavesOK ctxLitU 412150000000 2 ((leaves.drop 22170).take 30) 412900000000 2 = true :=
    take_step (n := 2) (t := 30) (b := 22172) rfl rfl ArealUCore.ArealUK.chunk_11085 s86
  have s84 : leavesOK ctxLitU 412100000000 2 ((leaves.drop 22168).take 32) 412900000000 2 = true :=
    take_step (n := 2) (t := 32) (b := 22170) rfl rfl ArealUCore.ArealUK.chunk_11084 s85
  have s83 : leavesOK ctxLitU 412050000000 2 ((leaves.drop 22166).take 34) 412900000000 2 = true :=
    take_step (n := 2) (t := 34) (b := 22168) rfl rfl ArealUCore.ArealUK.chunk_11083 s84
  have s82 : leavesOK ctxLitU 412000000000 2 ((leaves.drop 22164).take 36) 412900000000 2 = true :=
    take_step (n := 2) (t := 36) (b := 22166) rfl rfl ArealUCore.ArealUK.chunk_11082 s83
  have s81 : leavesOK ctxLitU 411950000000 2 ((leaves.drop 22162).take 38) 412900000000 2 = true :=
    take_step (n := 2) (t := 38) (b := 22164) rfl rfl ArealUCore.ArealUK.chunk_11081 s82
  have s80 : leavesOK ctxLitU 411900000000 2 ((leaves.drop 22160).take 40) 412900000000 2 = true :=
    take_step (n := 2) (t := 40) (b := 22162) rfl rfl ArealUCore.ArealUK.chunk_11080 s81
  have s79 : leavesOK ctxLitU 411850000000 2 ((leaves.drop 22158).take 42) 412900000000 2 = true :=
    take_step (n := 2) (t := 42) (b := 22160) rfl rfl ArealUCore.ArealUK.chunk_11079 s80
  have s78 : leavesOK ctxLitU 411800000000 2 ((leaves.drop 22156).take 44) 412900000000 2 = true :=
    take_step (n := 2) (t := 44) (b := 22158) rfl rfl ArealUCore.ArealUK.chunk_11078 s79
  have s77 : leavesOK ctxLitU 411750000000 2 ((leaves.drop 22154).take 46) 412900000000 2 = true :=
    take_step (n := 2) (t := 46) (b := 22156) rfl rfl ArealUCore.ArealUK.chunk_11077 s78
  have s76 : leavesOK ctxLitU 411700000000 2 ((leaves.drop 22152).take 48) 412900000000 2 = true :=
    take_step (n := 2) (t := 48) (b := 22154) rfl rfl ArealUCore.ArealUK.chunk_11076 s77
  have s75 : leavesOK ctxLitU 411650000000 2 ((leaves.drop 22150).take 50) 412900000000 2 = true :=
    take_step (n := 2) (t := 50) (b := 22152) rfl rfl ArealUCore.ArealUK.chunk_11075 s76
  have s74 : leavesOK ctxLitU 411600000000 2 ((leaves.drop 22148).take 52) 412900000000 2 = true :=
    take_step (n := 2) (t := 52) (b := 22150) rfl rfl ArealUCore.ArealUK.chunk_11074 s75
  have s73 : leavesOK ctxLitU 411550000000 2 ((leaves.drop 22146).take 54) 412900000000 2 = true :=
    take_step (n := 2) (t := 54) (b := 22148) rfl rfl ArealUCore.ArealUK.chunk_11073 s74
  have s72 : leavesOK ctxLitU 411500000000 2 ((leaves.drop 22144).take 56) 412900000000 2 = true :=
    take_step (n := 2) (t := 56) (b := 22146) rfl rfl ArealUCore.ArealUK.chunk_11072 s73
  have s71 : leavesOK ctxLitU 411450000000 2 ((leaves.drop 22142).take 58) 412900000000 2 = true :=
    take_step (n := 2) (t := 58) (b := 22144) rfl rfl ArealUCore.ArealUK.chunk_11071 s72
  have s70 : leavesOK ctxLitU 411400000000 2 ((leaves.drop 22140).take 60) 412900000000 2 = true :=
    take_step (n := 2) (t := 60) (b := 22142) rfl rfl ArealUCore.ArealUK.chunk_11070 s71
  have s69 : leavesOK ctxLitU 411350000000 2 ((leaves.drop 22138).take 62) 412900000000 2 = true :=
    take_step (n := 2) (t := 62) (b := 22140) rfl rfl ArealUCore.ArealUK.chunk_11069 s70
  have s68 : leavesOK ctxLitU 411300000000 2 ((leaves.drop 22136).take 64) 412900000000 2 = true :=
    take_step (n := 2) (t := 64) (b := 22138) rfl rfl ArealUCore.ArealUK.chunk_11068 s69
  have s67 : leavesOK ctxLitU 411250000000 2 ((leaves.drop 22134).take 66) 412900000000 2 = true :=
    take_step (n := 2) (t := 66) (b := 22136) rfl rfl ArealUCore.ArealUK.chunk_11067 s68
  have s66 : leavesOK ctxLitU 411200000000 2 ((leaves.drop 22132).take 68) 412900000000 2 = true :=
    take_step (n := 2) (t := 68) (b := 22134) rfl rfl ArealUCore.ArealUK.chunk_11066 s67
  have s65 : leavesOK ctxLitU 411150000000 2 ((leaves.drop 22130).take 70) 412900000000 2 = true :=
    take_step (n := 2) (t := 70) (b := 22132) rfl rfl ArealUCore.ArealUK.chunk_11065 s66
  have s64 : leavesOK ctxLitU 411100000000 2 ((leaves.drop 22128).take 72) 412900000000 2 = true :=
    take_step (n := 2) (t := 72) (b := 22130) rfl rfl ArealUCore.ArealUK.chunk_11064 s65
  have s63 : leavesOK ctxLitU 411050000000 2 ((leaves.drop 22126).take 74) 412900000000 2 = true :=
    take_step (n := 2) (t := 74) (b := 22128) rfl rfl ArealUCore.ArealUK.chunk_11063 s64
  have s62 : leavesOK ctxLitU 411000000000 2 ((leaves.drop 22124).take 76) 412900000000 2 = true :=
    take_step (n := 2) (t := 76) (b := 22126) rfl rfl ArealUCore.ArealUK.chunk_11062 s63
  have s61 : leavesOK ctxLitU 410950000000 2 ((leaves.drop 22122).take 78) 412900000000 2 = true :=
    take_step (n := 2) (t := 78) (b := 22124) rfl rfl ArealUCore.ArealUK.chunk_11061 s62
  have s60 : leavesOK ctxLitU 410900000000 2 ((leaves.drop 22120).take 80) 412900000000 2 = true :=
    take_step (n := 2) (t := 80) (b := 22122) rfl rfl ArealUCore.ArealUK.chunk_11060 s61
  have s59 : leavesOK ctxLitU 410850000000 2 ((leaves.drop 22118).take 82) 412900000000 2 = true :=
    take_step (n := 2) (t := 82) (b := 22120) rfl rfl ArealUCore.ArealUK.chunk_11059 s60
  have s58 : leavesOK ctxLitU 410800000000 2 ((leaves.drop 22116).take 84) 412900000000 2 = true :=
    take_step (n := 2) (t := 84) (b := 22118) rfl rfl ArealUCore.ArealUK.chunk_11058 s59
  have s57 : leavesOK ctxLitU 410750000000 2 ((leaves.drop 22114).take 86) 412900000000 2 = true :=
    take_step (n := 2) (t := 86) (b := 22116) rfl rfl ArealUCore.ArealUK.chunk_11057 s58
  have s56 : leavesOK ctxLitU 410700000000 2 ((leaves.drop 22112).take 88) 412900000000 2 = true :=
    take_step (n := 2) (t := 88) (b := 22114) rfl rfl ArealUCore.ArealUK.chunk_11056 s57
  have s55 : leavesOK ctxLitU 410650000000 2 ((leaves.drop 22110).take 90) 412900000000 2 = true :=
    take_step (n := 2) (t := 90) (b := 22112) rfl rfl ArealUCore.ArealUK.chunk_11055 s56
  have s54 : leavesOK ctxLitU 410600000000 2 ((leaves.drop 22108).take 92) 412900000000 2 = true :=
    take_step (n := 2) (t := 92) (b := 22110) rfl rfl ArealUCore.ArealUK.chunk_11054 s55
  have s53 : leavesOK ctxLitU 410550000000 2 ((leaves.drop 22106).take 94) 412900000000 2 = true :=
    take_step (n := 2) (t := 94) (b := 22108) rfl rfl ArealUCore.ArealUK.chunk_11053 s54
  have s52 : leavesOK ctxLitU 410500000000 2 ((leaves.drop 22104).take 96) 412900000000 2 = true :=
    take_step (n := 2) (t := 96) (b := 22106) rfl rfl ArealUCore.ArealUK.chunk_11052 s53
  have s51 : leavesOK ctxLitU 410450000000 2 ((leaves.drop 22102).take 98) 412900000000 2 = true :=
    take_step (n := 2) (t := 98) (b := 22104) rfl rfl ArealUCore.ArealUK.chunk_11051 s52
  have s50 : leavesOK ctxLitU 410400000000 2 ((leaves.drop 22100).take 100) 412900000000 2 = true :=
    take_step (n := 2) (t := 100) (b := 22102) rfl rfl ArealUCore.ArealUK.chunk_11050 s51
  have s49 : leavesOK ctxLitU 410350000000 2 ((leaves.drop 22098).take 102) 412900000000 2 = true :=
    take_step (n := 2) (t := 102) (b := 22100) rfl rfl ArealUCore.ArealUK.chunk_11049 s50
  have s48 : leavesOK ctxLitU 410300000000 2 ((leaves.drop 22096).take 104) 412900000000 2 = true :=
    take_step (n := 2) (t := 104) (b := 22098) rfl rfl ArealUCore.ArealUK.chunk_11048 s49
  have s47 : leavesOK ctxLitU 410250000000 2 ((leaves.drop 22094).take 106) 412900000000 2 = true :=
    take_step (n := 2) (t := 106) (b := 22096) rfl rfl ArealUCore.ArealUK.chunk_11047 s48
  have s46 : leavesOK ctxLitU 410200000000 2 ((leaves.drop 22092).take 108) 412900000000 2 = true :=
    take_step (n := 2) (t := 108) (b := 22094) rfl rfl ArealUCore.ArealUK.chunk_11046 s47
  have s45 : leavesOK ctxLitU 410150000000 2 ((leaves.drop 22090).take 110) 412900000000 2 = true :=
    take_step (n := 2) (t := 110) (b := 22092) rfl rfl ArealUCore.ArealUK.chunk_11045 s46
  have s44 : leavesOK ctxLitU 410100000000 2 ((leaves.drop 22088).take 112) 412900000000 2 = true :=
    take_step (n := 2) (t := 112) (b := 22090) rfl rfl ArealUCore.ArealUK.chunk_11044 s45
  have s43 : leavesOK ctxLitU 410050000000 2 ((leaves.drop 22086).take 114) 412900000000 2 = true :=
    take_step (n := 2) (t := 114) (b := 22088) rfl rfl ArealUCore.ArealUK.chunk_11043 s44
  have s42 : leavesOK ctxLitU 410000000000 2 ((leaves.drop 22084).take 116) 412900000000 2 = true :=
    take_step (n := 2) (t := 116) (b := 22086) rfl rfl ArealUCore.ArealUK.chunk_11042 s43
  have s41 : leavesOK ctxLitU 409950000000 2 ((leaves.drop 22082).take 118) 412900000000 2 = true :=
    take_step (n := 2) (t := 118) (b := 22084) rfl rfl ArealUCore.ArealUK.chunk_11041 s42
  have s40 : leavesOK ctxLitU 409900000000 2 ((leaves.drop 22080).take 120) 412900000000 2 = true :=
    take_step (n := 2) (t := 120) (b := 22082) rfl rfl ArealUCore.ArealUK.chunk_11040 s41
  have s39 : leavesOK ctxLitU 409850000000 2 ((leaves.drop 22078).take 122) 412900000000 2 = true :=
    take_step (n := 2) (t := 122) (b := 22080) rfl rfl ArealUCore.ArealUK.chunk_11039 s40
  have s38 : leavesOK ctxLitU 409800000000 2 ((leaves.drop 22076).take 124) 412900000000 2 = true :=
    take_step (n := 2) (t := 124) (b := 22078) rfl rfl ArealUCore.ArealUK.chunk_11038 s39
  have s37 : leavesOK ctxLitU 409750000000 2 ((leaves.drop 22074).take 126) 412900000000 2 = true :=
    take_step (n := 2) (t := 126) (b := 22076) rfl rfl ArealUCore.ArealUK.chunk_11037 s38
  have s36 : leavesOK ctxLitU 409700000000 2 ((leaves.drop 22072).take 128) 412900000000 2 = true :=
    take_step (n := 2) (t := 128) (b := 22074) rfl rfl ArealUCore.ArealUK.chunk_11036 s37
  have s35 : leavesOK ctxLitU 409650000000 2 ((leaves.drop 22070).take 130) 412900000000 2 = true :=
    take_step (n := 2) (t := 130) (b := 22072) rfl rfl ArealUCore.ArealUK.chunk_11035 s36
  have s34 : leavesOK ctxLitU 409600000000 2 ((leaves.drop 22068).take 132) 412900000000 2 = true :=
    take_step (n := 2) (t := 132) (b := 22070) rfl rfl ArealUCore.ArealUK.chunk_11034 s35
  have s33 : leavesOK ctxLitU 409550000000 2 ((leaves.drop 22066).take 134) 412900000000 2 = true :=
    take_step (n := 2) (t := 134) (b := 22068) rfl rfl ArealUCore.ArealUK.chunk_11033 s34
  have s32 : leavesOK ctxLitU 819025000000 3 ((leaves.drop 22064).take 136) 412900000000 2 = true :=
    take_step (n := 2) (t := 136) (b := 22066) rfl rfl ArealUCore.ArealUK.chunk_11032 s33
  have s31 : leavesOK ctxLitU 409475000000 2 ((leaves.drop 22062).take 138) 412900000000 2 = true :=
    take_step (n := 2) (t := 138) (b := 22064) rfl rfl ArealUCore.ArealUK.chunk_11031 s32
  have s30 : leavesOK ctxLitU 409425000000 2 ((leaves.drop 22060).take 140) 412900000000 2 = true :=
    take_step (n := 2) (t := 140) (b := 22062) rfl rfl ArealUCore.ArealUK.chunk_11030 s31
  have s29 : leavesOK ctxLitU 409375000000 2 ((leaves.drop 22058).take 142) 412900000000 2 = true :=
    take_step (n := 2) (t := 142) (b := 22060) rfl rfl ArealUCore.ArealUK.chunk_11029 s30
  have s28 : leavesOK ctxLitU 409325000000 2 ((leaves.drop 22056).take 144) 412900000000 2 = true :=
    take_step (n := 2) (t := 144) (b := 22058) rfl rfl ArealUCore.ArealUK.chunk_11028 s29
  have s27 : leavesOK ctxLitU 818575000000 3 ((leaves.drop 22054).take 146) 412900000000 2 = true :=
    take_step (n := 2) (t := 146) (b := 22056) rfl rfl ArealUCore.ArealUK.chunk_11027 s28
  have s26 : leavesOK ctxLitU 818525000000 3 ((leaves.drop 22052).take 148) 412900000000 2 = true :=
    take_step (n := 2) (t := 148) (b := 22054) rfl rfl ArealUCore.ArealUK.chunk_11026 s27
  have s25 : leavesOK ctxLitU 818475000000 3 ((leaves.drop 22050).take 150) 412900000000 2 = true :=
    take_step (n := 2) (t := 150) (b := 22052) rfl rfl ArealUCore.ArealUK.chunk_11025 s26
  have s24 : leavesOK ctxLitU 818425000000 3 ((leaves.drop 22048).take 152) 412900000000 2 = true :=
    take_step (n := 2) (t := 152) (b := 22050) rfl rfl ArealUCore.ArealUK.chunk_11024 s25
  have s23 : leavesOK ctxLitU 818375000000 3 ((leaves.drop 22046).take 154) 412900000000 2 = true :=
    take_step (n := 2) (t := 154) (b := 22048) rfl rfl ArealUCore.ArealUK.chunk_11023 s24
  have s22 : leavesOK ctxLitU 818325000000 3 ((leaves.drop 22044).take 156) 412900000000 2 = true :=
    take_step (n := 2) (t := 156) (b := 22046) rfl rfl ArealUCore.ArealUK.chunk_11022 s23
  have s21 : leavesOK ctxLitU 818275000000 3 ((leaves.drop 22042).take 158) 412900000000 2 = true :=
    take_step (n := 2) (t := 158) (b := 22044) rfl rfl ArealUCore.ArealUK.chunk_11021 s22
  have s20 : leavesOK ctxLitU 818225000000 3 ((leaves.drop 22040).take 160) 412900000000 2 = true :=
    take_step (n := 2) (t := 160) (b := 22042) rfl rfl ArealUCore.ArealUK.chunk_11020 s21
  have s19 : leavesOK ctxLitU 818175000000 3 ((leaves.drop 22038).take 162) 412900000000 2 = true :=
    take_step (n := 2) (t := 162) (b := 22040) rfl rfl ArealUCore.ArealUK.chunk_11019 s20
  have s18 : leavesOK ctxLitU 409050000000 2 ((leaves.drop 22036).take 164) 412900000000 2 = true :=
    take_step (n := 2) (t := 164) (b := 22038) rfl rfl ArealUCore.ArealUK.chunk_11018 s19
  have s17 : leavesOK ctxLitU 409000000000 2 ((leaves.drop 22034).take 166) 412900000000 2 = true :=
    take_step (n := 2) (t := 166) (b := 22036) rfl rfl ArealUCore.ArealUK.chunk_11017 s18
  have s16 : leavesOK ctxLitU 408950000000 2 ((leaves.drop 22032).take 168) 412900000000 2 = true :=
    take_step (n := 2) (t := 168) (b := 22034) rfl rfl ArealUCore.ArealUK.chunk_11016 s17
  have s15 : leavesOK ctxLitU 817850000000 3 ((leaves.drop 22030).take 170) 412900000000 2 = true :=
    take_step (n := 2) (t := 170) (b := 22032) rfl rfl ArealUCore.ArealUK.chunk_11015 s16
  have s14 : leavesOK ctxLitU 817800000000 3 ((leaves.drop 22028).take 172) 412900000000 2 = true :=
    take_step (n := 2) (t := 172) (b := 22030) rfl rfl ArealUCore.ArealUK.chunk_11014 s15
  have s13 : leavesOK ctxLitU 817750000000 3 ((leaves.drop 22026).take 174) 412900000000 2 = true :=
    take_step (n := 2) (t := 174) (b := 22028) rfl rfl ArealUCore.ArealUK.chunk_11013 s14
  have s12 : leavesOK ctxLitU 817700000000 3 ((leaves.drop 22024).take 176) 412900000000 2 = true :=
    take_step (n := 2) (t := 176) (b := 22026) rfl rfl ArealUCore.ArealUK.chunk_11012 s13
  have s11 : leavesOK ctxLitU 817650000000 3 ((leaves.drop 22022).take 178) 412900000000 2 = true :=
    take_step (n := 2) (t := 178) (b := 22024) rfl rfl ArealUCore.ArealUK.chunk_11011 s12
  have s10 : leavesOK ctxLitU 817600000000 3 ((leaves.drop 22020).take 180) 412900000000 2 = true :=
    take_step (n := 2) (t := 180) (b := 22022) rfl rfl ArealUCore.ArealUK.chunk_11010 s11
  have s9 : leavesOK ctxLitU 817550000000 3 ((leaves.drop 22018).take 182) 412900000000 2 = true :=
    take_step (n := 2) (t := 182) (b := 22020) rfl rfl ArealUCore.ArealUK.chunk_11009 s10
  have s8 : leavesOK ctxLitU 817500000000 3 ((leaves.drop 22016).take 184) 412900000000 2 = true :=
    take_step (n := 2) (t := 184) (b := 22018) rfl rfl ArealUCore.ArealUK.chunk_11008 s9
  have s7 : leavesOK ctxLitU 817450000000 3 ((leaves.drop 22014).take 186) 412900000000 2 = true :=
    take_step (n := 2) (t := 186) (b := 22016) rfl rfl ArealUCore.ArealUK.chunk_11007 s8
  have s6 : leavesOK ctxLitU 817400000000 3 ((leaves.drop 22012).take 188) 412900000000 2 = true :=
    take_step (n := 2) (t := 188) (b := 22014) rfl rfl ArealUCore.ArealUK.chunk_11006 s7
  have s5 : leavesOK ctxLitU 408675000000 2 ((leaves.drop 22010).take 190) 412900000000 2 = true :=
    take_step (n := 2) (t := 190) (b := 22012) rfl rfl ArealUCore.ArealUK.chunk_11005 s6
  have s4 : leavesOK ctxLitU 408650000000 2 ((leaves.drop 22008).take 192) 412900000000 2 = true :=
    take_step (n := 2) (t := 192) (b := 22010) rfl rfl ArealUCore.ArealUK.chunk_11004 s5
  have s3 : leavesOK ctxLitU 408625000000 2 ((leaves.drop 22006).take 194) 412900000000 2 = true :=
    take_step (n := 2) (t := 194) (b := 22008) rfl rfl ArealUCore.ArealUK.chunk_11003 s4
  have s2 : leavesOK ctxLitU 408600000000 2 ((leaves.drop 22004).take 196) 412900000000 2 = true :=
    take_step (n := 2) (t := 196) (b := 22006) rfl rfl ArealUCore.ArealUK.chunk_11002 s3
  have s1 : leavesOK ctxLitU 408581250000 2 ((leaves.drop 22002).take 198) 412900000000 2 = true :=
    take_step (n := 2) (t := 198) (b := 22004) rfl rfl ArealUCore.ArealUK.chunk_11001 s2
  have s0 : leavesOK ctxLitU 204281250000 1 ((leaves.drop 22000).take 200) 412900000000 2 = true :=
    take_step (n := 2) (t := 200) (b := 22002) rfl rfl ArealUCore.ArealUK.chunk_11000 s1
  exact s0

end Areal.UCert

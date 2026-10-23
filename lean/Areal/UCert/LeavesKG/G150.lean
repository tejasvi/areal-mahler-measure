import ArealUK.Chunk15000
import ArealUK.Chunk15001
import ArealUK.Chunk15002
import ArealUK.Chunk15003
import ArealUK.Chunk15004
import ArealUK.Chunk15005
import ArealUK.Chunk15006
import ArealUK.Chunk15007
import ArealUK.Chunk15008
import ArealUK.Chunk15009
import ArealUK.Chunk15010
import ArealUK.Chunk15011
import ArealUK.Chunk15012
import ArealUK.Chunk15013
import ArealUK.Chunk15014
import ArealUK.Chunk15015
import ArealUK.Chunk15016
import ArealUK.Chunk15017
import ArealUK.Chunk15018
import ArealUK.Chunk15019
import ArealUK.Chunk15020
import ArealUK.Chunk15021
import ArealUK.Chunk15022
import ArealUK.Chunk15023
import ArealUK.Chunk15024
import ArealUK.Chunk15025
import ArealUK.Chunk15026
import ArealUK.Chunk15027
import ArealUK.Chunk15028
import ArealUK.Chunk15029
import ArealUK.Chunk15030
import ArealUK.Chunk15031
import ArealUK.Chunk15032
import ArealUK.Chunk15033
import ArealUK.Chunk15034
import ArealUK.Chunk15035
import ArealUK.Chunk15036
import ArealUK.Chunk15037
import ArealUK.Chunk15038
import ArealUK.Chunk15039
import ArealUK.Chunk15040
import ArealUK.Chunk15041
import ArealUK.Chunk15042
import ArealUK.Chunk15043
import ArealUK.Chunk15044
import ArealUK.Chunk15045
import ArealUK.Chunk15046
import ArealUK.Chunk15047
import ArealUK.Chunk15048
import ArealUK.Chunk15049
import ArealUK.Chunk15050
import ArealUK.Chunk15051
import ArealUK.Chunk15052
import ArealUK.Chunk15053
import ArealUK.Chunk15054
import ArealUK.Chunk15055
import ArealUK.Chunk15056
import ArealUK.Chunk15057
import ArealUK.Chunk15058
import ArealUK.Chunk15059
import ArealUK.Chunk15060
import ArealUK.Chunk15061
import ArealUK.Chunk15062
import ArealUK.Chunk15063
import ArealUK.Chunk15064
import ArealUK.Chunk15065
import ArealUK.Chunk15066
import ArealUK.Chunk15067
import ArealUK.Chunk15068
import ArealUK.Chunk15069
import ArealUK.Chunk15070
import ArealUK.Chunk15071
import ArealUK.Chunk15072
import ArealUK.Chunk15073
import ArealUK.Chunk15074
import ArealUK.Chunk15075
import ArealUK.Chunk15076
import ArealUK.Chunk15077
import ArealUK.Chunk15078
import ArealUK.Chunk15079
import ArealUK.Chunk15080
import ArealUK.Chunk15081
import ArealUK.Chunk15082
import ArealUK.Chunk15083
import ArealUK.Chunk15084
import ArealUK.Chunk15085
import ArealUK.Chunk15086
import ArealUK.Chunk15087
import ArealUK.Chunk15088
import ArealUK.Chunk15089
import ArealUK.Chunk15090
import ArealUK.Chunk15091
import ArealUK.Chunk15092
import ArealUK.Chunk15093
import ArealUK.Chunk15094
import ArealUK.Chunk15095
import ArealUK.Chunk15096
import ArealUK.Chunk15097
import ArealUK.Chunk15098
import ArealUK.Chunk15099
import Areal.UCert.LeavesKGen

/-! Group 150 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_150 : leavesOK ctxLitU 156425000000 0 ((leaves.drop 30000).take 200) 157818750000 0 = true := by
  have s99 := ArealUCore.ArealUK.chunk_15099
  have s98 : leavesOK ctxLitU 315587500000 1 ((leaves.drop 30196).take 4) 157818750000 0 = true :=
    take_step (n := 2) (t := 4) (b := 30198) rfl rfl ArealUCore.ArealUK.chunk_15098 s99
  have s97 : leavesOK ctxLitU 157775000000 0 ((leaves.drop 30194).take 6) 157818750000 0 = true :=
    take_step (n := 2) (t := 6) (b := 30196) rfl rfl ArealUCore.ArealUK.chunk_15097 s98
  have s96 : leavesOK ctxLitU 157762500000 0 ((leaves.drop 30192).take 8) 157818750000 0 = true :=
    take_step (n := 2) (t := 8) (b := 30194) rfl rfl ArealUCore.ArealUK.chunk_15096 s97
  have s95 : leavesOK ctxLitU 157750000000 0 ((leaves.drop 30190).take 10) 157818750000 0 = true :=
    take_step (n := 2) (t := 10) (b := 30192) rfl rfl ArealUCore.ArealUK.chunk_15095 s96
  have s94 : leavesOK ctxLitU 157737500000 0 ((leaves.drop 30188).take 12) 157818750000 0 = true :=
    take_step (n := 2) (t := 12) (b := 30190) rfl rfl ArealUCore.ArealUK.chunk_15094 s95
  have s93 : leavesOK ctxLitU 157725000000 0 ((leaves.drop 30186).take 14) 157818750000 0 = true :=
    take_step (n := 2) (t := 14) (b := 30188) rfl rfl ArealUCore.ArealUK.chunk_15093 s94
  have s92 : leavesOK ctxLitU 315412500000 1 ((leaves.drop 30184).take 16) 157818750000 0 = true :=
    take_step (n := 2) (t := 16) (b := 30186) rfl rfl ArealUCore.ArealUK.chunk_15092 s93
  have s91 : leavesOK ctxLitU 315387500000 1 ((leaves.drop 30182).take 18) 157818750000 0 = true :=
    take_step (n := 2) (t := 18) (b := 30184) rfl rfl ArealUCore.ArealUK.chunk_15091 s92
  have s90 : leavesOK ctxLitU 157675000000 0 ((leaves.drop 30180).take 20) 157818750000 0 = true :=
    take_step (n := 2) (t := 20) (b := 30182) rfl rfl ArealUCore.ArealUK.chunk_15090 s91
  have s89 : leavesOK ctxLitU 157662500000 0 ((leaves.drop 30178).take 22) 157818750000 0 = true :=
    take_step (n := 2) (t := 22) (b := 30180) rfl rfl ArealUCore.ArealUK.chunk_15089 s90
  have s88 : leavesOK ctxLitU 157650000000 0 ((leaves.drop 30176).take 24) 157818750000 0 = true :=
    take_step (n := 2) (t := 24) (b := 30178) rfl rfl ArealUCore.ArealUK.chunk_15088 s89
  have s87 : leavesOK ctxLitU 157637500000 0 ((leaves.drop 30174).take 26) 157818750000 0 = true :=
    take_step (n := 2) (t := 26) (b := 30176) rfl rfl ArealUCore.ArealUK.chunk_15087 s88
  have s86 : leavesOK ctxLitU 157625000000 0 ((leaves.drop 30172).take 28) 157818750000 0 = true :=
    take_step (n := 2) (t := 28) (b := 30174) rfl rfl ArealUCore.ArealUK.chunk_15086 s87
  have s85 : leavesOK ctxLitU 315212500000 1 ((leaves.drop 30170).take 30) 157818750000 0 = true :=
    take_step (n := 2) (t := 30) (b := 30172) rfl rfl ArealUCore.ArealUK.chunk_15085 s86
  have s84 : leavesOK ctxLitU 157593750000 0 ((leaves.drop 30168).take 32) 157818750000 0 = true :=
    take_step (n := 2) (t := 32) (b := 30170) rfl rfl ArealUCore.ArealUK.chunk_15084 s85
  have s83 : leavesOK ctxLitU 157581250000 0 ((leaves.drop 30166).take 34) 157818750000 0 = true :=
    take_step (n := 2) (t := 34) (b := 30168) rfl rfl ArealUCore.ArealUK.chunk_15083 s84
  have s82 : leavesOK ctxLitU 157568750000 0 ((leaves.drop 30164).take 36) 157818750000 0 = true :=
    take_step (n := 2) (t := 36) (b := 30166) rfl rfl ArealUCore.ArealUK.chunk_15082 s83
  have s81 : leavesOK ctxLitU 157556250000 0 ((leaves.drop 30162).take 38) 157818750000 0 = true :=
    take_step (n := 2) (t := 38) (b := 30164) rfl rfl ArealUCore.ArealUK.chunk_15081 s82
  have s80 : leavesOK ctxLitU 157543750000 0 ((leaves.drop 30160).take 40) 157818750000 0 = true :=
    take_step (n := 2) (t := 40) (b := 30162) rfl rfl ArealUCore.ArealUK.chunk_15080 s81
  have s79 : leavesOK ctxLitU 157531250000 0 ((leaves.drop 30158).take 42) 157818750000 0 = true :=
    take_step (n := 2) (t := 42) (b := 30160) rfl rfl ArealUCore.ArealUK.chunk_15079 s80
  have s78 : leavesOK ctxLitU 315037500000 1 ((leaves.drop 30156).take 44) 157818750000 0 = true :=
    take_step (n := 2) (t := 44) (b := 30158) rfl rfl ArealUCore.ArealUK.chunk_15078 s79
  have s77 : leavesOK ctxLitU 315012500000 1 ((leaves.drop 30154).take 46) 157818750000 0 = true :=
    take_step (n := 2) (t := 46) (b := 30156) rfl rfl ArealUCore.ArealUK.chunk_15077 s78
  have s76 : leavesOK ctxLitU 157487500000 0 ((leaves.drop 30152).take 48) 157818750000 0 = true :=
    take_step (n := 2) (t := 48) (b := 30154) rfl rfl ArealUCore.ArealUK.chunk_15076 s77
  have s75 : leavesOK ctxLitU 157468750000 0 ((leaves.drop 30150).take 50) 157818750000 0 = true :=
    take_step (n := 2) (t := 50) (b := 30152) rfl rfl ArealUCore.ArealUK.chunk_15075 s76
  have s74 : leavesOK ctxLitU 157456250000 0 ((leaves.drop 30148).take 52) 157818750000 0 = true :=
    take_step (n := 2) (t := 52) (b := 30150) rfl rfl ArealUCore.ArealUK.chunk_15074 s75
  have s73 : leavesOK ctxLitU 157443750000 0 ((leaves.drop 30146).take 54) 157818750000 0 = true :=
    take_step (n := 2) (t := 54) (b := 30148) rfl rfl ArealUCore.ArealUK.chunk_15073 s74
  have s72 : leavesOK ctxLitU 157431250000 0 ((leaves.drop 30144).take 56) 157818750000 0 = true :=
    take_step (n := 2) (t := 56) (b := 30146) rfl rfl ArealUCore.ArealUK.chunk_15072 s73
  have s71 : leavesOK ctxLitU 157412500000 0 ((leaves.drop 30142).take 58) 157818750000 0 = true :=
    take_step (n := 2) (t := 58) (b := 30144) rfl rfl ArealUCore.ArealUK.chunk_15071 s72
  have s70 : leavesOK ctxLitU 157387500000 0 ((leaves.drop 30140).take 60) 157818750000 0 = true :=
    take_step (n := 2) (t := 60) (b := 30142) rfl rfl ArealUCore.ArealUK.chunk_15070 s71
  have s69 : leavesOK ctxLitU 314750000000 1 ((leaves.drop 30138).take 62) 157818750000 0 = true :=
    take_step (n := 2) (t := 62) (b := 30140) rfl rfl ArealUCore.ArealUK.chunk_15069 s70
  have s68 : leavesOK ctxLitU 314737500000 1 ((leaves.drop 30136).take 64) 157818750000 0 = true :=
    take_step (n := 2) (t := 64) (b := 30138) rfl rfl ArealUCore.ArealUK.chunk_15068 s69
  have s67 : leavesOK ctxLitU 157356250000 0 ((leaves.drop 30134).take 66) 157818750000 0 = true :=
    take_step (n := 2) (t := 66) (b := 30136) rfl rfl ArealUCore.ArealUK.chunk_15067 s68
  have s66 : leavesOK ctxLitU 157337500000 0 ((leaves.drop 30132).take 68) 157818750000 0 = true :=
    take_step (n := 2) (t := 68) (b := 30134) rfl rfl ArealUCore.ArealUK.chunk_15066 s67
  have s65 : leavesOK ctxLitU 314650000000 1 ((leaves.drop 30130).take 70) 157818750000 0 = true :=
    take_step (n := 2) (t := 70) (b := 30132) rfl rfl ArealUCore.ArealUK.chunk_15065 s66
  have s64 : leavesOK ctxLitU 629225000000 2 ((leaves.drop 30128).take 72) 157818750000 0 = true :=
    take_step (n := 2) (t := 72) (b := 30130) rfl rfl ArealUCore.ArealUK.chunk_15064 s65
  have s63 : leavesOK ctxLitU 629175000000 2 ((leaves.drop 30126).take 74) 157818750000 0 = true :=
    take_step (n := 2) (t := 74) (b := 30128) rfl rfl ArealUCore.ArealUK.chunk_15063 s64
  have s62 : leavesOK ctxLitU 314550000000 1 ((leaves.drop 30124).take 76) 157818750000 0 = true :=
    take_step (n := 2) (t := 76) (b := 30126) rfl rfl ArealUCore.ArealUK.chunk_15062 s63
  have s61 : leavesOK ctxLitU 314525000000 1 ((leaves.drop 30122).take 78) 157818750000 0 = true :=
    take_step (n := 2) (t := 78) (b := 30124) rfl rfl ArealUCore.ArealUK.chunk_15061 s62
  have s60 : leavesOK ctxLitU 157243750000 0 ((leaves.drop 30120).take 80) 157818750000 0 = true :=
    take_step (n := 2) (t := 80) (b := 30122) rfl rfl ArealUCore.ArealUK.chunk_15060 s61
  have s59 : leavesOK ctxLitU 314468750000 1 ((leaves.drop 30118).take 82) 157818750000 0 = true :=
    take_step (n := 2) (t := 82) (b := 30120) rfl rfl ArealUCore.ArealUK.chunk_15059 s60
  have s58 : leavesOK ctxLitU 314456250000 1 ((leaves.drop 30116).take 84) 157818750000 0 = true :=
    take_step (n := 2) (t := 84) (b := 30118) rfl rfl ArealUCore.ArealUK.chunk_15058 s59
  have s57 : leavesOK ctxLitU 314437500000 1 ((leaves.drop 30114).take 86) 157818750000 0 = true :=
    take_step (n := 2) (t := 86) (b := 30116) rfl rfl ArealUCore.ArealUK.chunk_15057 s58
  have s56 : leavesOK ctxLitU 157200000000 0 ((leaves.drop 30112).take 88) 157818750000 0 = true :=
    take_step (n := 2) (t := 88) (b := 30114) rfl rfl ArealUCore.ArealUK.chunk_15056 s57
  have s55 : leavesOK ctxLitU 314375000000 1 ((leaves.drop 30110).take 90) 157818750000 0 = true :=
    take_step (n := 2) (t := 90) (b := 30112) rfl rfl ArealUCore.ArealUK.chunk_15055 s56
  have s54 : leavesOK ctxLitU 314350000000 1 ((leaves.drop 30108).take 92) 157818750000 0 = true :=
    take_step (n := 2) (t := 92) (b := 30110) rfl rfl ArealUCore.ArealUK.chunk_15054 s55
  have s53 : leavesOK ctxLitU 157162500000 0 ((leaves.drop 30106).take 94) 157818750000 0 = true :=
    take_step (n := 2) (t := 94) (b := 30108) rfl rfl ArealUCore.ArealUK.chunk_15053 s54
  have s52 : leavesOK ctxLitU 157150000000 0 ((leaves.drop 30104).take 96) 157818750000 0 = true :=
    take_step (n := 2) (t := 96) (b := 30106) rfl rfl ArealUCore.ArealUK.chunk_15052 s53
  have s51 : leavesOK ctxLitU 157137500000 0 ((leaves.drop 30102).take 98) 157818750000 0 = true :=
    take_step (n := 2) (t := 98) (b := 30104) rfl rfl ArealUCore.ArealUK.chunk_15051 s52
  have s50 : leavesOK ctxLitU 157125000000 0 ((leaves.drop 30100).take 100) 157818750000 0 = true :=
    take_step (n := 2) (t := 100) (b := 30102) rfl rfl ArealUCore.ArealUK.chunk_15050 s51
  have s49 : leavesOK ctxLitU 157100000000 0 ((leaves.drop 30098).take 102) 157818750000 0 = true :=
    take_step (n := 2) (t := 102) (b := 30100) rfl rfl ArealUCore.ArealUK.chunk_15049 s50
  have s48 : leavesOK ctxLitU 314175000000 1 ((leaves.drop 30096).take 104) 157818750000 0 = true :=
    take_step (n := 2) (t := 104) (b := 30098) rfl rfl ArealUCore.ArealUK.chunk_15048 s49
  have s47 : leavesOK ctxLitU 314150000000 1 ((leaves.drop 30094).take 106) 157818750000 0 = true :=
    take_step (n := 2) (t := 106) (b := 30096) rfl rfl ArealUCore.ArealUK.chunk_15047 s48
  have s46 : leavesOK ctxLitU 157062500000 0 ((leaves.drop 30092).take 108) 157818750000 0 = true :=
    take_step (n := 2) (t := 108) (b := 30094) rfl rfl ArealUCore.ArealUK.chunk_15046 s47
  have s45 : leavesOK ctxLitU 157050000000 0 ((leaves.drop 30090).take 110) 157818750000 0 = true :=
    take_step (n := 2) (t := 110) (b := 30092) rfl rfl ArealUCore.ArealUK.chunk_15045 s46
  have s44 : leavesOK ctxLitU 157037500000 0 ((leaves.drop 30088).take 112) 157818750000 0 = true :=
    take_step (n := 2) (t := 112) (b := 30090) rfl rfl ArealUCore.ArealUK.chunk_15044 s45
  have s43 : leavesOK ctxLitU 157025000000 0 ((leaves.drop 30086).take 114) 157818750000 0 = true :=
    take_step (n := 2) (t := 114) (b := 30088) rfl rfl ArealUCore.ArealUK.chunk_15043 s44
  have s42 : leavesOK ctxLitU 157012500000 0 ((leaves.drop 30084).take 116) 157818750000 0 = true :=
    take_step (n := 2) (t := 116) (b := 30086) rfl rfl ArealUCore.ArealUK.chunk_15042 s43
  have s41 : leavesOK ctxLitU 157000000000 0 ((leaves.drop 30082).take 118) 157818750000 0 = true :=
    take_step (n := 2) (t := 118) (b := 30084) rfl rfl ArealUCore.ArealUK.chunk_15041 s42
  have s40 : leavesOK ctxLitU 156987500000 0 ((leaves.drop 30080).take 120) 157818750000 0 = true :=
    take_step (n := 2) (t := 120) (b := 30082) rfl rfl ArealUCore.ArealUK.chunk_15040 s41
  have s39 : leavesOK ctxLitU 156975000000 0 ((leaves.drop 30078).take 122) 157818750000 0 = true :=
    take_step (n := 2) (t := 122) (b := 30080) rfl rfl ArealUCore.ArealUK.chunk_15039 s40
  have s38 : leavesOK ctxLitU 156962500000 0 ((leaves.drop 30076).take 124) 157818750000 0 = true :=
    take_step (n := 2) (t := 124) (b := 30078) rfl rfl ArealUCore.ArealUK.chunk_15038 s39
  have s37 : leavesOK ctxLitU 156950000000 0 ((leaves.drop 30074).take 126) 157818750000 0 = true :=
    take_step (n := 2) (t := 126) (b := 30076) rfl rfl ArealUCore.ArealUK.chunk_15037 s38
  have s36 : leavesOK ctxLitU 156937500000 0 ((leaves.drop 30072).take 128) 157818750000 0 = true :=
    take_step (n := 2) (t := 128) (b := 30074) rfl rfl ArealUCore.ArealUK.chunk_15036 s37
  have s35 : leavesOK ctxLitU 156925000000 0 ((leaves.drop 30070).take 130) 157818750000 0 = true :=
    take_step (n := 2) (t := 130) (b := 30072) rfl rfl ArealUCore.ArealUK.chunk_15035 s36
  have s34 : leavesOK ctxLitU 313825000000 1 ((leaves.drop 30068).take 132) 157818750000 0 = true :=
    take_step (n := 2) (t := 132) (b := 30070) rfl rfl ArealUCore.ArealUK.chunk_15034 s35
  have s33 : leavesOK ctxLitU 313800000000 1 ((leaves.drop 30066).take 134) 157818750000 0 = true :=
    take_step (n := 2) (t := 134) (b := 30068) rfl rfl ArealUCore.ArealUK.chunk_15033 s34
  have s32 : leavesOK ctxLitU 156875000000 0 ((leaves.drop 30064).take 136) 157818750000 0 = true :=
    take_step (n := 2) (t := 136) (b := 30066) rfl rfl ArealUCore.ArealUK.chunk_15032 s33
  have s31 : leavesOK ctxLitU 156862500000 0 ((leaves.drop 30062).take 138) 157818750000 0 = true :=
    take_step (n := 2) (t := 138) (b := 30064) rfl rfl ArealUCore.ArealUK.chunk_15031 s32
  have s30 : leavesOK ctxLitU 156850000000 0 ((leaves.drop 30060).take 140) 157818750000 0 = true :=
    take_step (n := 2) (t := 140) (b := 30062) rfl rfl ArealUCore.ArealUK.chunk_15030 s31
  have s29 : leavesOK ctxLitU 156837500000 0 ((leaves.drop 30058).take 142) 157818750000 0 = true :=
    take_step (n := 2) (t := 142) (b := 30060) rfl rfl ArealUCore.ArealUK.chunk_15029 s30
  have s28 : leavesOK ctxLitU 156825000000 0 ((leaves.drop 30056).take 144) 157818750000 0 = true :=
    take_step (n := 2) (t := 144) (b := 30058) rfl rfl ArealUCore.ArealUK.chunk_15028 s29
  have s27 : leavesOK ctxLitU 156800000000 0 ((leaves.drop 30054).take 146) 157818750000 0 = true :=
    take_step (n := 2) (t := 146) (b := 30056) rfl rfl ArealUCore.ArealUK.chunk_15027 s28
  have s26 : leavesOK ctxLitU 156775000000 0 ((leaves.drop 30052).take 148) 157818750000 0 = true :=
    take_step (n := 2) (t := 148) (b := 30054) rfl rfl ArealUCore.ArealUK.chunk_15026 s27
  have s25 : leavesOK ctxLitU 156762500000 0 ((leaves.drop 30050).take 150) 157818750000 0 = true :=
    take_step (n := 2) (t := 150) (b := 30052) rfl rfl ArealUCore.ArealUK.chunk_15025 s26
  have s24 : leavesOK ctxLitU 156750000000 0 ((leaves.drop 30048).take 152) 157818750000 0 = true :=
    take_step (n := 2) (t := 152) (b := 30050) rfl rfl ArealUCore.ArealUK.chunk_15024 s25
  have s23 : leavesOK ctxLitU 156737500000 0 ((leaves.drop 30046).take 154) 157818750000 0 = true :=
    take_step (n := 2) (t := 154) (b := 30048) rfl rfl ArealUCore.ArealUK.chunk_15023 s24
  have s22 : leavesOK ctxLitU 156725000000 0 ((leaves.drop 30044).take 156) 157818750000 0 = true :=
    take_step (n := 2) (t := 156) (b := 30046) rfl rfl ArealUCore.ArealUK.chunk_15022 s23
  have s21 : leavesOK ctxLitU 156700000000 0 ((leaves.drop 30042).take 158) 157818750000 0 = true :=
    take_step (n := 2) (t := 158) (b := 30044) rfl rfl ArealUCore.ArealUK.chunk_15021 s22
  have s20 : leavesOK ctxLitU 313375000000 1 ((leaves.drop 30040).take 160) 157818750000 0 = true :=
    take_step (n := 2) (t := 160) (b := 30042) rfl rfl ArealUCore.ArealUK.chunk_15020 s21
  have s19 : leavesOK ctxLitU 313350000000 1 ((leaves.drop 30038).take 162) 157818750000 0 = true :=
    take_step (n := 2) (t := 162) (b := 30040) rfl rfl ArealUCore.ArealUK.chunk_15019 s20
  have s18 : leavesOK ctxLitU 156662500000 0 ((leaves.drop 30036).take 164) 157818750000 0 = true :=
    take_step (n := 2) (t := 164) (b := 30038) rfl rfl ArealUCore.ArealUK.chunk_15018 s19
  have s17 : leavesOK ctxLitU 156650000000 0 ((leaves.drop 30034).take 166) 157818750000 0 = true :=
    take_step (n := 2) (t := 166) (b := 30036) rfl rfl ArealUCore.ArealUK.chunk_15017 s18
  have s16 : leavesOK ctxLitU 156637500000 0 ((leaves.drop 30032).take 168) 157818750000 0 = true :=
    take_step (n := 2) (t := 168) (b := 30034) rfl rfl ArealUCore.ArealUK.chunk_15016 s17
  have s15 : leavesOK ctxLitU 156625000000 0 ((leaves.drop 30030).take 170) 157818750000 0 = true :=
    take_step (n := 2) (t := 170) (b := 30032) rfl rfl ArealUCore.ArealUK.chunk_15015 s16
  have s14 : leavesOK ctxLitU 156600000000 0 ((leaves.drop 30028).take 172) 157818750000 0 = true :=
    take_step (n := 2) (t := 172) (b := 30030) rfl rfl ArealUCore.ArealUK.chunk_15014 s15
  have s13 : leavesOK ctxLitU 313175000000 1 ((leaves.drop 30026).take 174) 157818750000 0 = true :=
    take_step (n := 2) (t := 174) (b := 30028) rfl rfl ArealUCore.ArealUK.chunk_15013 s14
  have s12 : leavesOK ctxLitU 313150000000 1 ((leaves.drop 30024).take 176) 157818750000 0 = true :=
    take_step (n := 2) (t := 176) (b := 30026) rfl rfl ArealUCore.ArealUK.chunk_15012 s13
  have s11 : leavesOK ctxLitU 156562500000 0 ((leaves.drop 30022).take 178) 157818750000 0 = true :=
    take_step (n := 2) (t := 178) (b := 30024) rfl rfl ArealUCore.ArealUK.chunk_15011 s12
  have s10 : leavesOK ctxLitU 156550000000 0 ((leaves.drop 30020).take 180) 157818750000 0 = true :=
    take_step (n := 2) (t := 180) (b := 30022) rfl rfl ArealUCore.ArealUK.chunk_15010 s11
  have s9 : leavesOK ctxLitU 156537500000 0 ((leaves.drop 30018).take 182) 157818750000 0 = true :=
    take_step (n := 2) (t := 182) (b := 30020) rfl rfl ArealUCore.ArealUK.chunk_15009 s10
  have s8 : leavesOK ctxLitU 156525000000 0 ((leaves.drop 30016).take 184) 157818750000 0 = true :=
    take_step (n := 2) (t := 184) (b := 30018) rfl rfl ArealUCore.ArealUK.chunk_15008 s9
  have s7 : leavesOK ctxLitU 313025000000 1 ((leaves.drop 30014).take 186) 157818750000 0 = true :=
    take_step (n := 2) (t := 186) (b := 30016) rfl rfl ArealUCore.ArealUK.chunk_15007 s8
  have s6 : leavesOK ctxLitU 313000000000 1 ((leaves.drop 30012).take 188) 157818750000 0 = true :=
    take_step (n := 2) (t := 188) (b := 30014) rfl rfl ArealUCore.ArealUK.chunk_15006 s7
  have s5 : leavesOK ctxLitU 312975000000 1 ((leaves.drop 30010).take 190) 157818750000 0 = true :=
    take_step (n := 2) (t := 190) (b := 30012) rfl rfl ArealUCore.ArealUK.chunk_15005 s6
  have s4 : leavesOK ctxLitU 312950000000 1 ((leaves.drop 30008).take 192) 157818750000 0 = true :=
    take_step (n := 2) (t := 192) (b := 30010) rfl rfl ArealUCore.ArealUK.chunk_15004 s5
  have s3 : leavesOK ctxLitU 156462500000 0 ((leaves.drop 30006).take 194) 157818750000 0 = true :=
    take_step (n := 2) (t := 194) (b := 30008) rfl rfl ArealUCore.ArealUK.chunk_15003 s4
  have s2 : leavesOK ctxLitU 156450000000 0 ((leaves.drop 30004).take 196) 157818750000 0 = true :=
    take_step (n := 2) (t := 196) (b := 30006) rfl rfl ArealUCore.ArealUK.chunk_15002 s3
  have s1 : leavesOK ctxLitU 156437500000 0 ((leaves.drop 30002).take 198) 157818750000 0 = true :=
    take_step (n := 2) (t := 198) (b := 30004) rfl rfl ArealUCore.ArealUK.chunk_15001 s2
  have s0 : leavesOK ctxLitU 156425000000 0 ((leaves.drop 30000).take 200) 157818750000 0 = true :=
    take_step (n := 2) (t := 200) (b := 30002) rfl rfl ArealUCore.ArealUK.chunk_15000 s1
  exact s0

end Areal.UCert

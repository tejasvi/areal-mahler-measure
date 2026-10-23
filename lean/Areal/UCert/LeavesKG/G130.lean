import ArealUK.Chunk13000
import ArealUK.Chunk13001
import ArealUK.Chunk13002
import ArealUK.Chunk13003
import ArealUK.Chunk13004
import ArealUK.Chunk13005
import ArealUK.Chunk13006
import ArealUK.Chunk13007
import ArealUK.Chunk13008
import ArealUK.Chunk13009
import ArealUK.Chunk13010
import ArealUK.Chunk13011
import ArealUK.Chunk13012
import ArealUK.Chunk13013
import ArealUK.Chunk13014
import ArealUK.Chunk13015
import ArealUK.Chunk13016
import ArealUK.Chunk13017
import ArealUK.Chunk13018
import ArealUK.Chunk13019
import ArealUK.Chunk13020
import ArealUK.Chunk13021
import ArealUK.Chunk13022
import ArealUK.Chunk13023
import ArealUK.Chunk13024
import ArealUK.Chunk13025
import ArealUK.Chunk13026
import ArealUK.Chunk13027
import ArealUK.Chunk13028
import ArealUK.Chunk13029
import ArealUK.Chunk13030
import ArealUK.Chunk13031
import ArealUK.Chunk13032
import ArealUK.Chunk13033
import ArealUK.Chunk13034
import ArealUK.Chunk13035
import ArealUK.Chunk13036
import ArealUK.Chunk13037
import ArealUK.Chunk13038
import ArealUK.Chunk13039
import ArealUK.Chunk13040
import ArealUK.Chunk13041
import ArealUK.Chunk13042
import ArealUK.Chunk13043
import ArealUK.Chunk13044
import ArealUK.Chunk13045
import ArealUK.Chunk13046
import ArealUK.Chunk13047
import ArealUK.Chunk13048
import ArealUK.Chunk13049
import ArealUK.Chunk13050
import ArealUK.Chunk13051
import ArealUK.Chunk13052
import ArealUK.Chunk13053
import ArealUK.Chunk13054
import ArealUK.Chunk13055
import ArealUK.Chunk13056
import ArealUK.Chunk13057
import ArealUK.Chunk13058
import ArealUK.Chunk13059
import ArealUK.Chunk13060
import ArealUK.Chunk13061
import ArealUK.Chunk13062
import ArealUK.Chunk13063
import ArealUK.Chunk13064
import ArealUK.Chunk13065
import ArealUK.Chunk13066
import ArealUK.Chunk13067
import ArealUK.Chunk13068
import ArealUK.Chunk13069
import ArealUK.Chunk13070
import ArealUK.Chunk13071
import ArealUK.Chunk13072
import ArealUK.Chunk13073
import ArealUK.Chunk13074
import ArealUK.Chunk13075
import ArealUK.Chunk13076
import ArealUK.Chunk13077
import ArealUK.Chunk13078
import ArealUK.Chunk13079
import ArealUK.Chunk13080
import ArealUK.Chunk13081
import ArealUK.Chunk13082
import ArealUK.Chunk13083
import ArealUK.Chunk13084
import ArealUK.Chunk13085
import ArealUK.Chunk13086
import ArealUK.Chunk13087
import ArealUK.Chunk13088
import ArealUK.Chunk13089
import ArealUK.Chunk13090
import ArealUK.Chunk13091
import ArealUK.Chunk13092
import ArealUK.Chunk13093
import ArealUK.Chunk13094
import ArealUK.Chunk13095
import ArealUK.Chunk13096
import ArealUK.Chunk13097
import ArealUK.Chunk13098
import ArealUK.Chunk13099
import Areal.UCert.LeavesKGen

/-! Group 130 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_130 : leavesOK ctxLitU 528350000000 2 ((leaves.drop 26000).take 200) 266500000000 1 = true := by
  have s99 := ArealUCore.ArealUK.chunk_13099
  have s98 : leavesOK ctxLitU 266462500000 1 ((leaves.drop 26196).take 4) 266500000000 1 = true :=
    take_step (n := 2) (t := 4) (b := 26198) rfl rfl ArealUCore.ArealUK.chunk_13098 s99
  have s97 : leavesOK ctxLitU 266450000000 1 ((leaves.drop 26194).take 6) 266500000000 1 = true :=
    take_step (n := 2) (t := 6) (b := 26196) rfl rfl ArealUCore.ArealUK.chunk_13097 s98
  have s96 : leavesOK ctxLitU 266425000000 1 ((leaves.drop 26192).take 8) 266500000000 1 = true :=
    take_step (n := 2) (t := 8) (b := 26194) rfl rfl ArealUCore.ArealUK.chunk_13096 s97
  have s95 : leavesOK ctxLitU 266400000000 1 ((leaves.drop 26190).take 10) 266500000000 1 = true :=
    take_step (n := 2) (t := 10) (b := 26192) rfl rfl ArealUCore.ArealUK.chunk_13095 s96
  have s94 : leavesOK ctxLitU 266375000000 1 ((leaves.drop 26188).take 12) 266500000000 1 = true :=
    take_step (n := 2) (t := 12) (b := 26190) rfl rfl ArealUCore.ArealUK.chunk_13094 s95
  have s93 : leavesOK ctxLitU 266350000000 1 ((leaves.drop 26186).take 14) 266500000000 1 = true :=
    take_step (n := 2) (t := 14) (b := 26188) rfl rfl ArealUCore.ArealUK.chunk_13093 s94
  have s92 : leavesOK ctxLitU 133162500000 0 ((leaves.drop 26184).take 16) 266500000000 1 = true :=
    take_step (n := 2) (t := 16) (b := 26186) rfl rfl ArealUCore.ArealUK.chunk_13092 s93
  have s91 : leavesOK ctxLitU 133150000000 0 ((leaves.drop 26182).take 18) 266500000000 1 = true :=
    take_step (n := 2) (t := 18) (b := 26184) rfl rfl ArealUCore.ArealUK.chunk_13091 s92
  have s90 : leavesOK ctxLitU 266275000000 1 ((leaves.drop 26180).take 20) 266500000000 1 = true :=
    take_step (n := 2) (t := 20) (b := 26182) rfl rfl ArealUCore.ArealUK.chunk_13090 s91
  have s89 : leavesOK ctxLitU 266250000000 1 ((leaves.drop 26178).take 22) 266500000000 1 = true :=
    take_step (n := 2) (t := 22) (b := 26180) rfl rfl ArealUCore.ArealUK.chunk_13089 s90
  have s88 : leavesOK ctxLitU 532450000000 2 ((leaves.drop 26176).take 24) 266500000000 1 = true :=
    take_step (n := 2) (t := 24) (b := 26178) rfl rfl ArealUCore.ArealUK.chunk_13088 s89
  have s87 : leavesOK ctxLitU 532400000000 2 ((leaves.drop 26174).take 26) 266500000000 1 = true :=
    take_step (n := 2) (t := 26) (b := 26176) rfl rfl ArealUCore.ArealUK.chunk_13087 s88
  have s86 : leavesOK ctxLitU 532350000000 2 ((leaves.drop 26172).take 28) 266500000000 1 = true :=
    take_step (n := 2) (t := 28) (b := 26174) rfl rfl ArealUCore.ArealUK.chunk_13086 s87
  have s85 : leavesOK ctxLitU 532300000000 2 ((leaves.drop 26170).take 30) 266500000000 1 = true :=
    take_step (n := 2) (t := 30) (b := 26172) rfl rfl ArealUCore.ArealUK.chunk_13085 s86
  have s84 : leavesOK ctxLitU 266125000000 1 ((leaves.drop 26168).take 32) 266500000000 1 = true :=
    take_step (n := 2) (t := 32) (b := 26170) rfl rfl ArealUCore.ArealUK.chunk_13084 s85
  have s83 : leavesOK ctxLitU 266100000000 1 ((leaves.drop 26166).take 34) 266500000000 1 = true :=
    take_step (n := 2) (t := 34) (b := 26168) rfl rfl ArealUCore.ArealUK.chunk_13083 s84
  have s82 : leavesOK ctxLitU 133037500000 0 ((leaves.drop 26164).take 36) 266500000000 1 = true :=
    take_step (n := 2) (t := 36) (b := 26166) rfl rfl ArealUCore.ArealUK.chunk_13082 s83
  have s81 : leavesOK ctxLitU 133025000000 0 ((leaves.drop 26162).take 38) 266500000000 1 = true :=
    take_step (n := 2) (t := 38) (b := 26164) rfl rfl ArealUCore.ArealUK.chunk_13081 s82
  have s80 : leavesOK ctxLitU 266025000000 1 ((leaves.drop 26160).take 40) 266500000000 1 = true :=
    take_step (n := 2) (t := 40) (b := 26162) rfl rfl ArealUCore.ArealUK.chunk_13080 s81
  have s79 : leavesOK ctxLitU 266000000000 1 ((leaves.drop 26158).take 42) 266500000000 1 = true :=
    take_step (n := 2) (t := 42) (b := 26160) rfl rfl ArealUCore.ArealUK.chunk_13079 s80
  have s78 : leavesOK ctxLitU 265975000000 1 ((leaves.drop 26156).take 44) 266500000000 1 = true :=
    take_step (n := 2) (t := 44) (b := 26158) rfl rfl ArealUCore.ArealUK.chunk_13078 s79
  have s77 : leavesOK ctxLitU 265950000000 1 ((leaves.drop 26154).take 46) 266500000000 1 = true :=
    take_step (n := 2) (t := 46) (b := 26156) rfl rfl ArealUCore.ArealUK.chunk_13077 s78
  have s76 : leavesOK ctxLitU 132962500000 0 ((leaves.drop 26152).take 48) 266500000000 1 = true :=
    take_step (n := 2) (t := 48) (b := 26154) rfl rfl ArealUCore.ArealUK.chunk_13076 s77
  have s75 : leavesOK ctxLitU 132950000000 0 ((leaves.drop 26150).take 50) 266500000000 1 = true :=
    take_step (n := 2) (t := 50) (b := 26152) rfl rfl ArealUCore.ArealUK.chunk_13075 s76
  have s74 : leavesOK ctxLitU 132937500000 0 ((leaves.drop 26148).take 52) 266500000000 1 = true :=
    take_step (n := 2) (t := 52) (b := 26150) rfl rfl ArealUCore.ArealUK.chunk_13074 s75
  have s73 : leavesOK ctxLitU 265862500000 1 ((leaves.drop 26146).take 54) 266500000000 1 = true :=
    take_step (n := 2) (t := 54) (b := 26148) rfl rfl ArealUCore.ArealUK.chunk_13073 s74
  have s72 : leavesOK ctxLitU 265850000000 1 ((leaves.drop 26144).take 56) 266500000000 1 = true :=
    take_step (n := 2) (t := 56) (b := 26146) rfl rfl ArealUCore.ArealUK.chunk_13072 s73
  have s71 : leavesOK ctxLitU 531662500000 2 ((leaves.drop 26142).take 58) 266500000000 1 = true :=
    take_step (n := 2) (t := 58) (b := 26144) rfl rfl ArealUCore.ArealUK.chunk_13071 s72
  have s70 : leavesOK ctxLitU 531637500000 2 ((leaves.drop 26140).take 60) 266500000000 1 = true :=
    take_step (n := 2) (t := 60) (b := 26142) rfl rfl ArealUCore.ArealUK.chunk_13070 s71
  have s69 : leavesOK ctxLitU 265800000000 1 ((leaves.drop 26138).take 62) 266500000000 1 = true :=
    take_step (n := 2) (t := 62) (b := 26140) rfl rfl ArealUCore.ArealUK.chunk_13069 s70
  have s68 : leavesOK ctxLitU 531550000000 2 ((leaves.drop 26136).take 64) 266500000000 1 = true :=
    take_step (n := 2) (t := 64) (b := 26138) rfl rfl ArealUCore.ArealUK.chunk_13068 s69
  have s67 : leavesOK ctxLitU 531500000000 2 ((leaves.drop 26134).take 66) 266500000000 1 = true :=
    take_step (n := 2) (t := 66) (b := 26136) rfl rfl ArealUCore.ArealUK.chunk_13067 s68
  have s66 : leavesOK ctxLitU 531450000000 2 ((leaves.drop 26132).take 68) 266500000000 1 = true :=
    take_step (n := 2) (t := 68) (b := 26134) rfl rfl ArealUCore.ArealUK.chunk_13066 s67
  have s65 : leavesOK ctxLitU 531400000000 2 ((leaves.drop 26130).take 70) 266500000000 1 = true :=
    take_step (n := 2) (t := 70) (b := 26132) rfl rfl ArealUCore.ArealUK.chunk_13065 s66
  have s64 : leavesOK ctxLitU 531350000000 2 ((leaves.drop 26128).take 72) 266500000000 1 = true :=
    take_step (n := 2) (t := 72) (b := 26130) rfl rfl ArealUCore.ArealUK.chunk_13064 s65
  have s63 : leavesOK ctxLitU 531300000000 2 ((leaves.drop 26126).take 74) 266500000000 1 = true :=
    take_step (n := 2) (t := 74) (b := 26128) rfl rfl ArealUCore.ArealUK.chunk_13063 s64
  have s62 : leavesOK ctxLitU 531250000000 2 ((leaves.drop 26124).take 76) 266500000000 1 = true :=
    take_step (n := 2) (t := 76) (b := 26126) rfl rfl ArealUCore.ArealUK.chunk_13062 s63
  have s61 : leavesOK ctxLitU 531200000000 2 ((leaves.drop 26122).take 78) 266500000000 1 = true :=
    take_step (n := 2) (t := 78) (b := 26124) rfl rfl ArealUCore.ArealUK.chunk_13061 s62
  have s60 : leavesOK ctxLitU 265575000000 1 ((leaves.drop 26120).take 80) 266500000000 1 = true :=
    take_step (n := 2) (t := 80) (b := 26122) rfl rfl ArealUCore.ArealUK.chunk_13060 s61
  have s59 : leavesOK ctxLitU 265550000000 1 ((leaves.drop 26118).take 82) 266500000000 1 = true :=
    take_step (n := 2) (t := 82) (b := 26120) rfl rfl ArealUCore.ArealUK.chunk_13059 s60
  have s58 : leavesOK ctxLitU 265537500000 1 ((leaves.drop 26116).take 84) 266500000000 1 = true :=
    take_step (n := 2) (t := 84) (b := 26118) rfl rfl ArealUCore.ArealUK.chunk_13058 s59
  have s57 : leavesOK ctxLitU 265525000000 1 ((leaves.drop 26114).take 86) 266500000000 1 = true :=
    take_step (n := 2) (t := 86) (b := 26116) rfl rfl ArealUCore.ArealUK.chunk_13057 s58
  have s56 : leavesOK ctxLitU 132750000000 0 ((leaves.drop 26112).take 88) 266500000000 1 = true :=
    take_step (n := 2) (t := 88) (b := 26114) rfl rfl ArealUCore.ArealUK.chunk_13056 s57
  have s55 : leavesOK ctxLitU 132737500000 0 ((leaves.drop 26110).take 90) 266500000000 1 = true :=
    take_step (n := 2) (t := 90) (b := 26112) rfl rfl ArealUCore.ArealUK.chunk_13055 s56
  have s54 : leavesOK ctxLitU 265462500000 1 ((leaves.drop 26108).take 92) 266500000000 1 = true :=
    take_step (n := 2) (t := 92) (b := 26110) rfl rfl ArealUCore.ArealUK.chunk_13054 s55
  have s53 : leavesOK ctxLitU 265450000000 1 ((leaves.drop 26106).take 94) 266500000000 1 = true :=
    take_step (n := 2) (t := 94) (b := 26108) rfl rfl ArealUCore.ArealUK.chunk_13053 s54
  have s52 : leavesOK ctxLitU 265425000000 1 ((leaves.drop 26104).take 96) 266500000000 1 = true :=
    take_step (n := 2) (t := 96) (b := 26106) rfl rfl ArealUCore.ArealUK.chunk_13052 s53
  have s51 : leavesOK ctxLitU 265400000000 1 ((leaves.drop 26102).take 98) 266500000000 1 = true :=
    take_step (n := 2) (t := 98) (b := 26104) rfl rfl ArealUCore.ArealUK.chunk_13051 s52
  have s50 : leavesOK ctxLitU 530750000000 2 ((leaves.drop 26100).take 100) 266500000000 1 = true :=
    take_step (n := 2) (t := 100) (b := 26102) rfl rfl ArealUCore.ArealUK.chunk_13050 s51
  have s49 : leavesOK ctxLitU 530700000000 2 ((leaves.drop 26098).take 102) 266500000000 1 = true :=
    take_step (n := 2) (t := 102) (b := 26100) rfl rfl ArealUCore.ArealUK.chunk_13049 s50
  have s48 : leavesOK ctxLitU 530650000000 2 ((leaves.drop 26096).take 104) 266500000000 1 = true :=
    take_step (n := 2) (t := 104) (b := 26098) rfl rfl ArealUCore.ArealUK.chunk_13048 s49
  have s47 : leavesOK ctxLitU 530600000000 2 ((leaves.drop 26094).take 106) 266500000000 1 = true :=
    take_step (n := 2) (t := 106) (b := 26096) rfl rfl ArealUCore.ArealUK.chunk_13047 s48
  have s46 : leavesOK ctxLitU 530550000000 2 ((leaves.drop 26092).take 108) 266500000000 1 = true :=
    take_step (n := 2) (t := 108) (b := 26094) rfl rfl ArealUCore.ArealUK.chunk_13046 s47
  have s45 : leavesOK ctxLitU 530500000000 2 ((leaves.drop 26090).take 110) 266500000000 1 = true :=
    take_step (n := 2) (t := 110) (b := 26092) rfl rfl ArealUCore.ArealUK.chunk_13045 s46
  have s44 : leavesOK ctxLitU 530450000000 2 ((leaves.drop 26088).take 112) 266500000000 1 = true :=
    take_step (n := 2) (t := 112) (b := 26090) rfl rfl ArealUCore.ArealUK.chunk_13044 s45
  have s43 : leavesOK ctxLitU 530400000000 2 ((leaves.drop 26086).take 114) 266500000000 1 = true :=
    take_step (n := 2) (t := 114) (b := 26088) rfl rfl ArealUCore.ArealUK.chunk_13043 s44
  have s42 : leavesOK ctxLitU 530350000000 2 ((leaves.drop 26084).take 116) 266500000000 1 = true :=
    take_step (n := 2) (t := 116) (b := 26086) rfl rfl ArealUCore.ArealUK.chunk_13042 s43
  have s41 : leavesOK ctxLitU 530300000000 2 ((leaves.drop 26082).take 118) 266500000000 1 = true :=
    take_step (n := 2) (t := 118) (b := 26084) rfl rfl ArealUCore.ArealUK.chunk_13041 s42
  have s40 : leavesOK ctxLitU 530250000000 2 ((leaves.drop 26080).take 120) 266500000000 1 = true :=
    take_step (n := 2) (t := 120) (b := 26082) rfl rfl ArealUCore.ArealUK.chunk_13040 s41
  have s39 : leavesOK ctxLitU 530200000000 2 ((leaves.drop 26078).take 122) 266500000000 1 = true :=
    take_step (n := 2) (t := 122) (b := 26080) rfl rfl ArealUCore.ArealUK.chunk_13039 s40
  have s38 : leavesOK ctxLitU 530150000000 2 ((leaves.drop 26076).take 124) 266500000000 1 = true :=
    take_step (n := 2) (t := 124) (b := 26078) rfl rfl ArealUCore.ArealUK.chunk_13038 s39
  have s37 : leavesOK ctxLitU 530100000000 2 ((leaves.drop 26074).take 126) 266500000000 1 = true :=
    take_step (n := 2) (t := 126) (b := 26076) rfl rfl ArealUCore.ArealUK.chunk_13037 s38
  have s36 : leavesOK ctxLitU 530050000000 2 ((leaves.drop 26072).take 128) 266500000000 1 = true :=
    take_step (n := 2) (t := 128) (b := 26074) rfl rfl ArealUCore.ArealUK.chunk_13036 s37
  have s35 : leavesOK ctxLitU 530000000000 2 ((leaves.drop 26070).take 130) 266500000000 1 = true :=
    take_step (n := 2) (t := 130) (b := 26072) rfl rfl ArealUCore.ArealUK.chunk_13035 s36
  have s34 : leavesOK ctxLitU 529962500000 2 ((leaves.drop 26068).take 132) 266500000000 1 = true :=
    take_step (n := 2) (t := 132) (b := 26070) rfl rfl ArealUCore.ArealUK.chunk_13034 s35
  have s33 : leavesOK ctxLitU 529937500000 2 ((leaves.drop 26066).take 134) 266500000000 1 = true :=
    take_step (n := 2) (t := 134) (b := 26068) rfl rfl ArealUCore.ArealUK.chunk_13033 s34
  have s32 : leavesOK ctxLitU 264950000000 1 ((leaves.drop 26064).take 136) 266500000000 1 = true :=
    take_step (n := 2) (t := 136) (b := 26066) rfl rfl ArealUCore.ArealUK.chunk_13032 s33
  have s31 : leavesOK ctxLitU 132462500000 0 ((leaves.drop 26062).take 138) 266500000000 1 = true :=
    take_step (n := 2) (t := 138) (b := 26064) rfl rfl ArealUCore.ArealUK.chunk_13031 s32
  have s30 : leavesOK ctxLitU 132450000000 0 ((leaves.drop 26060).take 140) 266500000000 1 = true :=
    take_step (n := 2) (t := 140) (b := 26062) rfl rfl ArealUCore.ArealUK.chunk_13030 s31
  have s29 : leavesOK ctxLitU 132437500000 0 ((leaves.drop 26058).take 142) 266500000000 1 = true :=
    take_step (n := 2) (t := 142) (b := 26060) rfl rfl ArealUCore.ArealUK.chunk_13029 s30
  have s28 : leavesOK ctxLitU 132425000000 0 ((leaves.drop 26056).take 144) 266500000000 1 = true :=
    take_step (n := 2) (t := 144) (b := 26058) rfl rfl ArealUCore.ArealUK.chunk_13028 s29
  have s27 : leavesOK ctxLitU 264825000000 1 ((leaves.drop 26054).take 146) 266500000000 1 = true :=
    take_step (n := 2) (t := 146) (b := 26056) rfl rfl ArealUCore.ArealUK.chunk_13027 s28
  have s26 : leavesOK ctxLitU 264800000000 1 ((leaves.drop 26052).take 148) 266500000000 1 = true :=
    take_step (n := 2) (t := 148) (b := 26054) rfl rfl ArealUCore.ArealUK.chunk_13026 s27
  have s25 : leavesOK ctxLitU 529550000000 2 ((leaves.drop 26050).take 150) 266500000000 1 = true :=
    take_step (n := 2) (t := 150) (b := 26052) rfl rfl ArealUCore.ArealUK.chunk_13025 s26
  have s24 : leavesOK ctxLitU 529500000000 2 ((leaves.drop 26048).take 152) 266500000000 1 = true :=
    take_step (n := 2) (t := 152) (b := 26050) rfl rfl ArealUCore.ArealUK.chunk_13024 s25
  have s23 : leavesOK ctxLitU 529450000000 2 ((leaves.drop 26046).take 154) 266500000000 1 = true :=
    take_step (n := 2) (t := 154) (b := 26048) rfl rfl ArealUCore.ArealUK.chunk_13023 s24
  have s22 : leavesOK ctxLitU 529400000000 2 ((leaves.drop 26044).take 156) 266500000000 1 = true :=
    take_step (n := 2) (t := 156) (b := 26046) rfl rfl ArealUCore.ArealUK.chunk_13022 s23
  have s21 : leavesOK ctxLitU 529350000000 2 ((leaves.drop 26042).take 158) 266500000000 1 = true :=
    take_step (n := 2) (t := 158) (b := 26044) rfl rfl ArealUCore.ArealUK.chunk_13021 s22
  have s20 : leavesOK ctxLitU 529300000000 2 ((leaves.drop 26040).take 160) 266500000000 1 = true :=
    take_step (n := 2) (t := 160) (b := 26042) rfl rfl ArealUCore.ArealUK.chunk_13020 s21
  have s19 : leavesOK ctxLitU 529250000000 2 ((leaves.drop 26038).take 162) 266500000000 1 = true :=
    take_step (n := 2) (t := 162) (b := 26040) rfl rfl ArealUCore.ArealUK.chunk_13019 s20
  have s18 : leavesOK ctxLitU 529200000000 2 ((leaves.drop 26036).take 164) 266500000000 1 = true :=
    take_step (n := 2) (t := 164) (b := 26038) rfl rfl ArealUCore.ArealUK.chunk_13018 s19
  have s17 : leavesOK ctxLitU 264575000000 1 ((leaves.drop 26034).take 166) 266500000000 1 = true :=
    take_step (n := 2) (t := 166) (b := 26036) rfl rfl ArealUCore.ArealUK.chunk_13017 s18
  have s16 : leavesOK ctxLitU 264550000000 1 ((leaves.drop 26032).take 168) 266500000000 1 = true :=
    take_step (n := 2) (t := 168) (b := 26034) rfl rfl ArealUCore.ArealUK.chunk_13016 s17
  have s15 : leavesOK ctxLitU 132262500000 0 ((leaves.drop 26030).take 170) 266500000000 1 = true :=
    take_step (n := 2) (t := 170) (b := 26032) rfl rfl ArealUCore.ArealUK.chunk_13015 s16
  have s14 : leavesOK ctxLitU 132250000000 0 ((leaves.drop 26028).take 172) 266500000000 1 = true :=
    take_step (n := 2) (t := 172) (b := 26030) rfl rfl ArealUCore.ArealUK.chunk_13014 s15
  have s13 : leavesOK ctxLitU 132237500000 0 ((leaves.drop 26026).take 174) 266500000000 1 = true :=
    take_step (n := 2) (t := 174) (b := 26028) rfl rfl ArealUCore.ArealUK.chunk_13013 s14
  have s12 : leavesOK ctxLitU 264456250000 1 ((leaves.drop 26024).take 176) 266500000000 1 = true :=
    take_step (n := 2) (t := 176) (b := 26026) rfl rfl ArealUCore.ArealUK.chunk_13012 s13
  have s11 : leavesOK ctxLitU 264437500000 1 ((leaves.drop 26022).take 178) 266500000000 1 = true :=
    take_step (n := 2) (t := 178) (b := 26024) rfl rfl ArealUCore.ArealUK.chunk_13011 s12
  have s10 : leavesOK ctxLitU 264412500000 1 ((leaves.drop 26020).take 180) 266500000000 1 = true :=
    take_step (n := 2) (t := 180) (b := 26022) rfl rfl ArealUCore.ArealUK.chunk_13010 s11
  have s9 : leavesOK ctxLitU 264387500000 1 ((leaves.drop 26018).take 182) 266500000000 1 = true :=
    take_step (n := 2) (t := 182) (b := 26020) rfl rfl ArealUCore.ArealUK.chunk_13009 s10
  have s8 : leavesOK ctxLitU 264362500000 1 ((leaves.drop 26016).take 184) 266500000000 1 = true :=
    take_step (n := 2) (t := 184) (b := 26018) rfl rfl ArealUCore.ArealUK.chunk_13008 s9
  have s7 : leavesOK ctxLitU 264343750000 1 ((leaves.drop 26014).take 186) 266500000000 1 = true :=
    take_step (n := 2) (t := 186) (b := 26016) rfl rfl ArealUCore.ArealUK.chunk_13007 s8
  have s6 : leavesOK ctxLitU 132162500000 0 ((leaves.drop 26012).take 188) 266500000000 1 = true :=
    take_step (n := 2) (t := 188) (b := 26014) rfl rfl ArealUCore.ArealUK.chunk_13006 s7
  have s5 : leavesOK ctxLitU 132150000000 0 ((leaves.drop 26010).take 190) 266500000000 1 = true :=
    take_step (n := 2) (t := 190) (b := 26012) rfl rfl ArealUCore.ArealUK.chunk_13005 s6
  have s4 : leavesOK ctxLitU 132137500000 0 ((leaves.drop 26008).take 192) 266500000000 1 = true :=
    take_step (n := 2) (t := 192) (b := 26010) rfl rfl ArealUCore.ArealUK.chunk_13004 s5
  have s3 : leavesOK ctxLitU 132125000000 0 ((leaves.drop 26006).take 194) 266500000000 1 = true :=
    take_step (n := 2) (t := 194) (b := 26008) rfl rfl ArealUCore.ArealUK.chunk_13003 s4
  have s2 : leavesOK ctxLitU 264225000000 1 ((leaves.drop 26004).take 196) 266500000000 1 = true :=
    take_step (n := 2) (t := 196) (b := 26006) rfl rfl ArealUCore.ArealUK.chunk_13002 s3
  have s1 : leavesOK ctxLitU 264200000000 1 ((leaves.drop 26002).take 198) 266500000000 1 = true :=
    take_step (n := 2) (t := 198) (b := 26004) rfl rfl ArealUCore.ArealUK.chunk_13001 s2
  have s0 : leavesOK ctxLitU 528350000000 2 ((leaves.drop 26000).take 200) 266500000000 1 = true :=
    take_step (n := 2) (t := 200) (b := 26002) rfl rfl ArealUCore.ArealUK.chunk_13000 s1
  exact s0

end Areal.UCert

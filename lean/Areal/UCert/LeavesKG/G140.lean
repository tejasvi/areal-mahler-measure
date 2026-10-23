import ArealUK.Chunk14000
import ArealUK.Chunk14001
import ArealUK.Chunk14002
import ArealUK.Chunk14003
import ArealUK.Chunk14004
import ArealUK.Chunk14005
import ArealUK.Chunk14006
import ArealUK.Chunk14007
import ArealUK.Chunk14008
import ArealUK.Chunk14009
import ArealUK.Chunk14010
import ArealUK.Chunk14011
import ArealUK.Chunk14012
import ArealUK.Chunk14013
import ArealUK.Chunk14014
import ArealUK.Chunk14015
import ArealUK.Chunk14016
import ArealUK.Chunk14017
import ArealUK.Chunk14018
import ArealUK.Chunk14019
import ArealUK.Chunk14020
import ArealUK.Chunk14021
import ArealUK.Chunk14022
import ArealUK.Chunk14023
import ArealUK.Chunk14024
import ArealUK.Chunk14025
import ArealUK.Chunk14026
import ArealUK.Chunk14027
import ArealUK.Chunk14028
import ArealUK.Chunk14029
import ArealUK.Chunk14030
import ArealUK.Chunk14031
import ArealUK.Chunk14032
import ArealUK.Chunk14033
import ArealUK.Chunk14034
import ArealUK.Chunk14035
import ArealUK.Chunk14036
import ArealUK.Chunk14037
import ArealUK.Chunk14038
import ArealUK.Chunk14039
import ArealUK.Chunk14040
import ArealUK.Chunk14041
import ArealUK.Chunk14042
import ArealUK.Chunk14043
import ArealUK.Chunk14044
import ArealUK.Chunk14045
import ArealUK.Chunk14046
import ArealUK.Chunk14047
import ArealUK.Chunk14048
import ArealUK.Chunk14049
import ArealUK.Chunk14050
import ArealUK.Chunk14051
import ArealUK.Chunk14052
import ArealUK.Chunk14053
import ArealUK.Chunk14054
import ArealUK.Chunk14055
import ArealUK.Chunk14056
import ArealUK.Chunk14057
import ArealUK.Chunk14058
import ArealUK.Chunk14059
import ArealUK.Chunk14060
import ArealUK.Chunk14061
import ArealUK.Chunk14062
import ArealUK.Chunk14063
import ArealUK.Chunk14064
import ArealUK.Chunk14065
import ArealUK.Chunk14066
import ArealUK.Chunk14067
import ArealUK.Chunk14068
import ArealUK.Chunk14069
import ArealUK.Chunk14070
import ArealUK.Chunk14071
import ArealUK.Chunk14072
import ArealUK.Chunk14073
import ArealUK.Chunk14074
import ArealUK.Chunk14075
import ArealUK.Chunk14076
import ArealUK.Chunk14077
import ArealUK.Chunk14078
import ArealUK.Chunk14079
import ArealUK.Chunk14080
import ArealUK.Chunk14081
import ArealUK.Chunk14082
import ArealUK.Chunk14083
import ArealUK.Chunk14084
import ArealUK.Chunk14085
import ArealUK.Chunk14086
import ArealUK.Chunk14087
import ArealUK.Chunk14088
import ArealUK.Chunk14089
import ArealUK.Chunk14090
import ArealUK.Chunk14091
import ArealUK.Chunk14092
import ArealUK.Chunk14093
import ArealUK.Chunk14094
import ArealUK.Chunk14095
import ArealUK.Chunk14096
import ArealUK.Chunk14097
import ArealUK.Chunk14098
import ArealUK.Chunk14099
import Areal.UCert.LeavesKGen

/-! Group 140 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_140 : leavesOK ctxLitU 575300000000 2 ((leaves.drop 28000).take 200) 290050000000 1 = true := by
  have s99 := ArealUCore.ArealUK.chunk_14099
  have s98 : leavesOK ctxLitU 290000000000 1 ((leaves.drop 28196).take 4) 290050000000 1 = true :=
    take_step (n := 2) (t := 4) (b := 28198) rfl rfl ArealUCore.ArealUK.chunk_14098 s99
  have s97 : leavesOK ctxLitU 289975000000 1 ((leaves.drop 28194).take 6) 290050000000 1 = true :=
    take_step (n := 2) (t := 6) (b := 28196) rfl rfl ArealUCore.ArealUK.chunk_14097 s98
  have s96 : leavesOK ctxLitU 289950000000 1 ((leaves.drop 28192).take 8) 290050000000 1 = true :=
    take_step (n := 2) (t := 8) (b := 28194) rfl rfl ArealUCore.ArealUK.chunk_14096 s97
  have s95 : leavesOK ctxLitU 289937500000 1 ((leaves.drop 28190).take 10) 290050000000 1 = true :=
    take_step (n := 2) (t := 10) (b := 28192) rfl rfl ArealUCore.ArealUK.chunk_14095 s96
  have s94 : leavesOK ctxLitU 289925000000 1 ((leaves.drop 28188).take 12) 290050000000 1 = true :=
    take_step (n := 2) (t := 12) (b := 28190) rfl rfl ArealUCore.ArealUK.chunk_14094 s95
  have s93 : leavesOK ctxLitU 144950000000 0 ((leaves.drop 28186).take 14) 290050000000 1 = true :=
    take_step (n := 2) (t := 14) (b := 28188) rfl rfl ArealUCore.ArealUK.chunk_14093 s94
  have s92 : leavesOK ctxLitU 144937500000 0 ((leaves.drop 28184).take 16) 290050000000 1 = true :=
    take_step (n := 2) (t := 16) (b := 28186) rfl rfl ArealUCore.ArealUK.chunk_14092 s93
  have s91 : leavesOK ctxLitU 144925000000 0 ((leaves.drop 28182).take 18) 290050000000 1 = true :=
    take_step (n := 2) (t := 18) (b := 28184) rfl rfl ArealUCore.ArealUK.chunk_14091 s92
  have s90 : leavesOK ctxLitU 289825000000 1 ((leaves.drop 28180).take 20) 290050000000 1 = true :=
    take_step (n := 2) (t := 20) (b := 28182) rfl rfl ArealUCore.ArealUK.chunk_14090 s91
  have s89 : leavesOK ctxLitU 289800000000 1 ((leaves.drop 28178).take 22) 290050000000 1 = true :=
    take_step (n := 2) (t := 22) (b := 28180) rfl rfl ArealUCore.ArealUK.chunk_14089 s90
  have s88 : leavesOK ctxLitU 289775000000 1 ((leaves.drop 28176).take 24) 290050000000 1 = true :=
    take_step (n := 2) (t := 24) (b := 28178) rfl rfl ArealUCore.ArealUK.chunk_14088 s89
  have s87 : leavesOK ctxLitU 289750000000 1 ((leaves.drop 28174).take 26) 290050000000 1 = true :=
    take_step (n := 2) (t := 26) (b := 28176) rfl rfl ArealUCore.ArealUK.chunk_14087 s88
  have s86 : leavesOK ctxLitU 144862500000 0 ((leaves.drop 28172).take 28) 290050000000 1 = true :=
    take_step (n := 2) (t := 28) (b := 28174) rfl rfl ArealUCore.ArealUK.chunk_14086 s87
  have s85 : leavesOK ctxLitU 144850000000 0 ((leaves.drop 28170).take 30) 290050000000 1 = true :=
    take_step (n := 2) (t := 30) (b := 28172) rfl rfl ArealUCore.ArealUK.chunk_14085 s86
  have s84 : leavesOK ctxLitU 144837500000 0 ((leaves.drop 28168).take 32) 290050000000 1 = true :=
    take_step (n := 2) (t := 32) (b := 28170) rfl rfl ArealUCore.ArealUK.chunk_14084 s85
  have s83 : leavesOK ctxLitU 289656250000 1 ((leaves.drop 28166).take 34) 290050000000 1 = true :=
    take_step (n := 2) (t := 34) (b := 28168) rfl rfl ArealUCore.ArealUK.chunk_14083 s84
  have s82 : leavesOK ctxLitU 289637500000 1 ((leaves.drop 28164).take 36) 290050000000 1 = true :=
    take_step (n := 2) (t := 36) (b := 28166) rfl rfl ArealUCore.ArealUK.chunk_14082 s83
  have s81 : leavesOK ctxLitU 289612500000 1 ((leaves.drop 28162).take 38) 290050000000 1 = true :=
    take_step (n := 2) (t := 38) (b := 28164) rfl rfl ArealUCore.ArealUK.chunk_14081 s82
  have s80 : leavesOK ctxLitU 289587500000 1 ((leaves.drop 28160).take 40) 290050000000 1 = true :=
    take_step (n := 2) (t := 40) (b := 28162) rfl rfl ArealUCore.ArealUK.chunk_14080 s81
  have s79 : leavesOK ctxLitU 289562500000 1 ((leaves.drop 28158).take 42) 290050000000 1 = true :=
    take_step (n := 2) (t := 42) (b := 28160) rfl rfl ArealUCore.ArealUK.chunk_14079 s80
  have s78 : leavesOK ctxLitU 289543750000 1 ((leaves.drop 28156).take 44) 290050000000 1 = true :=
    take_step (n := 2) (t := 44) (b := 28158) rfl rfl ArealUCore.ArealUK.chunk_14078 s79
  have s77 : leavesOK ctxLitU 289531250000 1 ((leaves.drop 28154).take 46) 290050000000 1 = true :=
    take_step (n := 2) (t := 46) (b := 28156) rfl rfl ArealUCore.ArealUK.chunk_14077 s78
  have s76 : leavesOK ctxLitU 144756250000 0 ((leaves.drop 28152).take 48) 290050000000 1 = true :=
    take_step (n := 2) (t := 48) (b := 28154) rfl rfl ArealUCore.ArealUK.chunk_14076 s77
  have s75 : leavesOK ctxLitU 289487500000 1 ((leaves.drop 28150).take 50) 290050000000 1 = true :=
    take_step (n := 2) (t := 50) (b := 28152) rfl rfl ArealUCore.ArealUK.chunk_14075 s76
  have s74 : leavesOK ctxLitU 289462500000 1 ((leaves.drop 28148).take 52) 290050000000 1 = true :=
    take_step (n := 2) (t := 52) (b := 28150) rfl rfl ArealUCore.ArealUK.chunk_14074 s75
  have s73 : leavesOK ctxLitU 578875000000 2 ((leaves.drop 28146).take 54) 290050000000 1 = true :=
    take_step (n := 2) (t := 54) (b := 28148) rfl rfl ArealUCore.ArealUK.chunk_14073 s74
  have s72 : leavesOK ctxLitU 578825000000 2 ((leaves.drop 28144).take 56) 290050000000 1 = true :=
    take_step (n := 2) (t := 56) (b := 28146) rfl rfl ArealUCore.ArealUK.chunk_14072 s73
  have s71 : leavesOK ctxLitU 289387500000 1 ((leaves.drop 28142).take 58) 290050000000 1 = true :=
    take_step (n := 2) (t := 58) (b := 28144) rfl rfl ArealUCore.ArealUK.chunk_14071 s72
  have s70 : leavesOK ctxLitU 289362500000 1 ((leaves.drop 28140).take 60) 290050000000 1 = true :=
    take_step (n := 2) (t := 60) (b := 28142) rfl rfl ArealUCore.ArealUK.chunk_14070 s71
  have s69 : leavesOK ctxLitU 144668750000 0 ((leaves.drop 28138).take 62) 290050000000 1 = true :=
    take_step (n := 2) (t := 62) (b := 28140) rfl rfl ArealUCore.ArealUK.chunk_14069 s70
  have s68 : leavesOK ctxLitU 144656250000 0 ((leaves.drop 28136).take 64) 290050000000 1 = true :=
    take_step (n := 2) (t := 64) (b := 28138) rfl rfl ArealUCore.ArealUK.chunk_14068 s69
  have s67 : leavesOK ctxLitU 144643750000 0 ((leaves.drop 28134).take 66) 290050000000 1 = true :=
    take_step (n := 2) (t := 66) (b := 28136) rfl rfl ArealUCore.ArealUK.chunk_14067 s68
  have s66 : leavesOK ctxLitU 289268750000 1 ((leaves.drop 28132).take 68) 290050000000 1 = true :=
    take_step (n := 2) (t := 68) (b := 28134) rfl rfl ArealUCore.ArealUK.chunk_14066 s67
  have s65 : leavesOK ctxLitU 289256250000 1 ((leaves.drop 28130).take 70) 290050000000 1 = true :=
    take_step (n := 2) (t := 70) (b := 28132) rfl rfl ArealUCore.ArealUK.chunk_14065 s66
  have s64 : leavesOK ctxLitU 289237500000 1 ((leaves.drop 28128).take 72) 290050000000 1 = true :=
    take_step (n := 2) (t := 72) (b := 28130) rfl rfl ArealUCore.ArealUK.chunk_14064 s65
  have s63 : leavesOK ctxLitU 289212500000 1 ((leaves.drop 28126).take 74) 290050000000 1 = true :=
    take_step (n := 2) (t := 74) (b := 28128) rfl rfl ArealUCore.ArealUK.chunk_14063 s64
  have s62 : leavesOK ctxLitU 578375000000 2 ((leaves.drop 28124).take 76) 290050000000 1 = true :=
    take_step (n := 2) (t := 76) (b := 28126) rfl rfl ArealUCore.ArealUK.chunk_14062 s63
  have s61 : leavesOK ctxLitU 578325000000 2 ((leaves.drop 28122).take 78) 290050000000 1 = true :=
    take_step (n := 2) (t := 78) (b := 28124) rfl rfl ArealUCore.ArealUK.chunk_14061 s62
  have s60 : leavesOK ctxLitU 578275000000 2 ((leaves.drop 28120).take 80) 290050000000 1 = true :=
    take_step (n := 2) (t := 80) (b := 28122) rfl rfl ArealUCore.ArealUK.chunk_14060 s61
  have s59 : leavesOK ctxLitU 289100000000 1 ((leaves.drop 28118).take 82) 290050000000 1 = true :=
    take_step (n := 2) (t := 82) (b := 28120) rfl rfl ArealUCore.ArealUK.chunk_14059 s60
  have s58 : leavesOK ctxLitU 578125000000 2 ((leaves.drop 28116).take 84) 290050000000 1 = true :=
    take_step (n := 2) (t := 84) (b := 28118) rfl rfl ArealUCore.ArealUK.chunk_14058 s59
  have s57 : leavesOK ctxLitU 578075000000 2 ((leaves.drop 28114).take 86) 290050000000 1 = true :=
    take_step (n := 2) (t := 86) (b := 28116) rfl rfl ArealUCore.ArealUK.chunk_14057 s58
  have s56 : leavesOK ctxLitU 578025000000 2 ((leaves.drop 28112).take 88) 290050000000 1 = true :=
    take_step (n := 2) (t := 88) (b := 28114) rfl rfl ArealUCore.ArealUK.chunk_14056 s57
  have s55 : leavesOK ctxLitU 577975000000 2 ((leaves.drop 28110).take 90) 290050000000 1 = true :=
    take_step (n := 2) (t := 90) (b := 28112) rfl rfl ArealUCore.ArealUK.chunk_14055 s56
  have s54 : leavesOK ctxLitU 577925000000 2 ((leaves.drop 28108).take 92) 290050000000 1 = true :=
    take_step (n := 2) (t := 92) (b := 28110) rfl rfl ArealUCore.ArealUK.chunk_14054 s55
  have s53 : leavesOK ctxLitU 577875000000 2 ((leaves.drop 28106).take 94) 290050000000 1 = true :=
    take_step (n := 2) (t := 94) (b := 28108) rfl rfl ArealUCore.ArealUK.chunk_14053 s54
  have s52 : leavesOK ctxLitU 577825000000 2 ((leaves.drop 28104).take 96) 290050000000 1 = true :=
    take_step (n := 2) (t := 96) (b := 28106) rfl rfl ArealUCore.ArealUK.chunk_14052 s53
  have s51 : leavesOK ctxLitU 577775000000 2 ((leaves.drop 28102).take 98) 290050000000 1 = true :=
    take_step (n := 2) (t := 98) (b := 28104) rfl rfl ArealUCore.ArealUK.chunk_14051 s52
  have s50 : leavesOK ctxLitU 577725000000 2 ((leaves.drop 28100).take 100) 290050000000 1 = true :=
    take_step (n := 2) (t := 100) (b := 28102) rfl rfl ArealUCore.ArealUK.chunk_14050 s51
  have s49 : leavesOK ctxLitU 577675000000 2 ((leaves.drop 28098).take 102) 290050000000 1 = true :=
    take_step (n := 2) (t := 102) (b := 28100) rfl rfl ArealUCore.ArealUK.chunk_14049 s50
  have s48 : leavesOK ctxLitU 577625000000 2 ((leaves.drop 28096).take 104) 290050000000 1 = true :=
    take_step (n := 2) (t := 104) (b := 28098) rfl rfl ArealUCore.ArealUK.chunk_14048 s49
  have s47 : leavesOK ctxLitU 288787500000 1 ((leaves.drop 28094).take 106) 290050000000 1 = true :=
    take_step (n := 2) (t := 106) (b := 28096) rfl rfl ArealUCore.ArealUK.chunk_14047 s48
  have s46 : leavesOK ctxLitU 288762500000 1 ((leaves.drop 28092).take 108) 290050000000 1 = true :=
    take_step (n := 2) (t := 108) (b := 28094) rfl rfl ArealUCore.ArealUK.chunk_14046 s47
  have s45 : leavesOK ctxLitU 144368750000 0 ((leaves.drop 28090).take 110) 290050000000 1 = true :=
    take_step (n := 2) (t := 110) (b := 28092) rfl rfl ArealUCore.ArealUK.chunk_14045 s46
  have s44 : leavesOK ctxLitU 144356250000 0 ((leaves.drop 28088).take 112) 290050000000 1 = true :=
    take_step (n := 2) (t := 112) (b := 28090) rfl rfl ArealUCore.ArealUK.chunk_14044 s45
  have s43 : leavesOK ctxLitU 144343750000 0 ((leaves.drop 28086).take 114) 290050000000 1 = true :=
    take_step (n := 2) (t := 114) (b := 28088) rfl rfl ArealUCore.ArealUK.chunk_14043 s44
  have s42 : leavesOK ctxLitU 144331250000 0 ((leaves.drop 28084).take 116) 290050000000 1 = true :=
    take_step (n := 2) (t := 116) (b := 28086) rfl rfl ArealUCore.ArealUK.chunk_14042 s43
  have s41 : leavesOK ctxLitU 288637500000 1 ((leaves.drop 28082).take 118) 290050000000 1 = true :=
    take_step (n := 2) (t := 118) (b := 28084) rfl rfl ArealUCore.ArealUK.chunk_14041 s42
  have s40 : leavesOK ctxLitU 288612500000 1 ((leaves.drop 28080).take 120) 290050000000 1 = true :=
    take_step (n := 2) (t := 120) (b := 28082) rfl rfl ArealUCore.ArealUK.chunk_14040 s41
  have s39 : leavesOK ctxLitU 577175000000 2 ((leaves.drop 28078).take 122) 290050000000 1 = true :=
    take_step (n := 2) (t := 122) (b := 28080) rfl rfl ArealUCore.ArealUK.chunk_14039 s40
  have s38 : leavesOK ctxLitU 577125000000 2 ((leaves.drop 28076).take 124) 290050000000 1 = true :=
    take_step (n := 2) (t := 124) (b := 28078) rfl rfl ArealUCore.ArealUK.chunk_14038 s39
  have s37 : leavesOK ctxLitU 288537500000 1 ((leaves.drop 28074).take 126) 290050000000 1 = true :=
    take_step (n := 2) (t := 126) (b := 28076) rfl rfl ArealUCore.ArealUK.chunk_14037 s38
  have s36 : leavesOK ctxLitU 288512500000 1 ((leaves.drop 28072).take 128) 290050000000 1 = true :=
    take_step (n := 2) (t := 128) (b := 28074) rfl rfl ArealUCore.ArealUK.chunk_14036 s37
  have s35 : leavesOK ctxLitU 144243750000 0 ((leaves.drop 28070).take 130) 290050000000 1 = true :=
    take_step (n := 2) (t := 130) (b := 28072) rfl rfl ArealUCore.ArealUK.chunk_14035 s36
  have s34 : leavesOK ctxLitU 288468750000 1 ((leaves.drop 28068).take 132) 290050000000 1 = true :=
    take_step (n := 2) (t := 132) (b := 28070) rfl rfl ArealUCore.ArealUK.chunk_14034 s35
  have s33 : leavesOK ctxLitU 288456250000 1 ((leaves.drop 28066).take 134) 290050000000 1 = true :=
    take_step (n := 2) (t := 134) (b := 28068) rfl rfl ArealUCore.ArealUK.chunk_14033 s34
  have s32 : leavesOK ctxLitU 288437500000 1 ((leaves.drop 28064).take 136) 290050000000 1 = true :=
    take_step (n := 2) (t := 136) (b := 28066) rfl rfl ArealUCore.ArealUK.chunk_14032 s33
  have s31 : leavesOK ctxLitU 288412500000 1 ((leaves.drop 28062).take 138) 290050000000 1 = true :=
    take_step (n := 2) (t := 138) (b := 28064) rfl rfl ArealUCore.ArealUK.chunk_14031 s32
  have s30 : leavesOK ctxLitU 288387500000 1 ((leaves.drop 28060).take 140) 290050000000 1 = true :=
    take_step (n := 2) (t := 140) (b := 28062) rfl rfl ArealUCore.ArealUK.chunk_14030 s31
  have s29 : leavesOK ctxLitU 288362500000 1 ((leaves.drop 28058).take 142) 290050000000 1 = true :=
    take_step (n := 2) (t := 142) (b := 28060) rfl rfl ArealUCore.ArealUK.chunk_14029 s30
  have s28 : leavesOK ctxLitU 288343750000 1 ((leaves.drop 28056).take 144) 290050000000 1 = true :=
    take_step (n := 2) (t := 144) (b := 28058) rfl rfl ArealUCore.ArealUK.chunk_14028 s29
  have s27 : leavesOK ctxLitU 288331250000 1 ((leaves.drop 28054).take 146) 290050000000 1 = true :=
    take_step (n := 2) (t := 146) (b := 28056) rfl rfl ArealUCore.ArealUK.chunk_14027 s28
  have s26 : leavesOK ctxLitU 144156250000 0 ((leaves.drop 28052).take 148) 290050000000 1 = true :=
    take_step (n := 2) (t := 148) (b := 28054) rfl rfl ArealUCore.ArealUK.chunk_14026 s27
  have s25 : leavesOK ctxLitU 144143750000 0 ((leaves.drop 28050).take 150) 290050000000 1 = true :=
    take_step (n := 2) (t := 150) (b := 28052) rfl rfl ArealUCore.ArealUK.chunk_14025 s26
  have s24 : leavesOK ctxLitU 144131250000 0 ((leaves.drop 28048).take 152) 290050000000 1 = true :=
    take_step (n := 2) (t := 152) (b := 28050) rfl rfl ArealUCore.ArealUK.chunk_14024 s25
  have s23 : leavesOK ctxLitU 288237500000 1 ((leaves.drop 28046).take 154) 290050000000 1 = true :=
    take_step (n := 2) (t := 154) (b := 28048) rfl rfl ArealUCore.ArealUK.chunk_14023 s24
  have s22 : leavesOK ctxLitU 288212500000 1 ((leaves.drop 28044).take 156) 290050000000 1 = true :=
    take_step (n := 2) (t := 156) (b := 28046) rfl rfl ArealUCore.ArealUK.chunk_14022 s23
  have s21 : leavesOK ctxLitU 288187500000 1 ((leaves.drop 28042).take 158) 290050000000 1 = true :=
    take_step (n := 2) (t := 158) (b := 28044) rfl rfl ArealUCore.ArealUK.chunk_14021 s22
  have s20 : leavesOK ctxLitU 288162500000 1 ((leaves.drop 28040).take 160) 290050000000 1 = true :=
    take_step (n := 2) (t := 160) (b := 28042) rfl rfl ArealUCore.ArealUK.chunk_14020 s21
  have s19 : leavesOK ctxLitU 144068750000 0 ((leaves.drop 28038).take 162) 290050000000 1 = true :=
    take_step (n := 2) (t := 162) (b := 28040) rfl rfl ArealUCore.ArealUK.chunk_14019 s20
  have s18 : leavesOK ctxLitU 144056250000 0 ((leaves.drop 28036).take 164) 290050000000 1 = true :=
    take_step (n := 2) (t := 164) (b := 28038) rfl rfl ArealUCore.ArealUK.chunk_14018 s19
  have s17 : leavesOK ctxLitU 144043750000 0 ((leaves.drop 28034).take 166) 290050000000 1 = true :=
    take_step (n := 2) (t := 166) (b := 28036) rfl rfl ArealUCore.ArealUK.chunk_14017 s18
  have s16 : leavesOK ctxLitU 144031250000 0 ((leaves.drop 28032).take 168) 290050000000 1 = true :=
    take_step (n := 2) (t := 168) (b := 28034) rfl rfl ArealUCore.ArealUK.chunk_14016 s17
  have s15 : leavesOK ctxLitU 288037500000 1 ((leaves.drop 28030).take 170) 290050000000 1 = true :=
    take_step (n := 2) (t := 170) (b := 28032) rfl rfl ArealUCore.ArealUK.chunk_14015 s16
  have s14 : leavesOK ctxLitU 288012500000 1 ((leaves.drop 28028).take 172) 290050000000 1 = true :=
    take_step (n := 2) (t := 172) (b := 28030) rfl rfl ArealUCore.ArealUK.chunk_14014 s15
  have s13 : leavesOK ctxLitU 575975000000 2 ((leaves.drop 28026).take 174) 290050000000 1 = true :=
    take_step (n := 2) (t := 174) (b := 28028) rfl rfl ArealUCore.ArealUK.chunk_14013 s14
  have s12 : leavesOK ctxLitU 575925000000 2 ((leaves.drop 28024).take 176) 290050000000 1 = true :=
    take_step (n := 2) (t := 176) (b := 28026) rfl rfl ArealUCore.ArealUK.chunk_14012 s13
  have s11 : leavesOK ctxLitU 575875000000 2 ((leaves.drop 28022).take 178) 290050000000 1 = true :=
    take_step (n := 2) (t := 178) (b := 28024) rfl rfl ArealUCore.ArealUK.chunk_14011 s12
  have s10 : leavesOK ctxLitU 575825000000 2 ((leaves.drop 28020).take 180) 290050000000 1 = true :=
    take_step (n := 2) (t := 180) (b := 28022) rfl rfl ArealUCore.ArealUK.chunk_14010 s11
  have s9 : leavesOK ctxLitU 287875000000 1 ((leaves.drop 28018).take 182) 290050000000 1 = true :=
    take_step (n := 2) (t := 182) (b := 28020) rfl rfl ArealUCore.ArealUK.chunk_14009 s10
  have s8 : leavesOK ctxLitU 575700000000 2 ((leaves.drop 28016).take 184) 290050000000 1 = true :=
    take_step (n := 2) (t := 184) (b := 28018) rfl rfl ArealUCore.ArealUK.chunk_14008 s9
  have s7 : leavesOK ctxLitU 575650000000 2 ((leaves.drop 28014).take 186) 290050000000 1 = true :=
    take_step (n := 2) (t := 186) (b := 28016) rfl rfl ArealUCore.ArealUK.chunk_14007 s8
  have s6 : leavesOK ctxLitU 575600000000 2 ((leaves.drop 28012).take 188) 290050000000 1 = true :=
    take_step (n := 2) (t := 188) (b := 28014) rfl rfl ArealUCore.ArealUK.chunk_14006 s7
  have s5 : leavesOK ctxLitU 575550000000 2 ((leaves.drop 28010).take 190) 290050000000 1 = true :=
    take_step (n := 2) (t := 190) (b := 28012) rfl rfl ArealUCore.ArealUK.chunk_14005 s6
  have s4 : leavesOK ctxLitU 575500000000 2 ((leaves.drop 28008).take 192) 290050000000 1 = true :=
    take_step (n := 2) (t := 192) (b := 28010) rfl rfl ArealUCore.ArealUK.chunk_14004 s5
  have s3 : leavesOK ctxLitU 575450000000 2 ((leaves.drop 28006).take 194) 290050000000 1 = true :=
    take_step (n := 2) (t := 194) (b := 28008) rfl rfl ArealUCore.ArealUK.chunk_14003 s4
  have s2 : leavesOK ctxLitU 575400000000 2 ((leaves.drop 28004).take 196) 290050000000 1 = true :=
    take_step (n := 2) (t := 196) (b := 28006) rfl rfl ArealUCore.ArealUK.chunk_14002 s3
  have s1 : leavesOK ctxLitU 575350000000 2 ((leaves.drop 28002).take 198) 290050000000 1 = true :=
    take_step (n := 2) (t := 198) (b := 28004) rfl rfl ArealUCore.ArealUK.chunk_14001 s2
  have s0 : leavesOK ctxLitU 575300000000 2 ((leaves.drop 28000).take 200) 290050000000 1 = true :=
    take_step (n := 2) (t := 200) (b := 28002) rfl rfl ArealUCore.ArealUK.chunk_14000 s1
  exact s0

end Areal.UCert

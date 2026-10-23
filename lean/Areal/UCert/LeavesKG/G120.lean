import ArealUK.Chunk12000
import ArealUK.Chunk12001
import ArealUK.Chunk12002
import ArealUK.Chunk12003
import ArealUK.Chunk12004
import ArealUK.Chunk12005
import ArealUK.Chunk12006
import ArealUK.Chunk12007
import ArealUK.Chunk12008
import ArealUK.Chunk12009
import ArealUK.Chunk12010
import ArealUK.Chunk12011
import ArealUK.Chunk12012
import ArealUK.Chunk12013
import ArealUK.Chunk12014
import ArealUK.Chunk12015
import ArealUK.Chunk12016
import ArealUK.Chunk12017
import ArealUK.Chunk12018
import ArealUK.Chunk12019
import ArealUK.Chunk12020
import ArealUK.Chunk12021
import ArealUK.Chunk12022
import ArealUK.Chunk12023
import ArealUK.Chunk12024
import ArealUK.Chunk12025
import ArealUK.Chunk12026
import ArealUK.Chunk12027
import ArealUK.Chunk12028
import ArealUK.Chunk12029
import ArealUK.Chunk12030
import ArealUK.Chunk12031
import ArealUK.Chunk12032
import ArealUK.Chunk12033
import ArealUK.Chunk12034
import ArealUK.Chunk12035
import ArealUK.Chunk12036
import ArealUK.Chunk12037
import ArealUK.Chunk12038
import ArealUK.Chunk12039
import ArealUK.Chunk12040
import ArealUK.Chunk12041
import ArealUK.Chunk12042
import ArealUK.Chunk12043
import ArealUK.Chunk12044
import ArealUK.Chunk12045
import ArealUK.Chunk12046
import ArealUK.Chunk12047
import ArealUK.Chunk12048
import ArealUK.Chunk12049
import ArealUK.Chunk12050
import ArealUK.Chunk12051
import ArealUK.Chunk12052
import ArealUK.Chunk12053
import ArealUK.Chunk12054
import ArealUK.Chunk12055
import ArealUK.Chunk12056
import ArealUK.Chunk12057
import ArealUK.Chunk12058
import ArealUK.Chunk12059
import ArealUK.Chunk12060
import ArealUK.Chunk12061
import ArealUK.Chunk12062
import ArealUK.Chunk12063
import ArealUK.Chunk12064
import ArealUK.Chunk12065
import ArealUK.Chunk12066
import ArealUK.Chunk12067
import ArealUK.Chunk12068
import ArealUK.Chunk12069
import ArealUK.Chunk12070
import ArealUK.Chunk12071
import ArealUK.Chunk12072
import ArealUK.Chunk12073
import ArealUK.Chunk12074
import ArealUK.Chunk12075
import ArealUK.Chunk12076
import ArealUK.Chunk12077
import ArealUK.Chunk12078
import ArealUK.Chunk12079
import ArealUK.Chunk12080
import ArealUK.Chunk12081
import ArealUK.Chunk12082
import ArealUK.Chunk12083
import ArealUK.Chunk12084
import ArealUK.Chunk12085
import ArealUK.Chunk12086
import ArealUK.Chunk12087
import ArealUK.Chunk12088
import ArealUK.Chunk12089
import ArealUK.Chunk12090
import ArealUK.Chunk12091
import ArealUK.Chunk12092
import ArealUK.Chunk12093
import ArealUK.Chunk12094
import ArealUK.Chunk12095
import ArealUK.Chunk12096
import ArealUK.Chunk12097
import ArealUK.Chunk12098
import ArealUK.Chunk12099
import Areal.UCert.LeavesKGen

/-! Group 120 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_120 : leavesOK ctxLitU 476750000000 2 ((leaves.drop 24000).take 200) 481750000000 2 = true := by
  have s99 := ArealUCore.ArealUK.chunk_12099
  have s98 : leavesOK ctxLitU 481650000000 2 ((leaves.drop 24196).take 4) 481750000000 2 = true :=
    take_step (n := 2) (t := 4) (b := 24198) rfl rfl ArealUCore.ArealUK.chunk_12098 s99
  have s97 : leavesOK ctxLitU 481600000000 2 ((leaves.drop 24194).take 6) 481750000000 2 = true :=
    take_step (n := 2) (t := 6) (b := 24196) rfl rfl ArealUCore.ArealUK.chunk_12097 s98
  have s96 : leavesOK ctxLitU 481550000000 2 ((leaves.drop 24192).take 8) 481750000000 2 = true :=
    take_step (n := 2) (t := 8) (b := 24194) rfl rfl ArealUCore.ArealUK.chunk_12096 s97
  have s95 : leavesOK ctxLitU 481500000000 2 ((leaves.drop 24190).take 10) 481750000000 2 = true :=
    take_step (n := 2) (t := 10) (b := 24192) rfl rfl ArealUCore.ArealUK.chunk_12095 s96
  have s94 : leavesOK ctxLitU 481450000000 2 ((leaves.drop 24188).take 12) 481750000000 2 = true :=
    take_step (n := 2) (t := 12) (b := 24190) rfl rfl ArealUCore.ArealUK.chunk_12094 s95
  have s93 : leavesOK ctxLitU 481400000000 2 ((leaves.drop 24186).take 14) 481750000000 2 = true :=
    take_step (n := 2) (t := 14) (b := 24188) rfl rfl ArealUCore.ArealUK.chunk_12093 s94
  have s92 : leavesOK ctxLitU 481350000000 2 ((leaves.drop 24184).take 16) 481750000000 2 = true :=
    take_step (n := 2) (t := 16) (b := 24186) rfl rfl ArealUCore.ArealUK.chunk_12092 s93
  have s91 : leavesOK ctxLitU 481300000000 2 ((leaves.drop 24182).take 18) 481750000000 2 = true :=
    take_step (n := 2) (t := 18) (b := 24184) rfl rfl ArealUCore.ArealUK.chunk_12091 s92
  have s90 : leavesOK ctxLitU 481250000000 2 ((leaves.drop 24180).take 20) 481750000000 2 = true :=
    take_step (n := 2) (t := 20) (b := 24182) rfl rfl ArealUCore.ArealUK.chunk_12090 s91
  have s89 : leavesOK ctxLitU 481200000000 2 ((leaves.drop 24178).take 22) 481750000000 2 = true :=
    take_step (n := 2) (t := 22) (b := 24180) rfl rfl ArealUCore.ArealUK.chunk_12089 s90
  have s88 : leavesOK ctxLitU 481150000000 2 ((leaves.drop 24176).take 24) 481750000000 2 = true :=
    take_step (n := 2) (t := 24) (b := 24178) rfl rfl ArealUCore.ArealUK.chunk_12088 s89
  have s87 : leavesOK ctxLitU 481100000000 2 ((leaves.drop 24174).take 26) 481750000000 2 = true :=
    take_step (n := 2) (t := 26) (b := 24176) rfl rfl ArealUCore.ArealUK.chunk_12087 s88
  have s86 : leavesOK ctxLitU 481050000000 2 ((leaves.drop 24172).take 28) 481750000000 2 = true :=
    take_step (n := 2) (t := 28) (b := 24174) rfl rfl ArealUCore.ArealUK.chunk_12086 s87
  have s85 : leavesOK ctxLitU 481000000000 2 ((leaves.drop 24170).take 30) 481750000000 2 = true :=
    take_step (n := 2) (t := 30) (b := 24172) rfl rfl ArealUCore.ArealUK.chunk_12085 s86
  have s84 : leavesOK ctxLitU 480950000000 2 ((leaves.drop 24168).take 32) 481750000000 2 = true :=
    take_step (n := 2) (t := 32) (b := 24170) rfl rfl ArealUCore.ArealUK.chunk_12084 s85
  have s83 : leavesOK ctxLitU 480900000000 2 ((leaves.drop 24166).take 34) 481750000000 2 = true :=
    take_step (n := 2) (t := 34) (b := 24168) rfl rfl ArealUCore.ArealUK.chunk_12083 s84
  have s82 : leavesOK ctxLitU 480850000000 2 ((leaves.drop 24164).take 36) 481750000000 2 = true :=
    take_step (n := 2) (t := 36) (b := 24166) rfl rfl ArealUCore.ArealUK.chunk_12082 s83
  have s81 : leavesOK ctxLitU 480800000000 2 ((leaves.drop 24162).take 38) 481750000000 2 = true :=
    take_step (n := 2) (t := 38) (b := 24164) rfl rfl ArealUCore.ArealUK.chunk_12081 s82
  have s80 : leavesOK ctxLitU 480750000000 2 ((leaves.drop 24160).take 40) 481750000000 2 = true :=
    take_step (n := 2) (t := 40) (b := 24162) rfl rfl ArealUCore.ArealUK.chunk_12080 s81
  have s79 : leavesOK ctxLitU 480700000000 2 ((leaves.drop 24158).take 42) 481750000000 2 = true :=
    take_step (n := 2) (t := 42) (b := 24160) rfl rfl ArealUCore.ArealUK.chunk_12079 s80
  have s78 : leavesOK ctxLitU 480650000000 2 ((leaves.drop 24156).take 44) 481750000000 2 = true :=
    take_step (n := 2) (t := 44) (b := 24158) rfl rfl ArealUCore.ArealUK.chunk_12078 s79
  have s77 : leavesOK ctxLitU 480600000000 2 ((leaves.drop 24154).take 46) 481750000000 2 = true :=
    take_step (n := 2) (t := 46) (b := 24156) rfl rfl ArealUCore.ArealUK.chunk_12077 s78
  have s76 : leavesOK ctxLitU 480550000000 2 ((leaves.drop 24152).take 48) 481750000000 2 = true :=
    take_step (n := 2) (t := 48) (b := 24154) rfl rfl ArealUCore.ArealUK.chunk_12076 s77
  have s75 : leavesOK ctxLitU 480500000000 2 ((leaves.drop 24150).take 50) 481750000000 2 = true :=
    take_step (n := 2) (t := 50) (b := 24152) rfl rfl ArealUCore.ArealUK.chunk_12075 s76
  have s74 : leavesOK ctxLitU 480450000000 2 ((leaves.drop 24148).take 52) 481750000000 2 = true :=
    take_step (n := 2) (t := 52) (b := 24150) rfl rfl ArealUCore.ArealUK.chunk_12074 s75
  have s73 : leavesOK ctxLitU 480400000000 2 ((leaves.drop 24146).take 54) 481750000000 2 = true :=
    take_step (n := 2) (t := 54) (b := 24148) rfl rfl ArealUCore.ArealUK.chunk_12073 s74
  have s72 : leavesOK ctxLitU 480350000000 2 ((leaves.drop 24144).take 56) 481750000000 2 = true :=
    take_step (n := 2) (t := 56) (b := 24146) rfl rfl ArealUCore.ArealUK.chunk_12072 s73
  have s71 : leavesOK ctxLitU 480300000000 2 ((leaves.drop 24142).take 58) 481750000000 2 = true :=
    take_step (n := 2) (t := 58) (b := 24144) rfl rfl ArealUCore.ArealUK.chunk_12071 s72
  have s70 : leavesOK ctxLitU 480250000000 2 ((leaves.drop 24140).take 60) 481750000000 2 = true :=
    take_step (n := 2) (t := 60) (b := 24142) rfl rfl ArealUCore.ArealUK.chunk_12070 s71
  have s69 : leavesOK ctxLitU 480200000000 2 ((leaves.drop 24138).take 62) 481750000000 2 = true :=
    take_step (n := 2) (t := 62) (b := 24140) rfl rfl ArealUCore.ArealUK.chunk_12069 s70
  have s68 : leavesOK ctxLitU 480150000000 2 ((leaves.drop 24136).take 64) 481750000000 2 = true :=
    take_step (n := 2) (t := 64) (b := 24138) rfl rfl ArealUCore.ArealUK.chunk_12068 s69
  have s67 : leavesOK ctxLitU 480100000000 2 ((leaves.drop 24134).take 66) 481750000000 2 = true :=
    take_step (n := 2) (t := 66) (b := 24136) rfl rfl ArealUCore.ArealUK.chunk_12067 s68
  have s66 : leavesOK ctxLitU 480050000000 2 ((leaves.drop 24132).take 68) 481750000000 2 = true :=
    take_step (n := 2) (t := 68) (b := 24134) rfl rfl ArealUCore.ArealUK.chunk_12066 s67
  have s65 : leavesOK ctxLitU 480000000000 2 ((leaves.drop 24130).take 70) 481750000000 2 = true :=
    take_step (n := 2) (t := 70) (b := 24132) rfl rfl ArealUCore.ArealUK.chunk_12065 s66
  have s64 : leavesOK ctxLitU 479950000000 2 ((leaves.drop 24128).take 72) 481750000000 2 = true :=
    take_step (n := 2) (t := 72) (b := 24130) rfl rfl ArealUCore.ArealUK.chunk_12064 s65
  have s63 : leavesOK ctxLitU 479900000000 2 ((leaves.drop 24126).take 74) 481750000000 2 = true :=
    take_step (n := 2) (t := 74) (b := 24128) rfl rfl ArealUCore.ArealUK.chunk_12063 s64
  have s62 : leavesOK ctxLitU 479850000000 2 ((leaves.drop 24124).take 76) 481750000000 2 = true :=
    take_step (n := 2) (t := 76) (b := 24126) rfl rfl ArealUCore.ArealUK.chunk_12062 s63
  have s61 : leavesOK ctxLitU 479800000000 2 ((leaves.drop 24122).take 78) 481750000000 2 = true :=
    take_step (n := 2) (t := 78) (b := 24124) rfl rfl ArealUCore.ArealUK.chunk_12061 s62
  have s60 : leavesOK ctxLitU 479750000000 2 ((leaves.drop 24120).take 80) 481750000000 2 = true :=
    take_step (n := 2) (t := 80) (b := 24122) rfl rfl ArealUCore.ArealUK.chunk_12060 s61
  have s59 : leavesOK ctxLitU 479700000000 2 ((leaves.drop 24118).take 82) 481750000000 2 = true :=
    take_step (n := 2) (t := 82) (b := 24120) rfl rfl ArealUCore.ArealUK.chunk_12059 s60
  have s58 : leavesOK ctxLitU 479650000000 2 ((leaves.drop 24116).take 84) 481750000000 2 = true :=
    take_step (n := 2) (t := 84) (b := 24118) rfl rfl ArealUCore.ArealUK.chunk_12058 s59
  have s57 : leavesOK ctxLitU 479600000000 2 ((leaves.drop 24114).take 86) 481750000000 2 = true :=
    take_step (n := 2) (t := 86) (b := 24116) rfl rfl ArealUCore.ArealUK.chunk_12057 s58
  have s56 : leavesOK ctxLitU 479550000000 2 ((leaves.drop 24112).take 88) 481750000000 2 = true :=
    take_step (n := 2) (t := 88) (b := 24114) rfl rfl ArealUCore.ArealUK.chunk_12056 s57
  have s55 : leavesOK ctxLitU 479500000000 2 ((leaves.drop 24110).take 90) 481750000000 2 = true :=
    take_step (n := 2) (t := 90) (b := 24112) rfl rfl ArealUCore.ArealUK.chunk_12055 s56
  have s54 : leavesOK ctxLitU 479450000000 2 ((leaves.drop 24108).take 92) 481750000000 2 = true :=
    take_step (n := 2) (t := 92) (b := 24110) rfl rfl ArealUCore.ArealUK.chunk_12054 s55
  have s53 : leavesOK ctxLitU 479400000000 2 ((leaves.drop 24106).take 94) 481750000000 2 = true :=
    take_step (n := 2) (t := 94) (b := 24108) rfl rfl ArealUCore.ArealUK.chunk_12053 s54
  have s52 : leavesOK ctxLitU 479350000000 2 ((leaves.drop 24104).take 96) 481750000000 2 = true :=
    take_step (n := 2) (t := 96) (b := 24106) rfl rfl ArealUCore.ArealUK.chunk_12052 s53
  have s51 : leavesOK ctxLitU 479300000000 2 ((leaves.drop 24102).take 98) 481750000000 2 = true :=
    take_step (n := 2) (t := 98) (b := 24104) rfl rfl ArealUCore.ArealUK.chunk_12051 s52
  have s50 : leavesOK ctxLitU 479250000000 2 ((leaves.drop 24100).take 100) 481750000000 2 = true :=
    take_step (n := 2) (t := 100) (b := 24102) rfl rfl ArealUCore.ArealUK.chunk_12050 s51
  have s49 : leavesOK ctxLitU 479200000000 2 ((leaves.drop 24098).take 102) 481750000000 2 = true :=
    take_step (n := 2) (t := 102) (b := 24100) rfl rfl ArealUCore.ArealUK.chunk_12049 s50
  have s48 : leavesOK ctxLitU 479150000000 2 ((leaves.drop 24096).take 104) 481750000000 2 = true :=
    take_step (n := 2) (t := 104) (b := 24098) rfl rfl ArealUCore.ArealUK.chunk_12048 s49
  have s47 : leavesOK ctxLitU 479100000000 2 ((leaves.drop 24094).take 106) 481750000000 2 = true :=
    take_step (n := 2) (t := 106) (b := 24096) rfl rfl ArealUCore.ArealUK.chunk_12047 s48
  have s46 : leavesOK ctxLitU 479050000000 2 ((leaves.drop 24092).take 108) 481750000000 2 = true :=
    take_step (n := 2) (t := 108) (b := 24094) rfl rfl ArealUCore.ArealUK.chunk_12046 s47
  have s45 : leavesOK ctxLitU 479000000000 2 ((leaves.drop 24090).take 110) 481750000000 2 = true :=
    take_step (n := 2) (t := 110) (b := 24092) rfl rfl ArealUCore.ArealUK.chunk_12045 s46
  have s44 : leavesOK ctxLitU 478950000000 2 ((leaves.drop 24088).take 112) 481750000000 2 = true :=
    take_step (n := 2) (t := 112) (b := 24090) rfl rfl ArealUCore.ArealUK.chunk_12044 s45
  have s43 : leavesOK ctxLitU 478900000000 2 ((leaves.drop 24086).take 114) 481750000000 2 = true :=
    take_step (n := 2) (t := 114) (b := 24088) rfl rfl ArealUCore.ArealUK.chunk_12043 s44
  have s42 : leavesOK ctxLitU 478850000000 2 ((leaves.drop 24084).take 116) 481750000000 2 = true :=
    take_step (n := 2) (t := 116) (b := 24086) rfl rfl ArealUCore.ArealUK.chunk_12042 s43
  have s41 : leavesOK ctxLitU 478800000000 2 ((leaves.drop 24082).take 118) 481750000000 2 = true :=
    take_step (n := 2) (t := 118) (b := 24084) rfl rfl ArealUCore.ArealUK.chunk_12041 s42
  have s40 : leavesOK ctxLitU 478750000000 2 ((leaves.drop 24080).take 120) 481750000000 2 = true :=
    take_step (n := 2) (t := 120) (b := 24082) rfl rfl ArealUCore.ArealUK.chunk_12040 s41
  have s39 : leavesOK ctxLitU 478700000000 2 ((leaves.drop 24078).take 122) 481750000000 2 = true :=
    take_step (n := 2) (t := 122) (b := 24080) rfl rfl ArealUCore.ArealUK.chunk_12039 s40
  have s38 : leavesOK ctxLitU 478650000000 2 ((leaves.drop 24076).take 124) 481750000000 2 = true :=
    take_step (n := 2) (t := 124) (b := 24078) rfl rfl ArealUCore.ArealUK.chunk_12038 s39
  have s37 : leavesOK ctxLitU 478600000000 2 ((leaves.drop 24074).take 126) 481750000000 2 = true :=
    take_step (n := 2) (t := 126) (b := 24076) rfl rfl ArealUCore.ArealUK.chunk_12037 s38
  have s36 : leavesOK ctxLitU 478550000000 2 ((leaves.drop 24072).take 128) 481750000000 2 = true :=
    take_step (n := 2) (t := 128) (b := 24074) rfl rfl ArealUCore.ArealUK.chunk_12036 s37
  have s35 : leavesOK ctxLitU 478500000000 2 ((leaves.drop 24070).take 130) 481750000000 2 = true :=
    take_step (n := 2) (t := 130) (b := 24072) rfl rfl ArealUCore.ArealUK.chunk_12035 s36
  have s34 : leavesOK ctxLitU 478450000000 2 ((leaves.drop 24068).take 132) 481750000000 2 = true :=
    take_step (n := 2) (t := 132) (b := 24070) rfl rfl ArealUCore.ArealUK.chunk_12034 s35
  have s33 : leavesOK ctxLitU 478400000000 2 ((leaves.drop 24066).take 134) 481750000000 2 = true :=
    take_step (n := 2) (t := 134) (b := 24068) rfl rfl ArealUCore.ArealUK.chunk_12033 s34
  have s32 : leavesOK ctxLitU 478350000000 2 ((leaves.drop 24064).take 136) 481750000000 2 = true :=
    take_step (n := 2) (t := 136) (b := 24066) rfl rfl ArealUCore.ArealUK.chunk_12032 s33
  have s31 : leavesOK ctxLitU 478300000000 2 ((leaves.drop 24062).take 138) 481750000000 2 = true :=
    take_step (n := 2) (t := 138) (b := 24064) rfl rfl ArealUCore.ArealUK.chunk_12031 s32
  have s30 : leavesOK ctxLitU 478250000000 2 ((leaves.drop 24060).take 140) 481750000000 2 = true :=
    take_step (n := 2) (t := 140) (b := 24062) rfl rfl ArealUCore.ArealUK.chunk_12030 s31
  have s29 : leavesOK ctxLitU 478200000000 2 ((leaves.drop 24058).take 142) 481750000000 2 = true :=
    take_step (n := 2) (t := 142) (b := 24060) rfl rfl ArealUCore.ArealUK.chunk_12029 s30
  have s28 : leavesOK ctxLitU 478150000000 2 ((leaves.drop 24056).take 144) 481750000000 2 = true :=
    take_step (n := 2) (t := 144) (b := 24058) rfl rfl ArealUCore.ArealUK.chunk_12028 s29
  have s27 : leavesOK ctxLitU 478100000000 2 ((leaves.drop 24054).take 146) 481750000000 2 = true :=
    take_step (n := 2) (t := 146) (b := 24056) rfl rfl ArealUCore.ArealUK.chunk_12027 s28
  have s26 : leavesOK ctxLitU 478050000000 2 ((leaves.drop 24052).take 148) 481750000000 2 = true :=
    take_step (n := 2) (t := 148) (b := 24054) rfl rfl ArealUCore.ArealUK.chunk_12026 s27
  have s25 : leavesOK ctxLitU 478000000000 2 ((leaves.drop 24050).take 150) 481750000000 2 = true :=
    take_step (n := 2) (t := 150) (b := 24052) rfl rfl ArealUCore.ArealUK.chunk_12025 s26
  have s24 : leavesOK ctxLitU 477950000000 2 ((leaves.drop 24048).take 152) 481750000000 2 = true :=
    take_step (n := 2) (t := 152) (b := 24050) rfl rfl ArealUCore.ArealUK.chunk_12024 s25
  have s23 : leavesOK ctxLitU 477900000000 2 ((leaves.drop 24046).take 154) 481750000000 2 = true :=
    take_step (n := 2) (t := 154) (b := 24048) rfl rfl ArealUCore.ArealUK.chunk_12023 s24
  have s22 : leavesOK ctxLitU 477850000000 2 ((leaves.drop 24044).take 156) 481750000000 2 = true :=
    take_step (n := 2) (t := 156) (b := 24046) rfl rfl ArealUCore.ArealUK.chunk_12022 s23
  have s21 : leavesOK ctxLitU 477800000000 2 ((leaves.drop 24042).take 158) 481750000000 2 = true :=
    take_step (n := 2) (t := 158) (b := 24044) rfl rfl ArealUCore.ArealUK.chunk_12021 s22
  have s20 : leavesOK ctxLitU 477750000000 2 ((leaves.drop 24040).take 160) 481750000000 2 = true :=
    take_step (n := 2) (t := 160) (b := 24042) rfl rfl ArealUCore.ArealUK.chunk_12020 s21
  have s19 : leavesOK ctxLitU 477700000000 2 ((leaves.drop 24038).take 162) 481750000000 2 = true :=
    take_step (n := 2) (t := 162) (b := 24040) rfl rfl ArealUCore.ArealUK.chunk_12019 s20
  have s18 : leavesOK ctxLitU 477650000000 2 ((leaves.drop 24036).take 164) 481750000000 2 = true :=
    take_step (n := 2) (t := 164) (b := 24038) rfl rfl ArealUCore.ArealUK.chunk_12018 s19
  have s17 : leavesOK ctxLitU 477600000000 2 ((leaves.drop 24034).take 166) 481750000000 2 = true :=
    take_step (n := 2) (t := 166) (b := 24036) rfl rfl ArealUCore.ArealUK.chunk_12017 s18
  have s16 : leavesOK ctxLitU 477550000000 2 ((leaves.drop 24032).take 168) 481750000000 2 = true :=
    take_step (n := 2) (t := 168) (b := 24034) rfl rfl ArealUCore.ArealUK.chunk_12016 s17
  have s15 : leavesOK ctxLitU 477500000000 2 ((leaves.drop 24030).take 170) 481750000000 2 = true :=
    take_step (n := 2) (t := 170) (b := 24032) rfl rfl ArealUCore.ArealUK.chunk_12015 s16
  have s14 : leavesOK ctxLitU 477450000000 2 ((leaves.drop 24028).take 172) 481750000000 2 = true :=
    take_step (n := 2) (t := 172) (b := 24030) rfl rfl ArealUCore.ArealUK.chunk_12014 s15
  have s13 : leavesOK ctxLitU 477400000000 2 ((leaves.drop 24026).take 174) 481750000000 2 = true :=
    take_step (n := 2) (t := 174) (b := 24028) rfl rfl ArealUCore.ArealUK.chunk_12013 s14
  have s12 : leavesOK ctxLitU 477350000000 2 ((leaves.drop 24024).take 176) 481750000000 2 = true :=
    take_step (n := 2) (t := 176) (b := 24026) rfl rfl ArealUCore.ArealUK.chunk_12012 s13
  have s11 : leavesOK ctxLitU 477300000000 2 ((leaves.drop 24022).take 178) 481750000000 2 = true :=
    take_step (n := 2) (t := 178) (b := 24024) rfl rfl ArealUCore.ArealUK.chunk_12011 s12
  have s10 : leavesOK ctxLitU 477250000000 2 ((leaves.drop 24020).take 180) 481750000000 2 = true :=
    take_step (n := 2) (t := 180) (b := 24022) rfl rfl ArealUCore.ArealUK.chunk_12010 s11
  have s9 : leavesOK ctxLitU 477200000000 2 ((leaves.drop 24018).take 182) 481750000000 2 = true :=
    take_step (n := 2) (t := 182) (b := 24020) rfl rfl ArealUCore.ArealUK.chunk_12009 s10
  have s8 : leavesOK ctxLitU 477150000000 2 ((leaves.drop 24016).take 184) 481750000000 2 = true :=
    take_step (n := 2) (t := 184) (b := 24018) rfl rfl ArealUCore.ArealUK.chunk_12008 s9
  have s7 : leavesOK ctxLitU 477100000000 2 ((leaves.drop 24014).take 186) 481750000000 2 = true :=
    take_step (n := 2) (t := 186) (b := 24016) rfl rfl ArealUCore.ArealUK.chunk_12007 s8
  have s6 : leavesOK ctxLitU 477050000000 2 ((leaves.drop 24012).take 188) 481750000000 2 = true :=
    take_step (n := 2) (t := 188) (b := 24014) rfl rfl ArealUCore.ArealUK.chunk_12006 s7
  have s5 : leavesOK ctxLitU 477000000000 2 ((leaves.drop 24010).take 190) 481750000000 2 = true :=
    take_step (n := 2) (t := 190) (b := 24012) rfl rfl ArealUCore.ArealUK.chunk_12005 s6
  have s4 : leavesOK ctxLitU 476950000000 2 ((leaves.drop 24008).take 192) 481750000000 2 = true :=
    take_step (n := 2) (t := 192) (b := 24010) rfl rfl ArealUCore.ArealUK.chunk_12004 s5
  have s3 : leavesOK ctxLitU 476900000000 2 ((leaves.drop 24006).take 194) 481750000000 2 = true :=
    take_step (n := 2) (t := 194) (b := 24008) rfl rfl ArealUCore.ArealUK.chunk_12003 s4
  have s2 : leavesOK ctxLitU 476850000000 2 ((leaves.drop 24004).take 196) 481750000000 2 = true :=
    take_step (n := 2) (t := 196) (b := 24006) rfl rfl ArealUCore.ArealUK.chunk_12002 s3
  have s1 : leavesOK ctxLitU 476800000000 2 ((leaves.drop 24002).take 198) 481750000000 2 = true :=
    take_step (n := 2) (t := 198) (b := 24004) rfl rfl ArealUCore.ArealUK.chunk_12001 s2
  have s0 : leavesOK ctxLitU 476750000000 2 ((leaves.drop 24000).take 200) 481750000000 2 = true :=
    take_step (n := 2) (t := 200) (b := 24002) rfl rfl ArealUCore.ArealUK.chunk_12000 s1
  exact s0

end Areal.UCert

import ArealUK.Chunk16000
import ArealUK.Chunk16001
import ArealUK.Chunk16002
import ArealUK.Chunk16003
import ArealUK.Chunk16004
import ArealUK.Chunk16005
import ArealUK.Chunk16006
import ArealUK.Chunk16007
import ArealUK.Chunk16008
import ArealUK.Chunk16009
import ArealUK.Chunk16010
import ArealUK.Chunk16011
import ArealUK.Chunk16012
import ArealUK.Chunk16013
import ArealUK.Chunk16014
import ArealUK.Chunk16015
import ArealUK.Chunk16016
import ArealUK.Chunk16017
import ArealUK.Chunk16018
import ArealUK.Chunk16019
import ArealUK.Chunk16020
import ArealUK.Chunk16021
import ArealUK.Chunk16022
import ArealUK.Chunk16023
import ArealUK.Chunk16024
import ArealUK.Chunk16025
import ArealUK.Chunk16026
import ArealUK.Chunk16027
import ArealUK.Chunk16028
import ArealUK.Chunk16029
import ArealUK.Chunk16030
import ArealUK.Chunk16031
import ArealUK.Chunk16032
import ArealUK.Chunk16033
import ArealUK.Chunk16034
import ArealUK.Chunk16035
import ArealUK.Chunk16036
import ArealUK.Chunk16037
import ArealUK.Chunk16038
import ArealUK.Chunk16039
import ArealUK.Chunk16040
import ArealUK.Chunk16041
import ArealUK.Chunk16042
import ArealUK.Chunk16043
import ArealUK.Chunk16044
import ArealUK.Chunk16045
import ArealUK.Chunk16046
import ArealUK.Chunk16047
import ArealUK.Chunk16048
import ArealUK.Chunk16049
import ArealUK.Chunk16050
import ArealUK.Chunk16051
import ArealUK.Chunk16052
import ArealUK.Chunk16053
import ArealUK.Chunk16054
import ArealUK.Chunk16055
import ArealUK.Chunk16056
import ArealUK.Chunk16057
import ArealUK.Chunk16058
import ArealUK.Chunk16059
import ArealUK.Chunk16060
import ArealUK.Chunk16061
import ArealUK.Chunk16062
import ArealUK.Chunk16063
import ArealUK.Chunk16064
import ArealUK.Chunk16065
import ArealUK.Chunk16066
import ArealUK.Chunk16067
import ArealUK.Chunk16068
import ArealUK.Chunk16069
import ArealUK.Chunk16070
import ArealUK.Chunk16071
import ArealUK.Chunk16072
import ArealUK.Chunk16073
import ArealUK.Chunk16074
import ArealUK.Chunk16075
import ArealUK.Chunk16076
import ArealUK.Chunk16077
import ArealUK.Chunk16078
import ArealUK.Chunk16079
import ArealUK.Chunk16080
import ArealUK.Chunk16081
import ArealUK.Chunk16082
import ArealUK.Chunk16083
import ArealUK.Chunk16084
import ArealUK.Chunk16085
import ArealUK.Chunk16086
import ArealUK.Chunk16087
import ArealUK.Chunk16088
import ArealUK.Chunk16089
import ArealUK.Chunk16090
import ArealUK.Chunk16091
import ArealUK.Chunk16092
import ArealUK.Chunk16093
import ArealUK.Chunk16094
import ArealUK.Chunk16095
import ArealUK.Chunk16096
import ArealUK.Chunk16097
import ArealUK.Chunk16098
import ArealUK.Chunk16099
import Areal.UCert.LeavesKGen

/-! Group 160 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_160 : leavesOK ctxLitU 171068750000 0 ((leaves.drop 32000).take 200) 172556250000 0 = true := by
  have s99 := ArealUCore.ArealUK.chunk_16099
  have s98 : leavesOK ctxLitU 172531250000 0 ((leaves.drop 32196).take 4) 172556250000 0 = true :=
    take_step (n := 2) (t := 4) (b := 32198) rfl rfl ArealUCore.ArealUK.chunk_16098 s99
  have s97 : leavesOK ctxLitU 345037500000 1 ((leaves.drop 32194).take 6) 172556250000 0 = true :=
    take_step (n := 2) (t := 6) (b := 32196) rfl rfl ArealUCore.ArealUK.chunk_16097 s98
  have s96 : leavesOK ctxLitU 345012500000 1 ((leaves.drop 32192).take 8) 172556250000 0 = true :=
    take_step (n := 2) (t := 8) (b := 32194) rfl rfl ArealUCore.ArealUK.chunk_16096 s97
  have s95 : leavesOK ctxLitU 344975000000 1 ((leaves.drop 32190).take 10) 172556250000 0 = true :=
    take_step (n := 2) (t := 10) (b := 32192) rfl rfl ArealUCore.ArealUK.chunk_16095 s96
  have s94 : leavesOK ctxLitU 172462500000 0 ((leaves.drop 32188).take 12) 172556250000 0 = true :=
    take_step (n := 2) (t := 12) (b := 32190) rfl rfl ArealUCore.ArealUK.chunk_16094 s95
  have s93 : leavesOK ctxLitU 172443750000 0 ((leaves.drop 32186).take 14) 172556250000 0 = true :=
    take_step (n := 2) (t := 14) (b := 32188) rfl rfl ArealUCore.ArealUK.chunk_16093 s94
  have s92 : leavesOK ctxLitU 172431250000 0 ((leaves.drop 32184).take 16) 172556250000 0 = true :=
    take_step (n := 2) (t := 16) (b := 32186) rfl rfl ArealUCore.ArealUK.chunk_16092 s93
  have s91 : leavesOK ctxLitU 172412500000 0 ((leaves.drop 32182).take 18) 172556250000 0 = true :=
    take_step (n := 2) (t := 18) (b := 32184) rfl rfl ArealUCore.ArealUK.chunk_16091 s92
  have s90 : leavesOK ctxLitU 172393750000 0 ((leaves.drop 32180).take 20) 172556250000 0 = true :=
    take_step (n := 2) (t := 20) (b := 32182) rfl rfl ArealUCore.ArealUK.chunk_16090 s91
  have s89 : leavesOK ctxLitU 172381250000 0 ((leaves.drop 32178).take 22) 172556250000 0 = true :=
    take_step (n := 2) (t := 22) (b := 32180) rfl rfl ArealUCore.ArealUK.chunk_16089 s90
  have s88 : leavesOK ctxLitU 172368750000 0 ((leaves.drop 32176).take 24) 172556250000 0 = true :=
    take_step (n := 2) (t := 24) (b := 32178) rfl rfl ArealUCore.ArealUK.chunk_16088 s89
  have s87 : leavesOK ctxLitU 172356250000 0 ((leaves.drop 32174).take 26) 172556250000 0 = true :=
    take_step (n := 2) (t := 26) (b := 32176) rfl rfl ArealUCore.ArealUK.chunk_16087 s88
  have s86 : leavesOK ctxLitU 172343750000 0 ((leaves.drop 32172).take 28) 172556250000 0 = true :=
    take_step (n := 2) (t := 28) (b := 32174) rfl rfl ArealUCore.ArealUK.chunk_16086 s87
  have s85 : leavesOK ctxLitU 172331250000 0 ((leaves.drop 32170).take 30) 172556250000 0 = true :=
    take_step (n := 2) (t := 30) (b := 32172) rfl rfl ArealUCore.ArealUK.chunk_16085 s86
  have s84 : leavesOK ctxLitU 172312500000 0 ((leaves.drop 32168).take 32) 172556250000 0 = true :=
    take_step (n := 2) (t := 32) (b := 32170) rfl rfl ArealUCore.ArealUK.chunk_16084 s85
  have s83 : leavesOK ctxLitU 172293750000 0 ((leaves.drop 32166).take 34) 172556250000 0 = true :=
    take_step (n := 2) (t := 34) (b := 32168) rfl rfl ArealUCore.ArealUK.chunk_16083 s84
  have s82 : leavesOK ctxLitU 172281250000 0 ((leaves.drop 32164).take 36) 172556250000 0 = true :=
    take_step (n := 2) (t := 36) (b := 32166) rfl rfl ArealUCore.ArealUK.chunk_16082 s83
  have s81 : leavesOK ctxLitU 172268750000 0 ((leaves.drop 32162).take 38) 172556250000 0 = true :=
    take_step (n := 2) (t := 38) (b := 32164) rfl rfl ArealUCore.ArealUK.chunk_16081 s82
  have s80 : leavesOK ctxLitU 172256250000 0 ((leaves.drop 32160).take 40) 172556250000 0 = true :=
    take_step (n := 2) (t := 40) (b := 32162) rfl rfl ArealUCore.ArealUK.chunk_16080 s81
  have s79 : leavesOK ctxLitU 172243750000 0 ((leaves.drop 32158).take 42) 172556250000 0 = true :=
    take_step (n := 2) (t := 42) (b := 32160) rfl rfl ArealUCore.ArealUK.chunk_16079 s80
  have s78 : leavesOK ctxLitU 172231250000 0 ((leaves.drop 32156).take 44) 172556250000 0 = true :=
    take_step (n := 2) (t := 44) (b := 32158) rfl rfl ArealUCore.ArealUK.chunk_16078 s79
  have s77 : leavesOK ctxLitU 172218750000 0 ((leaves.drop 32154).take 46) 172556250000 0 = true :=
    take_step (n := 2) (t := 46) (b := 32156) rfl rfl ArealUCore.ArealUK.chunk_16077 s78
  have s76 : leavesOK ctxLitU 172206250000 0 ((leaves.drop 32152).take 48) 172556250000 0 = true :=
    take_step (n := 2) (t := 48) (b := 32154) rfl rfl ArealUCore.ArealUK.chunk_16076 s77
  have s75 : leavesOK ctxLitU 172187500000 0 ((leaves.drop 32150).take 50) 172556250000 0 = true :=
    take_step (n := 2) (t := 50) (b := 32152) rfl rfl ArealUCore.ArealUK.chunk_16075 s76
  have s74 : leavesOK ctxLitU 172168750000 0 ((leaves.drop 32148).take 52) 172556250000 0 = true :=
    take_step (n := 2) (t := 52) (b := 32150) rfl rfl ArealUCore.ArealUK.chunk_16074 s75
  have s73 : leavesOK ctxLitU 172156250000 0 ((leaves.drop 32146).take 54) 172556250000 0 = true :=
    take_step (n := 2) (t := 54) (b := 32148) rfl rfl ArealUCore.ArealUK.chunk_16073 s74
  have s72 : leavesOK ctxLitU 172143750000 0 ((leaves.drop 32144).take 56) 172556250000 0 = true :=
    take_step (n := 2) (t := 56) (b := 32146) rfl rfl ArealUCore.ArealUK.chunk_16072 s73
  have s71 : leavesOK ctxLitU 172131250000 0 ((leaves.drop 32142).take 58) 172556250000 0 = true :=
    take_step (n := 2) (t := 58) (b := 32144) rfl rfl ArealUCore.ArealUK.chunk_16071 s72
  have s70 : leavesOK ctxLitU 172112500000 0 ((leaves.drop 32140).take 60) 172556250000 0 = true :=
    take_step (n := 2) (t := 60) (b := 32142) rfl rfl ArealUCore.ArealUK.chunk_16070 s71
  have s69 : leavesOK ctxLitU 172087500000 0 ((leaves.drop 32138).take 62) 172556250000 0 = true :=
    take_step (n := 2) (t := 62) (b := 32140) rfl rfl ArealUCore.ArealUK.chunk_16069 s70
  have s68 : leavesOK ctxLitU 172068750000 0 ((leaves.drop 32136).take 64) 172556250000 0 = true :=
    take_step (n := 2) (t := 64) (b := 32138) rfl rfl ArealUCore.ArealUK.chunk_16068 s69
  have s67 : leavesOK ctxLitU 172056250000 0 ((leaves.drop 32134).take 66) 172556250000 0 = true :=
    take_step (n := 2) (t := 66) (b := 32136) rfl rfl ArealUCore.ArealUK.chunk_16067 s68
  have s66 : leavesOK ctxLitU 172043750000 0 ((leaves.drop 32132).take 68) 172556250000 0 = true :=
    take_step (n := 2) (t := 68) (b := 32134) rfl rfl ArealUCore.ArealUK.chunk_16066 s67
  have s65 : leavesOK ctxLitU 172031250000 0 ((leaves.drop 32130).take 70) 172556250000 0 = true :=
    take_step (n := 2) (t := 70) (b := 32132) rfl rfl ArealUCore.ArealUK.chunk_16065 s66
  have s64 : leavesOK ctxLitU 172018750000 0 ((leaves.drop 32128).take 72) 172556250000 0 = true :=
    take_step (n := 2) (t := 72) (b := 32130) rfl rfl ArealUCore.ArealUK.chunk_16064 s65
  have s63 : leavesOK ctxLitU 172006250000 0 ((leaves.drop 32126).take 74) 172556250000 0 = true :=
    take_step (n := 2) (t := 74) (b := 32128) rfl rfl ArealUCore.ArealUK.chunk_16063 s64
  have s62 : leavesOK ctxLitU 171993750000 0 ((leaves.drop 32124).take 76) 172556250000 0 = true :=
    take_step (n := 2) (t := 76) (b := 32126) rfl rfl ArealUCore.ArealUK.chunk_16062 s63
  have s61 : leavesOK ctxLitU 171981250000 0 ((leaves.drop 32122).take 78) 172556250000 0 = true :=
    take_step (n := 2) (t := 78) (b := 32124) rfl rfl ArealUCore.ArealUK.chunk_16061 s62
  have s60 : leavesOK ctxLitU 171962500000 0 ((leaves.drop 32120).take 80) 172556250000 0 = true :=
    take_step (n := 2) (t := 80) (b := 32122) rfl rfl ArealUCore.ArealUK.chunk_16060 s61
  have s59 : leavesOK ctxLitU 171943750000 0 ((leaves.drop 32118).take 82) 172556250000 0 = true :=
    take_step (n := 2) (t := 82) (b := 32120) rfl rfl ArealUCore.ArealUK.chunk_16059 s60
  have s58 : leavesOK ctxLitU 171931250000 0 ((leaves.drop 32116).take 84) 172556250000 0 = true :=
    take_step (n := 2) (t := 84) (b := 32118) rfl rfl ArealUCore.ArealUK.chunk_16058 s59
  have s57 : leavesOK ctxLitU 171912500000 0 ((leaves.drop 32114).take 86) 172556250000 0 = true :=
    take_step (n := 2) (t := 86) (b := 32116) rfl rfl ArealUCore.ArealUK.chunk_16057 s58
  have s56 : leavesOK ctxLitU 171887500000 0 ((leaves.drop 32112).take 88) 172556250000 0 = true :=
    take_step (n := 2) (t := 88) (b := 32114) rfl rfl ArealUCore.ArealUK.chunk_16056 s57
  have s55 : leavesOK ctxLitU 171868750000 0 ((leaves.drop 32110).take 90) 172556250000 0 = true :=
    take_step (n := 2) (t := 90) (b := 32112) rfl rfl ArealUCore.ArealUK.chunk_16055 s56
  have s54 : leavesOK ctxLitU 171856250000 0 ((leaves.drop 32108).take 92) 172556250000 0 = true :=
    take_step (n := 2) (t := 92) (b := 32110) rfl rfl ArealUCore.ArealUK.chunk_16054 s55
  have s53 : leavesOK ctxLitU 171843750000 0 ((leaves.drop 32106).take 94) 172556250000 0 = true :=
    take_step (n := 2) (t := 94) (b := 32108) rfl rfl ArealUCore.ArealUK.chunk_16053 s54
  have s52 : leavesOK ctxLitU 171831250000 0 ((leaves.drop 32104).take 96) 172556250000 0 = true :=
    take_step (n := 2) (t := 96) (b := 32106) rfl rfl ArealUCore.ArealUK.chunk_16052 s53
  have s51 : leavesOK ctxLitU 171818750000 0 ((leaves.drop 32102).take 98) 172556250000 0 = true :=
    take_step (n := 2) (t := 98) (b := 32104) rfl rfl ArealUCore.ArealUK.chunk_16051 s52
  have s50 : leavesOK ctxLitU 171806250000 0 ((leaves.drop 32100).take 100) 172556250000 0 = true :=
    take_step (n := 2) (t := 100) (b := 32102) rfl rfl ArealUCore.ArealUK.chunk_16050 s51
  have s49 : leavesOK ctxLitU 171793750000 0 ((leaves.drop 32098).take 102) 172556250000 0 = true :=
    take_step (n := 2) (t := 102) (b := 32100) rfl rfl ArealUCore.ArealUK.chunk_16049 s50
  have s48 : leavesOK ctxLitU 171781250000 0 ((leaves.drop 32096).take 104) 172556250000 0 = true :=
    take_step (n := 2) (t := 104) (b := 32098) rfl rfl ArealUCore.ArealUK.chunk_16048 s49
  have s47 : leavesOK ctxLitU 171762500000 0 ((leaves.drop 32094).take 106) 172556250000 0 = true :=
    take_step (n := 2) (t := 106) (b := 32096) rfl rfl ArealUCore.ArealUK.chunk_16047 s48
  have s46 : leavesOK ctxLitU 171743750000 0 ((leaves.drop 32092).take 108) 172556250000 0 = true :=
    take_step (n := 2) (t := 108) (b := 32094) rfl rfl ArealUCore.ArealUK.chunk_16046 s47
  have s45 : leavesOK ctxLitU 171731250000 0 ((leaves.drop 32090).take 110) 172556250000 0 = true :=
    take_step (n := 2) (t := 110) (b := 32092) rfl rfl ArealUCore.ArealUK.chunk_16045 s46
  have s44 : leavesOK ctxLitU 343437500000 1 ((leaves.drop 32088).take 112) 172556250000 0 = true :=
    take_step (n := 2) (t := 112) (b := 32090) rfl rfl ArealUCore.ArealUK.chunk_16044 s45
  have s43 : leavesOK ctxLitU 343412500000 1 ((leaves.drop 32086).take 114) 172556250000 0 = true :=
    take_step (n := 2) (t := 114) (b := 32088) rfl rfl ArealUCore.ArealUK.chunk_16043 s44
  have s42 : leavesOK ctxLitU 171687500000 0 ((leaves.drop 32084).take 116) 172556250000 0 = true :=
    take_step (n := 2) (t := 116) (b := 32086) rfl rfl ArealUCore.ArealUK.chunk_16042 s43
  have s41 : leavesOK ctxLitU 171668750000 0 ((leaves.drop 32082).take 118) 172556250000 0 = true :=
    take_step (n := 2) (t := 118) (b := 32084) rfl rfl ArealUCore.ArealUK.chunk_16041 s42
  have s40 : leavesOK ctxLitU 171656250000 0 ((leaves.drop 32080).take 120) 172556250000 0 = true :=
    take_step (n := 2) (t := 120) (b := 32082) rfl rfl ArealUCore.ArealUK.chunk_16040 s41
  have s39 : leavesOK ctxLitU 171643750000 0 ((leaves.drop 32078).take 122) 172556250000 0 = true :=
    take_step (n := 2) (t := 122) (b := 32080) rfl rfl ArealUCore.ArealUK.chunk_16039 s40
  have s38 : leavesOK ctxLitU 171631250000 0 ((leaves.drop 32076).take 124) 172556250000 0 = true :=
    take_step (n := 2) (t := 124) (b := 32078) rfl rfl ArealUCore.ArealUK.chunk_16038 s39
  have s37 : leavesOK ctxLitU 171612500000 0 ((leaves.drop 32074).take 126) 172556250000 0 = true :=
    take_step (n := 2) (t := 126) (b := 32076) rfl rfl ArealUCore.ArealUK.chunk_16037 s38
  have s36 : leavesOK ctxLitU 171587500000 0 ((leaves.drop 32072).take 128) 172556250000 0 = true :=
    take_step (n := 2) (t := 128) (b := 32074) rfl rfl ArealUCore.ArealUK.chunk_16036 s37
  have s35 : leavesOK ctxLitU 171568750000 0 ((leaves.drop 32070).take 130) 172556250000 0 = true :=
    take_step (n := 2) (t := 130) (b := 32072) rfl rfl ArealUCore.ArealUK.chunk_16035 s36
  have s34 : leavesOK ctxLitU 171556250000 0 ((leaves.drop 32068).take 132) 172556250000 0 = true :=
    take_step (n := 2) (t := 132) (b := 32070) rfl rfl ArealUCore.ArealUK.chunk_16034 s35
  have s33 : leavesOK ctxLitU 171543750000 0 ((leaves.drop 32066).take 134) 172556250000 0 = true :=
    take_step (n := 2) (t := 134) (b := 32068) rfl rfl ArealUCore.ArealUK.chunk_16033 s34
  have s32 : leavesOK ctxLitU 171531250000 0 ((leaves.drop 32064).take 136) 172556250000 0 = true :=
    take_step (n := 2) (t := 136) (b := 32066) rfl rfl ArealUCore.ArealUK.chunk_16032 s33
  have s31 : leavesOK ctxLitU 343037500000 1 ((leaves.drop 32062).take 138) 172556250000 0 = true :=
    take_step (n := 2) (t := 138) (b := 32064) rfl rfl ArealUCore.ArealUK.chunk_16031 s32
  have s30 : leavesOK ctxLitU 686037500000 2 ((leaves.drop 32060).take 140) 172556250000 0 = true :=
    take_step (n := 2) (t := 140) (b := 32062) rfl rfl ArealUCore.ArealUK.chunk_16030 s31
  have s29 : leavesOK ctxLitU 343000000000 1 ((leaves.drop 32058).take 142) 172556250000 0 = true :=
    take_step (n := 2) (t := 142) (b := 32060) rfl rfl ArealUCore.ArealUK.chunk_16029 s30
  have s28 : leavesOK ctxLitU 342950000000 1 ((leaves.drop 32056).take 144) 172556250000 0 = true :=
    take_step (n := 2) (t := 144) (b := 32058) rfl rfl ArealUCore.ArealUK.chunk_16028 s29
  have s27 : leavesOK ctxLitU 171450000000 0 ((leaves.drop 32054).take 146) 172556250000 0 = true :=
    take_step (n := 2) (t := 146) (b := 32056) rfl rfl ArealUCore.ArealUK.chunk_16027 s28
  have s26 : leavesOK ctxLitU 171437500000 0 ((leaves.drop 32052).take 148) 172556250000 0 = true :=
    take_step (n := 2) (t := 148) (b := 32054) rfl rfl ArealUCore.ArealUK.chunk_16026 s27
  have s25 : leavesOK ctxLitU 342862500000 1 ((leaves.drop 32050).take 150) 172556250000 0 = true :=
    take_step (n := 2) (t := 150) (b := 32052) rfl rfl ArealUCore.ArealUK.chunk_16025 s26
  have s24 : leavesOK ctxLitU 342850000000 1 ((leaves.drop 32048).take 152) 172556250000 0 = true :=
    take_step (n := 2) (t := 152) (b := 32050) rfl rfl ArealUCore.ArealUK.chunk_16024 s25
  have s23 : leavesOK ctxLitU 171400000000 0 ((leaves.drop 32046).take 154) 172556250000 0 = true :=
    take_step (n := 2) (t := 154) (b := 32048) rfl rfl ArealUCore.ArealUK.chunk_16023 s24
  have s22 : leavesOK ctxLitU 171375000000 0 ((leaves.drop 32044).take 156) 172556250000 0 = true :=
    take_step (n := 2) (t := 156) (b := 32046) rfl rfl ArealUCore.ArealUK.chunk_16022 s23
  have s21 : leavesOK ctxLitU 171362500000 0 ((leaves.drop 32042).take 158) 172556250000 0 = true :=
    take_step (n := 2) (t := 158) (b := 32044) rfl rfl ArealUCore.ArealUK.chunk_16021 s22
  have s20 : leavesOK ctxLitU 171350000000 0 ((leaves.drop 32040).take 160) 172556250000 0 = true :=
    take_step (n := 2) (t := 160) (b := 32042) rfl rfl ArealUCore.ArealUK.chunk_16020 s21
  have s19 : leavesOK ctxLitU 171337500000 0 ((leaves.drop 32038).take 162) 172556250000 0 = true :=
    take_step (n := 2) (t := 162) (b := 32040) rfl rfl ArealUCore.ArealUK.chunk_16019 s20
  have s18 : leavesOK ctxLitU 171325000000 0 ((leaves.drop 32036).take 164) 172556250000 0 = true :=
    take_step (n := 2) (t := 164) (b := 32038) rfl rfl ArealUCore.ArealUK.chunk_16018 s19
  have s17 : leavesOK ctxLitU 342625000000 1 ((leaves.drop 32034).take 166) 172556250000 0 = true :=
    take_step (n := 2) (t := 166) (b := 32036) rfl rfl ArealUCore.ArealUK.chunk_16017 s18
  have s16 : leavesOK ctxLitU 342600000000 1 ((leaves.drop 32032).take 168) 172556250000 0 = true :=
    take_step (n := 2) (t := 168) (b := 32034) rfl rfl ArealUCore.ArealUK.chunk_16016 s17
  have s15 : leavesOK ctxLitU 171275000000 0 ((leaves.drop 32030).take 170) 172556250000 0 = true :=
    take_step (n := 2) (t := 170) (b := 32032) rfl rfl ArealUCore.ArealUK.chunk_16015 s16
  have s14 : leavesOK ctxLitU 171262500000 0 ((leaves.drop 32028).take 172) 172556250000 0 = true :=
    take_step (n := 2) (t := 172) (b := 32030) rfl rfl ArealUCore.ArealUK.chunk_16014 s15
  have s13 : leavesOK ctxLitU 171250000000 0 ((leaves.drop 32026).take 174) 172556250000 0 = true :=
    take_step (n := 2) (t := 174) (b := 32028) rfl rfl ArealUCore.ArealUK.chunk_16013 s14
  have s12 : leavesOK ctxLitU 171237500000 0 ((leaves.drop 32024).take 176) 172556250000 0 = true :=
    take_step (n := 2) (t := 176) (b := 32026) rfl rfl ArealUCore.ArealUK.chunk_16012 s13
  have s11 : leavesOK ctxLitU 171225000000 0 ((leaves.drop 32022).take 178) 172556250000 0 = true :=
    take_step (n := 2) (t := 178) (b := 32024) rfl rfl ArealUCore.ArealUK.chunk_16011 s12
  have s10 : leavesOK ctxLitU 171212500000 0 ((leaves.drop 32020).take 180) 172556250000 0 = true :=
    take_step (n := 2) (t := 180) (b := 32022) rfl rfl ArealUCore.ArealUK.chunk_16010 s11
  have s9 : leavesOK ctxLitU 171200000000 0 ((leaves.drop 32018).take 182) 172556250000 0 = true :=
    take_step (n := 2) (t := 182) (b := 32020) rfl rfl ArealUCore.ArealUK.chunk_16009 s10
  have s8 : leavesOK ctxLitU 171187500000 0 ((leaves.drop 32016).take 184) 172556250000 0 = true :=
    take_step (n := 2) (t := 184) (b := 32018) rfl rfl ArealUCore.ArealUK.chunk_16008 s9
  have s7 : leavesOK ctxLitU 171175000000 0 ((leaves.drop 32014).take 186) 172556250000 0 = true :=
    take_step (n := 2) (t := 186) (b := 32016) rfl rfl ArealUCore.ArealUK.chunk_16007 s8
  have s6 : leavesOK ctxLitU 171162500000 0 ((leaves.drop 32012).take 188) 172556250000 0 = true :=
    take_step (n := 2) (t := 188) (b := 32014) rfl rfl ArealUCore.ArealUK.chunk_16006 s7
  have s5 : leavesOK ctxLitU 171150000000 0 ((leaves.drop 32010).take 190) 172556250000 0 = true :=
    take_step (n := 2) (t := 190) (b := 32012) rfl rfl ArealUCore.ArealUK.chunk_16005 s6
  have s4 : leavesOK ctxLitU 171137500000 0 ((leaves.drop 32008).take 192) 172556250000 0 = true :=
    take_step (n := 2) (t := 192) (b := 32010) rfl rfl ArealUCore.ArealUK.chunk_16004 s5
  have s3 : leavesOK ctxLitU 171125000000 0 ((leaves.drop 32006).take 194) 172556250000 0 = true :=
    take_step (n := 2) (t := 194) (b := 32008) rfl rfl ArealUCore.ArealUK.chunk_16003 s4
  have s2 : leavesOK ctxLitU 342212500000 1 ((leaves.drop 32004).take 196) 172556250000 0 = true :=
    take_step (n := 2) (t := 196) (b := 32006) rfl rfl ArealUCore.ArealUK.chunk_16002 s3
  have s1 : leavesOK ctxLitU 171087500000 0 ((leaves.drop 32002).take 198) 172556250000 0 = true :=
    take_step (n := 2) (t := 198) (b := 32004) rfl rfl ArealUCore.ArealUK.chunk_16001 s2
  have s0 : leavesOK ctxLitU 171068750000 0 ((leaves.drop 32000).take 200) 172556250000 0 = true :=
    take_step (n := 2) (t := 200) (b := 32002) rfl rfl ArealUCore.ArealUK.chunk_16000 s1
  exact s0

end Areal.UCert

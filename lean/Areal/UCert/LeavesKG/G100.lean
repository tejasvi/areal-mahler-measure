import ArealUK.Chunk10000
import ArealUK.Chunk10001
import ArealUK.Chunk10002
import ArealUK.Chunk10003
import ArealUK.Chunk10004
import ArealUK.Chunk10005
import ArealUK.Chunk10006
import ArealUK.Chunk10007
import ArealUK.Chunk10008
import ArealUK.Chunk10009
import ArealUK.Chunk10010
import ArealUK.Chunk10011
import ArealUK.Chunk10012
import ArealUK.Chunk10013
import ArealUK.Chunk10014
import ArealUK.Chunk10015
import ArealUK.Chunk10016
import ArealUK.Chunk10017
import ArealUK.Chunk10018
import ArealUK.Chunk10019
import ArealUK.Chunk10020
import ArealUK.Chunk10021
import ArealUK.Chunk10022
import ArealUK.Chunk10023
import ArealUK.Chunk10024
import ArealUK.Chunk10025
import ArealUK.Chunk10026
import ArealUK.Chunk10027
import ArealUK.Chunk10028
import ArealUK.Chunk10029
import ArealUK.Chunk10030
import ArealUK.Chunk10031
import ArealUK.Chunk10032
import ArealUK.Chunk10033
import ArealUK.Chunk10034
import ArealUK.Chunk10035
import ArealUK.Chunk10036
import ArealUK.Chunk10037
import ArealUK.Chunk10038
import ArealUK.Chunk10039
import ArealUK.Chunk10040
import ArealUK.Chunk10041
import ArealUK.Chunk10042
import ArealUK.Chunk10043
import ArealUK.Chunk10044
import ArealUK.Chunk10045
import ArealUK.Chunk10046
import ArealUK.Chunk10047
import ArealUK.Chunk10048
import ArealUK.Chunk10049
import ArealUK.Chunk10050
import ArealUK.Chunk10051
import ArealUK.Chunk10052
import ArealUK.Chunk10053
import ArealUK.Chunk10054
import ArealUK.Chunk10055
import ArealUK.Chunk10056
import ArealUK.Chunk10057
import ArealUK.Chunk10058
import ArealUK.Chunk10059
import ArealUK.Chunk10060
import ArealUK.Chunk10061
import ArealUK.Chunk10062
import ArealUK.Chunk10063
import ArealUK.Chunk10064
import ArealUK.Chunk10065
import ArealUK.Chunk10066
import ArealUK.Chunk10067
import ArealUK.Chunk10068
import ArealUK.Chunk10069
import ArealUK.Chunk10070
import ArealUK.Chunk10071
import ArealUK.Chunk10072
import ArealUK.Chunk10073
import ArealUK.Chunk10074
import ArealUK.Chunk10075
import ArealUK.Chunk10076
import ArealUK.Chunk10077
import ArealUK.Chunk10078
import ArealUK.Chunk10079
import ArealUK.Chunk10080
import ArealUK.Chunk10081
import ArealUK.Chunk10082
import ArealUK.Chunk10083
import ArealUK.Chunk10084
import ArealUK.Chunk10085
import ArealUK.Chunk10086
import ArealUK.Chunk10087
import ArealUK.Chunk10088
import ArealUK.Chunk10089
import ArealUK.Chunk10090
import ArealUK.Chunk10091
import ArealUK.Chunk10092
import ArealUK.Chunk10093
import ArealUK.Chunk10094
import ArealUK.Chunk10095
import ArealUK.Chunk10096
import ArealUK.Chunk10097
import ArealUK.Chunk10098
import ArealUK.Chunk10099
import Areal.UCert.LeavesKGen

/-! Group 100 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_100 : leavesOK ctxLitU 357175000000 2 ((leaves.drop 20000).take 200) 362175000000 2 = true := by
  have s99 := ArealUCore.ArealUK.chunk_10099
  have s98 : leavesOK ctxLitU 362075000000 2 ((leaves.drop 20196).take 4) 362175000000 2 = true :=
    take_step (n := 2) (t := 4) (b := 20198) rfl rfl ArealUCore.ArealUK.chunk_10098 s99
  have s97 : leavesOK ctxLitU 362025000000 2 ((leaves.drop 20194).take 6) 362175000000 2 = true :=
    take_step (n := 2) (t := 6) (b := 20196) rfl rfl ArealUCore.ArealUK.chunk_10097 s98
  have s96 : leavesOK ctxLitU 361975000000 2 ((leaves.drop 20192).take 8) 362175000000 2 = true :=
    take_step (n := 2) (t := 8) (b := 20194) rfl rfl ArealUCore.ArealUK.chunk_10096 s97
  have s95 : leavesOK ctxLitU 361925000000 2 ((leaves.drop 20190).take 10) 362175000000 2 = true :=
    take_step (n := 2) (t := 10) (b := 20192) rfl rfl ArealUCore.ArealUK.chunk_10095 s96
  have s94 : leavesOK ctxLitU 361875000000 2 ((leaves.drop 20188).take 12) 362175000000 2 = true :=
    take_step (n := 2) (t := 12) (b := 20190) rfl rfl ArealUCore.ArealUK.chunk_10094 s95
  have s93 : leavesOK ctxLitU 361825000000 2 ((leaves.drop 20186).take 14) 362175000000 2 = true :=
    take_step (n := 2) (t := 14) (b := 20188) rfl rfl ArealUCore.ArealUK.chunk_10093 s94
  have s92 : leavesOK ctxLitU 361775000000 2 ((leaves.drop 20184).take 16) 362175000000 2 = true :=
    take_step (n := 2) (t := 16) (b := 20186) rfl rfl ArealUCore.ArealUK.chunk_10092 s93
  have s91 : leavesOK ctxLitU 361725000000 2 ((leaves.drop 20182).take 18) 362175000000 2 = true :=
    take_step (n := 2) (t := 18) (b := 20184) rfl rfl ArealUCore.ArealUK.chunk_10091 s92
  have s90 : leavesOK ctxLitU 361675000000 2 ((leaves.drop 20180).take 20) 362175000000 2 = true :=
    take_step (n := 2) (t := 20) (b := 20182) rfl rfl ArealUCore.ArealUK.chunk_10090 s91
  have s89 : leavesOK ctxLitU 361625000000 2 ((leaves.drop 20178).take 22) 362175000000 2 = true :=
    take_step (n := 2) (t := 22) (b := 20180) rfl rfl ArealUCore.ArealUK.chunk_10089 s90
  have s88 : leavesOK ctxLitU 361575000000 2 ((leaves.drop 20176).take 24) 362175000000 2 = true :=
    take_step (n := 2) (t := 24) (b := 20178) rfl rfl ArealUCore.ArealUK.chunk_10088 s89
  have s87 : leavesOK ctxLitU 361525000000 2 ((leaves.drop 20174).take 26) 362175000000 2 = true :=
    take_step (n := 2) (t := 26) (b := 20176) rfl rfl ArealUCore.ArealUK.chunk_10087 s88
  have s86 : leavesOK ctxLitU 361475000000 2 ((leaves.drop 20172).take 28) 362175000000 2 = true :=
    take_step (n := 2) (t := 28) (b := 20174) rfl rfl ArealUCore.ArealUK.chunk_10086 s87
  have s85 : leavesOK ctxLitU 361425000000 2 ((leaves.drop 20170).take 30) 362175000000 2 = true :=
    take_step (n := 2) (t := 30) (b := 20172) rfl rfl ArealUCore.ArealUK.chunk_10085 s86
  have s84 : leavesOK ctxLitU 361375000000 2 ((leaves.drop 20168).take 32) 362175000000 2 = true :=
    take_step (n := 2) (t := 32) (b := 20170) rfl rfl ArealUCore.ArealUK.chunk_10084 s85
  have s83 : leavesOK ctxLitU 361325000000 2 ((leaves.drop 20166).take 34) 362175000000 2 = true :=
    take_step (n := 2) (t := 34) (b := 20168) rfl rfl ArealUCore.ArealUK.chunk_10083 s84
  have s82 : leavesOK ctxLitU 361275000000 2 ((leaves.drop 20164).take 36) 362175000000 2 = true :=
    take_step (n := 2) (t := 36) (b := 20166) rfl rfl ArealUCore.ArealUK.chunk_10082 s83
  have s81 : leavesOK ctxLitU 361225000000 2 ((leaves.drop 20162).take 38) 362175000000 2 = true :=
    take_step (n := 2) (t := 38) (b := 20164) rfl rfl ArealUCore.ArealUK.chunk_10081 s82
  have s80 : leavesOK ctxLitU 361175000000 2 ((leaves.drop 20160).take 40) 362175000000 2 = true :=
    take_step (n := 2) (t := 40) (b := 20162) rfl rfl ArealUCore.ArealUK.chunk_10080 s81
  have s79 : leavesOK ctxLitU 361125000000 2 ((leaves.drop 20158).take 42) 362175000000 2 = true :=
    take_step (n := 2) (t := 42) (b := 20160) rfl rfl ArealUCore.ArealUK.chunk_10079 s80
  have s78 : leavesOK ctxLitU 361075000000 2 ((leaves.drop 20156).take 44) 362175000000 2 = true :=
    take_step (n := 2) (t := 44) (b := 20158) rfl rfl ArealUCore.ArealUK.chunk_10078 s79
  have s77 : leavesOK ctxLitU 361025000000 2 ((leaves.drop 20154).take 46) 362175000000 2 = true :=
    take_step (n := 2) (t := 46) (b := 20156) rfl rfl ArealUCore.ArealUK.chunk_10077 s78
  have s76 : leavesOK ctxLitU 360975000000 2 ((leaves.drop 20152).take 48) 362175000000 2 = true :=
    take_step (n := 2) (t := 48) (b := 20154) rfl rfl ArealUCore.ArealUK.chunk_10076 s77
  have s75 : leavesOK ctxLitU 360925000000 2 ((leaves.drop 20150).take 50) 362175000000 2 = true :=
    take_step (n := 2) (t := 50) (b := 20152) rfl rfl ArealUCore.ArealUK.chunk_10075 s76
  have s74 : leavesOK ctxLitU 360875000000 2 ((leaves.drop 20148).take 52) 362175000000 2 = true :=
    take_step (n := 2) (t := 52) (b := 20150) rfl rfl ArealUCore.ArealUK.chunk_10074 s75
  have s73 : leavesOK ctxLitU 360825000000 2 ((leaves.drop 20146).take 54) 362175000000 2 = true :=
    take_step (n := 2) (t := 54) (b := 20148) rfl rfl ArealUCore.ArealUK.chunk_10073 s74
  have s72 : leavesOK ctxLitU 360775000000 2 ((leaves.drop 20144).take 56) 362175000000 2 = true :=
    take_step (n := 2) (t := 56) (b := 20146) rfl rfl ArealUCore.ArealUK.chunk_10072 s73
  have s71 : leavesOK ctxLitU 360725000000 2 ((leaves.drop 20142).take 58) 362175000000 2 = true :=
    take_step (n := 2) (t := 58) (b := 20144) rfl rfl ArealUCore.ArealUK.chunk_10071 s72
  have s70 : leavesOK ctxLitU 360675000000 2 ((leaves.drop 20140).take 60) 362175000000 2 = true :=
    take_step (n := 2) (t := 60) (b := 20142) rfl rfl ArealUCore.ArealUK.chunk_10070 s71
  have s69 : leavesOK ctxLitU 360625000000 2 ((leaves.drop 20138).take 62) 362175000000 2 = true :=
    take_step (n := 2) (t := 62) (b := 20140) rfl rfl ArealUCore.ArealUK.chunk_10069 s70
  have s68 : leavesOK ctxLitU 360575000000 2 ((leaves.drop 20136).take 64) 362175000000 2 = true :=
    take_step (n := 2) (t := 64) (b := 20138) rfl rfl ArealUCore.ArealUK.chunk_10068 s69
  have s67 : leavesOK ctxLitU 360525000000 2 ((leaves.drop 20134).take 66) 362175000000 2 = true :=
    take_step (n := 2) (t := 66) (b := 20136) rfl rfl ArealUCore.ArealUK.chunk_10067 s68
  have s66 : leavesOK ctxLitU 360475000000 2 ((leaves.drop 20132).take 68) 362175000000 2 = true :=
    take_step (n := 2) (t := 68) (b := 20134) rfl rfl ArealUCore.ArealUK.chunk_10066 s67
  have s65 : leavesOK ctxLitU 360425000000 2 ((leaves.drop 20130).take 70) 362175000000 2 = true :=
    take_step (n := 2) (t := 70) (b := 20132) rfl rfl ArealUCore.ArealUK.chunk_10065 s66
  have s64 : leavesOK ctxLitU 360375000000 2 ((leaves.drop 20128).take 72) 362175000000 2 = true :=
    take_step (n := 2) (t := 72) (b := 20130) rfl rfl ArealUCore.ArealUK.chunk_10064 s65
  have s63 : leavesOK ctxLitU 360325000000 2 ((leaves.drop 20126).take 74) 362175000000 2 = true :=
    take_step (n := 2) (t := 74) (b := 20128) rfl rfl ArealUCore.ArealUK.chunk_10063 s64
  have s62 : leavesOK ctxLitU 360275000000 2 ((leaves.drop 20124).take 76) 362175000000 2 = true :=
    take_step (n := 2) (t := 76) (b := 20126) rfl rfl ArealUCore.ArealUK.chunk_10062 s63
  have s61 : leavesOK ctxLitU 360225000000 2 ((leaves.drop 20122).take 78) 362175000000 2 = true :=
    take_step (n := 2) (t := 78) (b := 20124) rfl rfl ArealUCore.ArealUK.chunk_10061 s62
  have s60 : leavesOK ctxLitU 360175000000 2 ((leaves.drop 20120).take 80) 362175000000 2 = true :=
    take_step (n := 2) (t := 80) (b := 20122) rfl rfl ArealUCore.ArealUK.chunk_10060 s61
  have s59 : leavesOK ctxLitU 360125000000 2 ((leaves.drop 20118).take 82) 362175000000 2 = true :=
    take_step (n := 2) (t := 82) (b := 20120) rfl rfl ArealUCore.ArealUK.chunk_10059 s60
  have s58 : leavesOK ctxLitU 360075000000 2 ((leaves.drop 20116).take 84) 362175000000 2 = true :=
    take_step (n := 2) (t := 84) (b := 20118) rfl rfl ArealUCore.ArealUK.chunk_10058 s59
  have s57 : leavesOK ctxLitU 360025000000 2 ((leaves.drop 20114).take 86) 362175000000 2 = true :=
    take_step (n := 2) (t := 86) (b := 20116) rfl rfl ArealUCore.ArealUK.chunk_10057 s58
  have s56 : leavesOK ctxLitU 359975000000 2 ((leaves.drop 20112).take 88) 362175000000 2 = true :=
    take_step (n := 2) (t := 88) (b := 20114) rfl rfl ArealUCore.ArealUK.chunk_10056 s57
  have s55 : leavesOK ctxLitU 359925000000 2 ((leaves.drop 20110).take 90) 362175000000 2 = true :=
    take_step (n := 2) (t := 90) (b := 20112) rfl rfl ArealUCore.ArealUK.chunk_10055 s56
  have s54 : leavesOK ctxLitU 359875000000 2 ((leaves.drop 20108).take 92) 362175000000 2 = true :=
    take_step (n := 2) (t := 92) (b := 20110) rfl rfl ArealUCore.ArealUK.chunk_10054 s55
  have s53 : leavesOK ctxLitU 359825000000 2 ((leaves.drop 20106).take 94) 362175000000 2 = true :=
    take_step (n := 2) (t := 94) (b := 20108) rfl rfl ArealUCore.ArealUK.chunk_10053 s54
  have s52 : leavesOK ctxLitU 359775000000 2 ((leaves.drop 20104).take 96) 362175000000 2 = true :=
    take_step (n := 2) (t := 96) (b := 20106) rfl rfl ArealUCore.ArealUK.chunk_10052 s53
  have s51 : leavesOK ctxLitU 359725000000 2 ((leaves.drop 20102).take 98) 362175000000 2 = true :=
    take_step (n := 2) (t := 98) (b := 20104) rfl rfl ArealUCore.ArealUK.chunk_10051 s52
  have s50 : leavesOK ctxLitU 359675000000 2 ((leaves.drop 20100).take 100) 362175000000 2 = true :=
    take_step (n := 2) (t := 100) (b := 20102) rfl rfl ArealUCore.ArealUK.chunk_10050 s51
  have s49 : leavesOK ctxLitU 359625000000 2 ((leaves.drop 20098).take 102) 362175000000 2 = true :=
    take_step (n := 2) (t := 102) (b := 20100) rfl rfl ArealUCore.ArealUK.chunk_10049 s50
  have s48 : leavesOK ctxLitU 359575000000 2 ((leaves.drop 20096).take 104) 362175000000 2 = true :=
    take_step (n := 2) (t := 104) (b := 20098) rfl rfl ArealUCore.ArealUK.chunk_10048 s49
  have s47 : leavesOK ctxLitU 359525000000 2 ((leaves.drop 20094).take 106) 362175000000 2 = true :=
    take_step (n := 2) (t := 106) (b := 20096) rfl rfl ArealUCore.ArealUK.chunk_10047 s48
  have s46 : leavesOK ctxLitU 359475000000 2 ((leaves.drop 20092).take 108) 362175000000 2 = true :=
    take_step (n := 2) (t := 108) (b := 20094) rfl rfl ArealUCore.ArealUK.chunk_10046 s47
  have s45 : leavesOK ctxLitU 359425000000 2 ((leaves.drop 20090).take 110) 362175000000 2 = true :=
    take_step (n := 2) (t := 110) (b := 20092) rfl rfl ArealUCore.ArealUK.chunk_10045 s46
  have s44 : leavesOK ctxLitU 359375000000 2 ((leaves.drop 20088).take 112) 362175000000 2 = true :=
    take_step (n := 2) (t := 112) (b := 20090) rfl rfl ArealUCore.ArealUK.chunk_10044 s45
  have s43 : leavesOK ctxLitU 359325000000 2 ((leaves.drop 20086).take 114) 362175000000 2 = true :=
    take_step (n := 2) (t := 114) (b := 20088) rfl rfl ArealUCore.ArealUK.chunk_10043 s44
  have s42 : leavesOK ctxLitU 359275000000 2 ((leaves.drop 20084).take 116) 362175000000 2 = true :=
    take_step (n := 2) (t := 116) (b := 20086) rfl rfl ArealUCore.ArealUK.chunk_10042 s43
  have s41 : leavesOK ctxLitU 359225000000 2 ((leaves.drop 20082).take 118) 362175000000 2 = true :=
    take_step (n := 2) (t := 118) (b := 20084) rfl rfl ArealUCore.ArealUK.chunk_10041 s42
  have s40 : leavesOK ctxLitU 359175000000 2 ((leaves.drop 20080).take 120) 362175000000 2 = true :=
    take_step (n := 2) (t := 120) (b := 20082) rfl rfl ArealUCore.ArealUK.chunk_10040 s41
  have s39 : leavesOK ctxLitU 359125000000 2 ((leaves.drop 20078).take 122) 362175000000 2 = true :=
    take_step (n := 2) (t := 122) (b := 20080) rfl rfl ArealUCore.ArealUK.chunk_10039 s40
  have s38 : leavesOK ctxLitU 359075000000 2 ((leaves.drop 20076).take 124) 362175000000 2 = true :=
    take_step (n := 2) (t := 124) (b := 20078) rfl rfl ArealUCore.ArealUK.chunk_10038 s39
  have s37 : leavesOK ctxLitU 359025000000 2 ((leaves.drop 20074).take 126) 362175000000 2 = true :=
    take_step (n := 2) (t := 126) (b := 20076) rfl rfl ArealUCore.ArealUK.chunk_10037 s38
  have s36 : leavesOK ctxLitU 358975000000 2 ((leaves.drop 20072).take 128) 362175000000 2 = true :=
    take_step (n := 2) (t := 128) (b := 20074) rfl rfl ArealUCore.ArealUK.chunk_10036 s37
  have s35 : leavesOK ctxLitU 358925000000 2 ((leaves.drop 20070).take 130) 362175000000 2 = true :=
    take_step (n := 2) (t := 130) (b := 20072) rfl rfl ArealUCore.ArealUK.chunk_10035 s36
  have s34 : leavesOK ctxLitU 358875000000 2 ((leaves.drop 20068).take 132) 362175000000 2 = true :=
    take_step (n := 2) (t := 132) (b := 20070) rfl rfl ArealUCore.ArealUK.chunk_10034 s35
  have s33 : leavesOK ctxLitU 358825000000 2 ((leaves.drop 20066).take 134) 362175000000 2 = true :=
    take_step (n := 2) (t := 134) (b := 20068) rfl rfl ArealUCore.ArealUK.chunk_10033 s34
  have s32 : leavesOK ctxLitU 358775000000 2 ((leaves.drop 20064).take 136) 362175000000 2 = true :=
    take_step (n := 2) (t := 136) (b := 20066) rfl rfl ArealUCore.ArealUK.chunk_10032 s33
  have s31 : leavesOK ctxLitU 358725000000 2 ((leaves.drop 20062).take 138) 362175000000 2 = true :=
    take_step (n := 2) (t := 138) (b := 20064) rfl rfl ArealUCore.ArealUK.chunk_10031 s32
  have s30 : leavesOK ctxLitU 358675000000 2 ((leaves.drop 20060).take 140) 362175000000 2 = true :=
    take_step (n := 2) (t := 140) (b := 20062) rfl rfl ArealUCore.ArealUK.chunk_10030 s31
  have s29 : leavesOK ctxLitU 358625000000 2 ((leaves.drop 20058).take 142) 362175000000 2 = true :=
    take_step (n := 2) (t := 142) (b := 20060) rfl rfl ArealUCore.ArealUK.chunk_10029 s30
  have s28 : leavesOK ctxLitU 358575000000 2 ((leaves.drop 20056).take 144) 362175000000 2 = true :=
    take_step (n := 2) (t := 144) (b := 20058) rfl rfl ArealUCore.ArealUK.chunk_10028 s29
  have s27 : leavesOK ctxLitU 358525000000 2 ((leaves.drop 20054).take 146) 362175000000 2 = true :=
    take_step (n := 2) (t := 146) (b := 20056) rfl rfl ArealUCore.ArealUK.chunk_10027 s28
  have s26 : leavesOK ctxLitU 358475000000 2 ((leaves.drop 20052).take 148) 362175000000 2 = true :=
    take_step (n := 2) (t := 148) (b := 20054) rfl rfl ArealUCore.ArealUK.chunk_10026 s27
  have s25 : leavesOK ctxLitU 358425000000 2 ((leaves.drop 20050).take 150) 362175000000 2 = true :=
    take_step (n := 2) (t := 150) (b := 20052) rfl rfl ArealUCore.ArealUK.chunk_10025 s26
  have s24 : leavesOK ctxLitU 358375000000 2 ((leaves.drop 20048).take 152) 362175000000 2 = true :=
    take_step (n := 2) (t := 152) (b := 20050) rfl rfl ArealUCore.ArealUK.chunk_10024 s25
  have s23 : leavesOK ctxLitU 358325000000 2 ((leaves.drop 20046).take 154) 362175000000 2 = true :=
    take_step (n := 2) (t := 154) (b := 20048) rfl rfl ArealUCore.ArealUK.chunk_10023 s24
  have s22 : leavesOK ctxLitU 358275000000 2 ((leaves.drop 20044).take 156) 362175000000 2 = true :=
    take_step (n := 2) (t := 156) (b := 20046) rfl rfl ArealUCore.ArealUK.chunk_10022 s23
  have s21 : leavesOK ctxLitU 358225000000 2 ((leaves.drop 20042).take 158) 362175000000 2 = true :=
    take_step (n := 2) (t := 158) (b := 20044) rfl rfl ArealUCore.ArealUK.chunk_10021 s22
  have s20 : leavesOK ctxLitU 358175000000 2 ((leaves.drop 20040).take 160) 362175000000 2 = true :=
    take_step (n := 2) (t := 160) (b := 20042) rfl rfl ArealUCore.ArealUK.chunk_10020 s21
  have s19 : leavesOK ctxLitU 358125000000 2 ((leaves.drop 20038).take 162) 362175000000 2 = true :=
    take_step (n := 2) (t := 162) (b := 20040) rfl rfl ArealUCore.ArealUK.chunk_10019 s20
  have s18 : leavesOK ctxLitU 358075000000 2 ((leaves.drop 20036).take 164) 362175000000 2 = true :=
    take_step (n := 2) (t := 164) (b := 20038) rfl rfl ArealUCore.ArealUK.chunk_10018 s19
  have s17 : leavesOK ctxLitU 358025000000 2 ((leaves.drop 20034).take 166) 362175000000 2 = true :=
    take_step (n := 2) (t := 166) (b := 20036) rfl rfl ArealUCore.ArealUK.chunk_10017 s18
  have s16 : leavesOK ctxLitU 357975000000 2 ((leaves.drop 20032).take 168) 362175000000 2 = true :=
    take_step (n := 2) (t := 168) (b := 20034) rfl rfl ArealUCore.ArealUK.chunk_10016 s17
  have s15 : leavesOK ctxLitU 357925000000 2 ((leaves.drop 20030).take 170) 362175000000 2 = true :=
    take_step (n := 2) (t := 170) (b := 20032) rfl rfl ArealUCore.ArealUK.chunk_10015 s16
  have s14 : leavesOK ctxLitU 357875000000 2 ((leaves.drop 20028).take 172) 362175000000 2 = true :=
    take_step (n := 2) (t := 172) (b := 20030) rfl rfl ArealUCore.ArealUK.chunk_10014 s15
  have s13 : leavesOK ctxLitU 357825000000 2 ((leaves.drop 20026).take 174) 362175000000 2 = true :=
    take_step (n := 2) (t := 174) (b := 20028) rfl rfl ArealUCore.ArealUK.chunk_10013 s14
  have s12 : leavesOK ctxLitU 357775000000 2 ((leaves.drop 20024).take 176) 362175000000 2 = true :=
    take_step (n := 2) (t := 176) (b := 20026) rfl rfl ArealUCore.ArealUK.chunk_10012 s13
  have s11 : leavesOK ctxLitU 357725000000 2 ((leaves.drop 20022).take 178) 362175000000 2 = true :=
    take_step (n := 2) (t := 178) (b := 20024) rfl rfl ArealUCore.ArealUK.chunk_10011 s12
  have s10 : leavesOK ctxLitU 357675000000 2 ((leaves.drop 20020).take 180) 362175000000 2 = true :=
    take_step (n := 2) (t := 180) (b := 20022) rfl rfl ArealUCore.ArealUK.chunk_10010 s11
  have s9 : leavesOK ctxLitU 357625000000 2 ((leaves.drop 20018).take 182) 362175000000 2 = true :=
    take_step (n := 2) (t := 182) (b := 20020) rfl rfl ArealUCore.ArealUK.chunk_10009 s10
  have s8 : leavesOK ctxLitU 357575000000 2 ((leaves.drop 20016).take 184) 362175000000 2 = true :=
    take_step (n := 2) (t := 184) (b := 20018) rfl rfl ArealUCore.ArealUK.chunk_10008 s9
  have s7 : leavesOK ctxLitU 357525000000 2 ((leaves.drop 20014).take 186) 362175000000 2 = true :=
    take_step (n := 2) (t := 186) (b := 20016) rfl rfl ArealUCore.ArealUK.chunk_10007 s8
  have s6 : leavesOK ctxLitU 357475000000 2 ((leaves.drop 20012).take 188) 362175000000 2 = true :=
    take_step (n := 2) (t := 188) (b := 20014) rfl rfl ArealUCore.ArealUK.chunk_10006 s7
  have s5 : leavesOK ctxLitU 357425000000 2 ((leaves.drop 20010).take 190) 362175000000 2 = true :=
    take_step (n := 2) (t := 190) (b := 20012) rfl rfl ArealUCore.ArealUK.chunk_10005 s6
  have s4 : leavesOK ctxLitU 357375000000 2 ((leaves.drop 20008).take 192) 362175000000 2 = true :=
    take_step (n := 2) (t := 192) (b := 20010) rfl rfl ArealUCore.ArealUK.chunk_10004 s5
  have s3 : leavesOK ctxLitU 357325000000 2 ((leaves.drop 20006).take 194) 362175000000 2 = true :=
    take_step (n := 2) (t := 194) (b := 20008) rfl rfl ArealUCore.ArealUK.chunk_10003 s4
  have s2 : leavesOK ctxLitU 357275000000 2 ((leaves.drop 20004).take 196) 362175000000 2 = true :=
    take_step (n := 2) (t := 196) (b := 20006) rfl rfl ArealUCore.ArealUK.chunk_10002 s3
  have s1 : leavesOK ctxLitU 357225000000 2 ((leaves.drop 20002).take 198) 362175000000 2 = true :=
    take_step (n := 2) (t := 198) (b := 20004) rfl rfl ArealUCore.ArealUK.chunk_10001 s2
  have s0 : leavesOK ctxLitU 357175000000 2 ((leaves.drop 20000).take 200) 362175000000 2 = true :=
    take_step (n := 2) (t := 200) (b := 20002) rfl rfl ArealUCore.ArealUK.chunk_10000 s1
  exact s0

end Areal.UCert

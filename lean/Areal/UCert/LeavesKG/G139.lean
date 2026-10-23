import ArealUK.Chunk13900
import ArealUK.Chunk13901
import ArealUK.Chunk13902
import ArealUK.Chunk13903
import ArealUK.Chunk13904
import ArealUK.Chunk13905
import ArealUK.Chunk13906
import ArealUK.Chunk13907
import ArealUK.Chunk13908
import ArealUK.Chunk13909
import ArealUK.Chunk13910
import ArealUK.Chunk13911
import ArealUK.Chunk13912
import ArealUK.Chunk13913
import ArealUK.Chunk13914
import ArealUK.Chunk13915
import ArealUK.Chunk13916
import ArealUK.Chunk13917
import ArealUK.Chunk13918
import ArealUK.Chunk13919
import ArealUK.Chunk13920
import ArealUK.Chunk13921
import ArealUK.Chunk13922
import ArealUK.Chunk13923
import ArealUK.Chunk13924
import ArealUK.Chunk13925
import ArealUK.Chunk13926
import ArealUK.Chunk13927
import ArealUK.Chunk13928
import ArealUK.Chunk13929
import ArealUK.Chunk13930
import ArealUK.Chunk13931
import ArealUK.Chunk13932
import ArealUK.Chunk13933
import ArealUK.Chunk13934
import ArealUK.Chunk13935
import ArealUK.Chunk13936
import ArealUK.Chunk13937
import ArealUK.Chunk13938
import ArealUK.Chunk13939
import ArealUK.Chunk13940
import ArealUK.Chunk13941
import ArealUK.Chunk13942
import ArealUK.Chunk13943
import ArealUK.Chunk13944
import ArealUK.Chunk13945
import ArealUK.Chunk13946
import ArealUK.Chunk13947
import ArealUK.Chunk13948
import ArealUK.Chunk13949
import ArealUK.Chunk13950
import ArealUK.Chunk13951
import ArealUK.Chunk13952
import ArealUK.Chunk13953
import ArealUK.Chunk13954
import ArealUK.Chunk13955
import ArealUK.Chunk13956
import ArealUK.Chunk13957
import ArealUK.Chunk13958
import ArealUK.Chunk13959
import ArealUK.Chunk13960
import ArealUK.Chunk13961
import ArealUK.Chunk13962
import ArealUK.Chunk13963
import ArealUK.Chunk13964
import ArealUK.Chunk13965
import ArealUK.Chunk13966
import ArealUK.Chunk13967
import ArealUK.Chunk13968
import ArealUK.Chunk13969
import ArealUK.Chunk13970
import ArealUK.Chunk13971
import ArealUK.Chunk13972
import ArealUK.Chunk13973
import ArealUK.Chunk13974
import ArealUK.Chunk13975
import ArealUK.Chunk13976
import ArealUK.Chunk13977
import ArealUK.Chunk13978
import ArealUK.Chunk13979
import ArealUK.Chunk13980
import ArealUK.Chunk13981
import ArealUK.Chunk13982
import ArealUK.Chunk13983
import ArealUK.Chunk13984
import ArealUK.Chunk13985
import ArealUK.Chunk13986
import ArealUK.Chunk13987
import ArealUK.Chunk13988
import ArealUK.Chunk13989
import ArealUK.Chunk13990
import ArealUK.Chunk13991
import ArealUK.Chunk13992
import ArealUK.Chunk13993
import ArealUK.Chunk13994
import ArealUK.Chunk13995
import ArealUK.Chunk13996
import ArealUK.Chunk13997
import ArealUK.Chunk13998
import ArealUK.Chunk13999
import Areal.UCert.LeavesKGen

/-! Group 139 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_139 : leavesOK ctxLitU 142650000000 0 ((leaves.drop 27800).take 200) 575300000000 2 = true := by
  have s99 := ArealUCore.ArealUK.chunk_13999
  have s98 : leavesOK ctxLitU 575200000000 2 ((leaves.drop 27996).take 4) 575300000000 2 = true :=
    take_step (n := 2) (t := 4) (b := 27998) rfl rfl ArealUCore.ArealUK.chunk_13998 s99
  have s97 : leavesOK ctxLitU 287575000000 1 ((leaves.drop 27994).take 6) 575300000000 2 = true :=
    take_step (n := 2) (t := 6) (b := 27996) rfl rfl ArealUCore.ArealUK.chunk_13997 s98
  have s96 : leavesOK ctxLitU 287550000000 1 ((leaves.drop 27992).take 8) 575300000000 2 = true :=
    take_step (n := 2) (t := 8) (b := 27994) rfl rfl ArealUCore.ArealUK.chunk_13996 s97
  have s95 : leavesOK ctxLitU 287537500000 1 ((leaves.drop 27990).take 10) 575300000000 2 = true :=
    take_step (n := 2) (t := 10) (b := 27992) rfl rfl ArealUCore.ArealUK.chunk_13995 s96
  have s94 : leavesOK ctxLitU 143756250000 0 ((leaves.drop 27988).take 12) 575300000000 2 = true :=
    take_step (n := 2) (t := 12) (b := 27990) rfl rfl ArealUCore.ArealUK.chunk_13994 s95
  have s93 : leavesOK ctxLitU 143743750000 0 ((leaves.drop 27986).take 14) 575300000000 2 = true :=
    take_step (n := 2) (t := 14) (b := 27988) rfl rfl ArealUCore.ArealUK.chunk_13993 s94
  have s92 : leavesOK ctxLitU 143731250000 0 ((leaves.drop 27984).take 16) 575300000000 2 = true :=
    take_step (n := 2) (t := 16) (b := 27986) rfl rfl ArealUCore.ArealUK.chunk_13992 s93
  have s91 : leavesOK ctxLitU 287437500000 1 ((leaves.drop 27982).take 18) 575300000000 2 = true :=
    take_step (n := 2) (t := 18) (b := 27984) rfl rfl ArealUCore.ArealUK.chunk_13991 s92
  have s90 : leavesOK ctxLitU 574837500000 2 ((leaves.drop 27980).take 20) 575300000000 2 = true :=
    take_step (n := 2) (t := 20) (b := 27982) rfl rfl ArealUCore.ArealUK.chunk_13990 s91
  have s89 : leavesOK ctxLitU 287400000000 1 ((leaves.drop 27978).take 22) 575300000000 2 = true :=
    take_step (n := 2) (t := 22) (b := 27980) rfl rfl ArealUCore.ArealUK.chunk_13989 s90
  have s88 : leavesOK ctxLitU 574750000000 2 ((leaves.drop 27976).take 24) 575300000000 2 = true :=
    take_step (n := 2) (t := 24) (b := 27978) rfl rfl ArealUCore.ArealUK.chunk_13988 s89
  have s87 : leavesOK ctxLitU 574700000000 2 ((leaves.drop 27974).take 26) 575300000000 2 = true :=
    take_step (n := 2) (t := 26) (b := 27976) rfl rfl ArealUCore.ArealUK.chunk_13987 s88
  have s86 : leavesOK ctxLitU 287325000000 1 ((leaves.drop 27972).take 28) 575300000000 2 = true :=
    take_step (n := 2) (t := 28) (b := 27974) rfl rfl ArealUCore.ArealUK.chunk_13986 s87
  have s85 : leavesOK ctxLitU 287300000000 1 ((leaves.drop 27970).take 30) 575300000000 2 = true :=
    take_step (n := 2) (t := 30) (b := 27972) rfl rfl ArealUCore.ArealUK.chunk_13985 s86
  have s84 : leavesOK ctxLitU 143637500000 0 ((leaves.drop 27968).take 32) 575300000000 2 = true :=
    take_step (n := 2) (t := 32) (b := 27970) rfl rfl ArealUCore.ArealUK.chunk_13984 s85
  have s83 : leavesOK ctxLitU 287262500000 1 ((leaves.drop 27966).take 34) 575300000000 2 = true :=
    take_step (n := 2) (t := 34) (b := 27968) rfl rfl ArealUCore.ArealUK.chunk_13983 s84
  have s82 : leavesOK ctxLitU 287250000000 1 ((leaves.drop 27964).take 36) 575300000000 2 = true :=
    take_step (n := 2) (t := 36) (b := 27966) rfl rfl ArealUCore.ArealUK.chunk_13982 s83
  have s81 : leavesOK ctxLitU 287225000000 1 ((leaves.drop 27962).take 38) 575300000000 2 = true :=
    take_step (n := 2) (t := 38) (b := 27964) rfl rfl ArealUCore.ArealUK.chunk_13981 s82
  have s80 : leavesOK ctxLitU 287200000000 1 ((leaves.drop 27960).take 40) 575300000000 2 = true :=
    take_step (n := 2) (t := 40) (b := 27962) rfl rfl ArealUCore.ArealUK.chunk_13980 s81
  have s79 : leavesOK ctxLitU 287175000000 1 ((leaves.drop 27958).take 42) 575300000000 2 = true :=
    take_step (n := 2) (t := 42) (b := 27960) rfl rfl ArealUCore.ArealUK.chunk_13979 s80
  have s78 : leavesOK ctxLitU 287150000000 1 ((leaves.drop 27956).take 44) 575300000000 2 = true :=
    take_step (n := 2) (t := 44) (b := 27958) rfl rfl ArealUCore.ArealUK.chunk_13978 s79
  have s77 : leavesOK ctxLitU 287137500000 1 ((leaves.drop 27954).take 46) 575300000000 2 = true :=
    take_step (n := 2) (t := 46) (b := 27956) rfl rfl ArealUCore.ArealUK.chunk_13977 s78
  have s76 : leavesOK ctxLitU 143556250000 0 ((leaves.drop 27952).take 48) 575300000000 2 = true :=
    take_step (n := 2) (t := 48) (b := 27954) rfl rfl ArealUCore.ArealUK.chunk_13976 s77
  have s75 : leavesOK ctxLitU 287087500000 1 ((leaves.drop 27950).take 50) 575300000000 2 = true :=
    take_step (n := 2) (t := 50) (b := 27952) rfl rfl ArealUCore.ArealUK.chunk_13975 s76
  have s74 : leavesOK ctxLitU 287062500000 1 ((leaves.drop 27948).take 52) 575300000000 2 = true :=
    take_step (n := 2) (t := 52) (b := 27950) rfl rfl ArealUCore.ArealUK.chunk_13974 s75
  have s73 : leavesOK ctxLitU 574075000000 2 ((leaves.drop 27946).take 54) 575300000000 2 = true :=
    take_step (n := 2) (t := 54) (b := 27948) rfl rfl ArealUCore.ArealUK.chunk_13973 s74
  have s72 : leavesOK ctxLitU 574025000000 2 ((leaves.drop 27944).take 56) 575300000000 2 = true :=
    take_step (n := 2) (t := 56) (b := 27946) rfl rfl ArealUCore.ArealUK.chunk_13972 s73
  have s71 : leavesOK ctxLitU 573975000000 2 ((leaves.drop 27942).take 58) 575300000000 2 = true :=
    take_step (n := 2) (t := 58) (b := 27944) rfl rfl ArealUCore.ArealUK.chunk_13971 s72
  have s70 : leavesOK ctxLitU 573925000000 2 ((leaves.drop 27940).take 60) 575300000000 2 = true :=
    take_step (n := 2) (t := 60) (b := 27942) rfl rfl ArealUCore.ArealUK.chunk_13970 s71
  have s69 : leavesOK ctxLitU 286937500000 1 ((leaves.drop 27938).take 62) 575300000000 2 = true :=
    take_step (n := 2) (t := 62) (b := 27940) rfl rfl ArealUCore.ArealUK.chunk_13969 s70
  have s68 : leavesOK ctxLitU 286912500000 1 ((leaves.drop 27936).take 64) 575300000000 2 = true :=
    take_step (n := 2) (t := 64) (b := 27938) rfl rfl ArealUCore.ArealUK.chunk_13968 s69
  have s67 : leavesOK ctxLitU 143443750000 0 ((leaves.drop 27934).take 66) 575300000000 2 = true :=
    take_step (n := 2) (t := 66) (b := 27936) rfl rfl ArealUCore.ArealUK.chunk_13967 s68
  have s66 : leavesOK ctxLitU 286868750000 1 ((leaves.drop 27932).take 68) 575300000000 2 = true :=
    take_step (n := 2) (t := 68) (b := 27934) rfl rfl ArealUCore.ArealUK.chunk_13966 s67
  have s65 : leavesOK ctxLitU 286856250000 1 ((leaves.drop 27930).take 70) 575300000000 2 = true :=
    take_step (n := 2) (t := 70) (b := 27932) rfl rfl ArealUCore.ArealUK.chunk_13965 s66
  have s64 : leavesOK ctxLitU 286837500000 1 ((leaves.drop 27928).take 72) 575300000000 2 = true :=
    take_step (n := 2) (t := 72) (b := 27930) rfl rfl ArealUCore.ArealUK.chunk_13964 s65
  have s63 : leavesOK ctxLitU 286812500000 1 ((leaves.drop 27926).take 74) 575300000000 2 = true :=
    take_step (n := 2) (t := 74) (b := 27928) rfl rfl ArealUCore.ArealUK.chunk_13963 s64
  have s62 : leavesOK ctxLitU 286787500000 1 ((leaves.drop 27924).take 76) 575300000000 2 = true :=
    take_step (n := 2) (t := 76) (b := 27926) rfl rfl ArealUCore.ArealUK.chunk_13962 s63
  have s61 : leavesOK ctxLitU 286762500000 1 ((leaves.drop 27922).take 78) 575300000000 2 = true :=
    take_step (n := 2) (t := 78) (b := 27924) rfl rfl ArealUCore.ArealUK.chunk_13961 s62
  have s60 : leavesOK ctxLitU 143368750000 0 ((leaves.drop 27920).take 80) 575300000000 2 = true :=
    take_step (n := 2) (t := 80) (b := 27922) rfl rfl ArealUCore.ArealUK.chunk_13960 s61
  have s59 : leavesOK ctxLitU 143356250000 0 ((leaves.drop 27918).take 82) 575300000000 2 = true :=
    take_step (n := 2) (t := 82) (b := 27920) rfl rfl ArealUCore.ArealUK.chunk_13959 s60
  have s58 : leavesOK ctxLitU 143343750000 0 ((leaves.drop 27916).take 84) 575300000000 2 = true :=
    take_step (n := 2) (t := 84) (b := 27918) rfl rfl ArealUCore.ArealUK.chunk_13958 s59
  have s57 : leavesOK ctxLitU 143331250000 0 ((leaves.drop 27914).take 86) 575300000000 2 = true :=
    take_step (n := 2) (t := 86) (b := 27916) rfl rfl ArealUCore.ArealUK.chunk_13957 s58
  have s56 : leavesOK ctxLitU 286637500000 1 ((leaves.drop 27912).take 88) 575300000000 2 = true :=
    take_step (n := 2) (t := 88) (b := 27914) rfl rfl ArealUCore.ArealUK.chunk_13956 s57
  have s55 : leavesOK ctxLitU 286612500000 1 ((leaves.drop 27910).take 90) 575300000000 2 = true :=
    take_step (n := 2) (t := 90) (b := 27912) rfl rfl ArealUCore.ArealUK.chunk_13955 s56
  have s54 : leavesOK ctxLitU 286587500000 1 ((leaves.drop 27908).take 92) 575300000000 2 = true :=
    take_step (n := 2) (t := 92) (b := 27910) rfl rfl ArealUCore.ArealUK.chunk_13954 s55
  have s53 : leavesOK ctxLitU 286562500000 1 ((leaves.drop 27906).take 94) 575300000000 2 = true :=
    take_step (n := 2) (t := 94) (b := 27908) rfl rfl ArealUCore.ArealUK.chunk_13953 s54
  have s52 : leavesOK ctxLitU 143268750000 0 ((leaves.drop 27904).take 96) 575300000000 2 = true :=
    take_step (n := 2) (t := 96) (b := 27906) rfl rfl ArealUCore.ArealUK.chunk_13952 s53
  have s51 : leavesOK ctxLitU 143256250000 0 ((leaves.drop 27902).take 98) 575300000000 2 = true :=
    take_step (n := 2) (t := 98) (b := 27904) rfl rfl ArealUCore.ArealUK.chunk_13951 s52
  have s50 : leavesOK ctxLitU 143243750000 0 ((leaves.drop 27900).take 100) 575300000000 2 = true :=
    take_step (n := 2) (t := 100) (b := 27902) rfl rfl ArealUCore.ArealUK.chunk_13950 s51
  have s49 : leavesOK ctxLitU 143231250000 0 ((leaves.drop 27898).take 102) 575300000000 2 = true :=
    take_step (n := 2) (t := 102) (b := 27900) rfl rfl ArealUCore.ArealUK.chunk_13949 s50
  have s48 : leavesOK ctxLitU 286450000000 1 ((leaves.drop 27896).take 104) 575300000000 2 = true :=
    take_step (n := 2) (t := 104) (b := 27898) rfl rfl ArealUCore.ArealUK.chunk_13948 s49
  have s47 : leavesOK ctxLitU 286425000000 1 ((leaves.drop 27894).take 106) 575300000000 2 = true :=
    take_step (n := 2) (t := 106) (b := 27896) rfl rfl ArealUCore.ArealUK.chunk_13947 s48
  have s46 : leavesOK ctxLitU 286400000000 1 ((leaves.drop 27892).take 108) 575300000000 2 = true :=
    take_step (n := 2) (t := 108) (b := 27894) rfl rfl ArealUCore.ArealUK.chunk_13946 s47
  have s45 : leavesOK ctxLitU 572750000000 2 ((leaves.drop 27890).take 110) 575300000000 2 = true :=
    take_step (n := 2) (t := 110) (b := 27892) rfl rfl ArealUCore.ArealUK.chunk_13945 s46
  have s44 : leavesOK ctxLitU 572700000000 2 ((leaves.drop 27888).take 112) 575300000000 2 = true :=
    take_step (n := 2) (t := 112) (b := 27890) rfl rfl ArealUCore.ArealUK.chunk_13944 s45
  have s43 : leavesOK ctxLitU 572650000000 2 ((leaves.drop 27886).take 114) 575300000000 2 = true :=
    take_step (n := 2) (t := 114) (b := 27888) rfl rfl ArealUCore.ArealUK.chunk_13943 s44
  have s42 : leavesOK ctxLitU 572600000000 2 ((leaves.drop 27884).take 116) 575300000000 2 = true :=
    take_step (n := 2) (t := 116) (b := 27886) rfl rfl ArealUCore.ArealUK.chunk_13942 s43
  have s41 : leavesOK ctxLitU 572525000000 2 ((leaves.drop 27882).take 118) 575300000000 2 = true :=
    take_step (n := 2) (t := 118) (b := 27884) rfl rfl ArealUCore.ArealUK.chunk_13941 s42
  have s40 : leavesOK ctxLitU 572475000000 2 ((leaves.drop 27880).take 120) 575300000000 2 = true :=
    take_step (n := 2) (t := 120) (b := 27882) rfl rfl ArealUCore.ArealUK.chunk_13940 s41
  have s39 : leavesOK ctxLitU 572425000000 2 ((leaves.drop 27878).take 122) 575300000000 2 = true :=
    take_step (n := 2) (t := 122) (b := 27880) rfl rfl ArealUCore.ArealUK.chunk_13939 s40
  have s38 : leavesOK ctxLitU 286187500000 1 ((leaves.drop 27876).take 124) 575300000000 2 = true :=
    take_step (n := 2) (t := 124) (b := 27878) rfl rfl ArealUCore.ArealUK.chunk_13938 s39
  have s37 : leavesOK ctxLitU 286162500000 1 ((leaves.drop 27874).take 126) 575300000000 2 = true :=
    take_step (n := 2) (t := 126) (b := 27876) rfl rfl ArealUCore.ArealUK.chunk_13937 s38
  have s36 : leavesOK ctxLitU 286143750000 1 ((leaves.drop 27872).take 128) 575300000000 2 = true :=
    take_step (n := 2) (t := 128) (b := 27874) rfl rfl ArealUCore.ArealUK.chunk_13936 s37
  have s35 : leavesOK ctxLitU 286131250000 1 ((leaves.drop 27870).take 130) 575300000000 2 = true :=
    take_step (n := 2) (t := 130) (b := 27872) rfl rfl ArealUCore.ArealUK.chunk_13935 s36
  have s34 : leavesOK ctxLitU 143056250000 0 ((leaves.drop 27868).take 132) 575300000000 2 = true :=
    take_step (n := 2) (t := 132) (b := 27870) rfl rfl ArealUCore.ArealUK.chunk_13934 s35
  have s33 : leavesOK ctxLitU 143043750000 0 ((leaves.drop 27866).take 134) 575300000000 2 = true :=
    take_step (n := 2) (t := 134) (b := 27868) rfl rfl ArealUCore.ArealUK.chunk_13933 s34
  have s32 : leavesOK ctxLitU 286068750000 1 ((leaves.drop 27864).take 136) 575300000000 2 = true :=
    take_step (n := 2) (t := 136) (b := 27866) rfl rfl ArealUCore.ArealUK.chunk_13932 s33
  have s31 : leavesOK ctxLitU 286056250000 1 ((leaves.drop 27862).take 138) 575300000000 2 = true :=
    take_step (n := 2) (t := 138) (b := 27864) rfl rfl ArealUCore.ArealUK.chunk_13931 s32
  have s30 : leavesOK ctxLitU 286037500000 1 ((leaves.drop 27860).take 140) 575300000000 2 = true :=
    take_step (n := 2) (t := 140) (b := 27862) rfl rfl ArealUCore.ArealUK.chunk_13930 s31
  have s29 : leavesOK ctxLitU 286012500000 1 ((leaves.drop 27858).take 142) 575300000000 2 = true :=
    take_step (n := 2) (t := 142) (b := 27860) rfl rfl ArealUCore.ArealUK.chunk_13929 s30
  have s28 : leavesOK ctxLitU 571975000000 2 ((leaves.drop 27856).take 144) 575300000000 2 = true :=
    take_step (n := 2) (t := 144) (b := 27858) rfl rfl ArealUCore.ArealUK.chunk_13928 s29
  have s27 : leavesOK ctxLitU 571925000000 2 ((leaves.drop 27854).take 146) 575300000000 2 = true :=
    take_step (n := 2) (t := 146) (b := 27856) rfl rfl ArealUCore.ArealUK.chunk_13927 s28
  have s26 : leavesOK ctxLitU 571875000000 2 ((leaves.drop 27852).take 148) 575300000000 2 = true :=
    take_step (n := 2) (t := 148) (b := 27854) rfl rfl ArealUCore.ArealUK.chunk_13926 s27
  have s25 : leavesOK ctxLitU 571825000000 2 ((leaves.drop 27850).take 150) 575300000000 2 = true :=
    take_step (n := 2) (t := 150) (b := 27852) rfl rfl ArealUCore.ArealUK.chunk_13925 s26
  have s24 : leavesOK ctxLitU 285875000000 1 ((leaves.drop 27848).take 152) 575300000000 2 = true :=
    take_step (n := 2) (t := 152) (b := 27850) rfl rfl ArealUCore.ArealUK.chunk_13924 s25
  have s23 : leavesOK ctxLitU 571700000000 2 ((leaves.drop 27846).take 154) 575300000000 2 = true :=
    take_step (n := 2) (t := 154) (b := 27848) rfl rfl ArealUCore.ArealUK.chunk_13923 s24
  have s22 : leavesOK ctxLitU 571650000000 2 ((leaves.drop 27844).take 156) 575300000000 2 = true :=
    take_step (n := 2) (t := 156) (b := 27846) rfl rfl ArealUCore.ArealUK.chunk_13922 s23
  have s21 : leavesOK ctxLitU 571600000000 2 ((leaves.drop 27842).take 158) 575300000000 2 = true :=
    take_step (n := 2) (t := 158) (b := 27844) rfl rfl ArealUCore.ArealUK.chunk_13921 s22
  have s20 : leavesOK ctxLitU 285775000000 1 ((leaves.drop 27840).take 160) 575300000000 2 = true :=
    take_step (n := 2) (t := 160) (b := 27842) rfl rfl ArealUCore.ArealUK.chunk_13920 s21
  have s19 : leavesOK ctxLitU 285750000000 1 ((leaves.drop 27838).take 162) 575300000000 2 = true :=
    take_step (n := 2) (t := 162) (b := 27840) rfl rfl ArealUCore.ArealUK.chunk_13919 s20
  have s18 : leavesOK ctxLitU 142862500000 0 ((leaves.drop 27836).take 164) 575300000000 2 = true :=
    take_step (n := 2) (t := 164) (b := 27838) rfl rfl ArealUCore.ArealUK.chunk_13918 s19
  have s17 : leavesOK ctxLitU 142850000000 0 ((leaves.drop 27834).take 166) 575300000000 2 = true :=
    take_step (n := 2) (t := 166) (b := 27836) rfl rfl ArealUCore.ArealUK.chunk_13917 s18
  have s16 : leavesOK ctxLitU 142837500000 0 ((leaves.drop 27832).take 168) 575300000000 2 = true :=
    take_step (n := 2) (t := 168) (b := 27834) rfl rfl ArealUCore.ArealUK.chunk_13916 s17
  have s15 : leavesOK ctxLitU 142825000000 0 ((leaves.drop 27830).take 170) 575300000000 2 = true :=
    take_step (n := 2) (t := 170) (b := 27832) rfl rfl ArealUCore.ArealUK.chunk_13915 s16
  have s14 : leavesOK ctxLitU 285625000000 1 ((leaves.drop 27828).take 172) 575300000000 2 = true :=
    take_step (n := 2) (t := 172) (b := 27830) rfl rfl ArealUCore.ArealUK.chunk_13914 s15
  have s13 : leavesOK ctxLitU 285600000000 1 ((leaves.drop 27826).take 174) 575300000000 2 = true :=
    take_step (n := 2) (t := 174) (b := 27828) rfl rfl ArealUCore.ArealUK.chunk_13913 s14
  have s12 : leavesOK ctxLitU 285575000000 1 ((leaves.drop 27824).take 176) 575300000000 2 = true :=
    take_step (n := 2) (t := 176) (b := 27826) rfl rfl ArealUCore.ArealUK.chunk_13912 s13
  have s11 : leavesOK ctxLitU 285550000000 1 ((leaves.drop 27822).take 178) 575300000000 2 = true :=
    take_step (n := 2) (t := 178) (b := 27824) rfl rfl ArealUCore.ArealUK.chunk_13911 s12
  have s10 : leavesOK ctxLitU 285537500000 1 ((leaves.drop 27820).take 180) 575300000000 2 = true :=
    take_step (n := 2) (t := 180) (b := 27822) rfl rfl ArealUCore.ArealUK.chunk_13910 s11
  have s9 : leavesOK ctxLitU 285525000000 1 ((leaves.drop 27818).take 182) 575300000000 2 = true :=
    take_step (n := 2) (t := 182) (b := 27820) rfl rfl ArealUCore.ArealUK.chunk_13909 s10
  have s8 : leavesOK ctxLitU 142750000000 0 ((leaves.drop 27816).take 184) 575300000000 2 = true :=
    take_step (n := 2) (t := 184) (b := 27818) rfl rfl ArealUCore.ArealUK.chunk_13908 s9
  have s7 : leavesOK ctxLitU 142737500000 0 ((leaves.drop 27814).take 186) 575300000000 2 = true :=
    take_step (n := 2) (t := 186) (b := 27816) rfl rfl ArealUCore.ArealUK.chunk_13907 s8
  have s6 : leavesOK ctxLitU 142725000000 0 ((leaves.drop 27812).take 188) 575300000000 2 = true :=
    take_step (n := 2) (t := 188) (b := 27814) rfl rfl ArealUCore.ArealUK.chunk_13906 s7
  have s5 : leavesOK ctxLitU 285425000000 1 ((leaves.drop 27810).take 190) 575300000000 2 = true :=
    take_step (n := 2) (t := 190) (b := 27812) rfl rfl ArealUCore.ArealUK.chunk_13905 s6
  have s4 : leavesOK ctxLitU 285400000000 1 ((leaves.drop 27808).take 192) 575300000000 2 = true :=
    take_step (n := 2) (t := 192) (b := 27810) rfl rfl ArealUCore.ArealUK.chunk_13904 s5
  have s3 : leavesOK ctxLitU 285375000000 1 ((leaves.drop 27806).take 194) 575300000000 2 = true :=
    take_step (n := 2) (t := 194) (b := 27808) rfl rfl ArealUCore.ArealUK.chunk_13903 s4
  have s2 : leavesOK ctxLitU 285350000000 1 ((leaves.drop 27804).take 196) 575300000000 2 = true :=
    take_step (n := 2) (t := 196) (b := 27806) rfl rfl ArealUCore.ArealUK.chunk_13902 s3
  have s1 : leavesOK ctxLitU 142662500000 0 ((leaves.drop 27802).take 198) 575300000000 2 = true :=
    take_step (n := 2) (t := 198) (b := 27804) rfl rfl ArealUCore.ArealUK.chunk_13901 s2
  have s0 : leavesOK ctxLitU 142650000000 0 ((leaves.drop 27800).take 200) 575300000000 2 = true :=
    take_step (n := 2) (t := 200) (b := 27802) rfl rfl ArealUCore.ArealUK.chunk_13900 s1
  exact s0

end Areal.UCert

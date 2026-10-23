import ArealUK.Chunk11900
import ArealUK.Chunk11901
import ArealUK.Chunk11902
import ArealUK.Chunk11903
import ArealUK.Chunk11904
import ArealUK.Chunk11905
import ArealUK.Chunk11906
import ArealUK.Chunk11907
import ArealUK.Chunk11908
import ArealUK.Chunk11909
import ArealUK.Chunk11910
import ArealUK.Chunk11911
import ArealUK.Chunk11912
import ArealUK.Chunk11913
import ArealUK.Chunk11914
import ArealUK.Chunk11915
import ArealUK.Chunk11916
import ArealUK.Chunk11917
import ArealUK.Chunk11918
import ArealUK.Chunk11919
import ArealUK.Chunk11920
import ArealUK.Chunk11921
import ArealUK.Chunk11922
import ArealUK.Chunk11923
import ArealUK.Chunk11924
import ArealUK.Chunk11925
import ArealUK.Chunk11926
import ArealUK.Chunk11927
import ArealUK.Chunk11928
import ArealUK.Chunk11929
import ArealUK.Chunk11930
import ArealUK.Chunk11931
import ArealUK.Chunk11932
import ArealUK.Chunk11933
import ArealUK.Chunk11934
import ArealUK.Chunk11935
import ArealUK.Chunk11936
import ArealUK.Chunk11937
import ArealUK.Chunk11938
import ArealUK.Chunk11939
import ArealUK.Chunk11940
import ArealUK.Chunk11941
import ArealUK.Chunk11942
import ArealUK.Chunk11943
import ArealUK.Chunk11944
import ArealUK.Chunk11945
import ArealUK.Chunk11946
import ArealUK.Chunk11947
import ArealUK.Chunk11948
import ArealUK.Chunk11949
import ArealUK.Chunk11950
import ArealUK.Chunk11951
import ArealUK.Chunk11952
import ArealUK.Chunk11953
import ArealUK.Chunk11954
import ArealUK.Chunk11955
import ArealUK.Chunk11956
import ArealUK.Chunk11957
import ArealUK.Chunk11958
import ArealUK.Chunk11959
import ArealUK.Chunk11960
import ArealUK.Chunk11961
import ArealUK.Chunk11962
import ArealUK.Chunk11963
import ArealUK.Chunk11964
import ArealUK.Chunk11965
import ArealUK.Chunk11966
import ArealUK.Chunk11967
import ArealUK.Chunk11968
import ArealUK.Chunk11969
import ArealUK.Chunk11970
import ArealUK.Chunk11971
import ArealUK.Chunk11972
import ArealUK.Chunk11973
import ArealUK.Chunk11974
import ArealUK.Chunk11975
import ArealUK.Chunk11976
import ArealUK.Chunk11977
import ArealUK.Chunk11978
import ArealUK.Chunk11979
import ArealUK.Chunk11980
import ArealUK.Chunk11981
import ArealUK.Chunk11982
import ArealUK.Chunk11983
import ArealUK.Chunk11984
import ArealUK.Chunk11985
import ArealUK.Chunk11986
import ArealUK.Chunk11987
import ArealUK.Chunk11988
import ArealUK.Chunk11989
import ArealUK.Chunk11990
import ArealUK.Chunk11991
import ArealUK.Chunk11992
import ArealUK.Chunk11993
import ArealUK.Chunk11994
import ArealUK.Chunk11995
import ArealUK.Chunk11996
import ArealUK.Chunk11997
import ArealUK.Chunk11998
import ArealUK.Chunk11999
import Areal.UCert.LeavesKGen

/-! Group 119 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_119 : leavesOK ctxLitU 471750000000 2 ((leaves.drop 23800).take 200) 476750000000 2 = true := by
  have s99 := ArealUCore.ArealUK.chunk_11999
  have s98 : leavesOK ctxLitU 476650000000 2 ((leaves.drop 23996).take 4) 476750000000 2 = true :=
    take_step (n := 2) (t := 4) (b := 23998) rfl rfl ArealUCore.ArealUK.chunk_11998 s99
  have s97 : leavesOK ctxLitU 476600000000 2 ((leaves.drop 23994).take 6) 476750000000 2 = true :=
    take_step (n := 2) (t := 6) (b := 23996) rfl rfl ArealUCore.ArealUK.chunk_11997 s98
  have s96 : leavesOK ctxLitU 476550000000 2 ((leaves.drop 23992).take 8) 476750000000 2 = true :=
    take_step (n := 2) (t := 8) (b := 23994) rfl rfl ArealUCore.ArealUK.chunk_11996 s97
  have s95 : leavesOK ctxLitU 476500000000 2 ((leaves.drop 23990).take 10) 476750000000 2 = true :=
    take_step (n := 2) (t := 10) (b := 23992) rfl rfl ArealUCore.ArealUK.chunk_11995 s96
  have s94 : leavesOK ctxLitU 476450000000 2 ((leaves.drop 23988).take 12) 476750000000 2 = true :=
    take_step (n := 2) (t := 12) (b := 23990) rfl rfl ArealUCore.ArealUK.chunk_11994 s95
  have s93 : leavesOK ctxLitU 476400000000 2 ((leaves.drop 23986).take 14) 476750000000 2 = true :=
    take_step (n := 2) (t := 14) (b := 23988) rfl rfl ArealUCore.ArealUK.chunk_11993 s94
  have s92 : leavesOK ctxLitU 476350000000 2 ((leaves.drop 23984).take 16) 476750000000 2 = true :=
    take_step (n := 2) (t := 16) (b := 23986) rfl rfl ArealUCore.ArealUK.chunk_11992 s93
  have s91 : leavesOK ctxLitU 476300000000 2 ((leaves.drop 23982).take 18) 476750000000 2 = true :=
    take_step (n := 2) (t := 18) (b := 23984) rfl rfl ArealUCore.ArealUK.chunk_11991 s92
  have s90 : leavesOK ctxLitU 476250000000 2 ((leaves.drop 23980).take 20) 476750000000 2 = true :=
    take_step (n := 2) (t := 20) (b := 23982) rfl rfl ArealUCore.ArealUK.chunk_11990 s91
  have s89 : leavesOK ctxLitU 476200000000 2 ((leaves.drop 23978).take 22) 476750000000 2 = true :=
    take_step (n := 2) (t := 22) (b := 23980) rfl rfl ArealUCore.ArealUK.chunk_11989 s90
  have s88 : leavesOK ctxLitU 476150000000 2 ((leaves.drop 23976).take 24) 476750000000 2 = true :=
    take_step (n := 2) (t := 24) (b := 23978) rfl rfl ArealUCore.ArealUK.chunk_11988 s89
  have s87 : leavesOK ctxLitU 476100000000 2 ((leaves.drop 23974).take 26) 476750000000 2 = true :=
    take_step (n := 2) (t := 26) (b := 23976) rfl rfl ArealUCore.ArealUK.chunk_11987 s88
  have s86 : leavesOK ctxLitU 476050000000 2 ((leaves.drop 23972).take 28) 476750000000 2 = true :=
    take_step (n := 2) (t := 28) (b := 23974) rfl rfl ArealUCore.ArealUK.chunk_11986 s87
  have s85 : leavesOK ctxLitU 476000000000 2 ((leaves.drop 23970).take 30) 476750000000 2 = true :=
    take_step (n := 2) (t := 30) (b := 23972) rfl rfl ArealUCore.ArealUK.chunk_11985 s86
  have s84 : leavesOK ctxLitU 475950000000 2 ((leaves.drop 23968).take 32) 476750000000 2 = true :=
    take_step (n := 2) (t := 32) (b := 23970) rfl rfl ArealUCore.ArealUK.chunk_11984 s85
  have s83 : leavesOK ctxLitU 475900000000 2 ((leaves.drop 23966).take 34) 476750000000 2 = true :=
    take_step (n := 2) (t := 34) (b := 23968) rfl rfl ArealUCore.ArealUK.chunk_11983 s84
  have s82 : leavesOK ctxLitU 475850000000 2 ((leaves.drop 23964).take 36) 476750000000 2 = true :=
    take_step (n := 2) (t := 36) (b := 23966) rfl rfl ArealUCore.ArealUK.chunk_11982 s83
  have s81 : leavesOK ctxLitU 475800000000 2 ((leaves.drop 23962).take 38) 476750000000 2 = true :=
    take_step (n := 2) (t := 38) (b := 23964) rfl rfl ArealUCore.ArealUK.chunk_11981 s82
  have s80 : leavesOK ctxLitU 475750000000 2 ((leaves.drop 23960).take 40) 476750000000 2 = true :=
    take_step (n := 2) (t := 40) (b := 23962) rfl rfl ArealUCore.ArealUK.chunk_11980 s81
  have s79 : leavesOK ctxLitU 475700000000 2 ((leaves.drop 23958).take 42) 476750000000 2 = true :=
    take_step (n := 2) (t := 42) (b := 23960) rfl rfl ArealUCore.ArealUK.chunk_11979 s80
  have s78 : leavesOK ctxLitU 475650000000 2 ((leaves.drop 23956).take 44) 476750000000 2 = true :=
    take_step (n := 2) (t := 44) (b := 23958) rfl rfl ArealUCore.ArealUK.chunk_11978 s79
  have s77 : leavesOK ctxLitU 475600000000 2 ((leaves.drop 23954).take 46) 476750000000 2 = true :=
    take_step (n := 2) (t := 46) (b := 23956) rfl rfl ArealUCore.ArealUK.chunk_11977 s78
  have s76 : leavesOK ctxLitU 475550000000 2 ((leaves.drop 23952).take 48) 476750000000 2 = true :=
    take_step (n := 2) (t := 48) (b := 23954) rfl rfl ArealUCore.ArealUK.chunk_11976 s77
  have s75 : leavesOK ctxLitU 475500000000 2 ((leaves.drop 23950).take 50) 476750000000 2 = true :=
    take_step (n := 2) (t := 50) (b := 23952) rfl rfl ArealUCore.ArealUK.chunk_11975 s76
  have s74 : leavesOK ctxLitU 475450000000 2 ((leaves.drop 23948).take 52) 476750000000 2 = true :=
    take_step (n := 2) (t := 52) (b := 23950) rfl rfl ArealUCore.ArealUK.chunk_11974 s75
  have s73 : leavesOK ctxLitU 475400000000 2 ((leaves.drop 23946).take 54) 476750000000 2 = true :=
    take_step (n := 2) (t := 54) (b := 23948) rfl rfl ArealUCore.ArealUK.chunk_11973 s74
  have s72 : leavesOK ctxLitU 475350000000 2 ((leaves.drop 23944).take 56) 476750000000 2 = true :=
    take_step (n := 2) (t := 56) (b := 23946) rfl rfl ArealUCore.ArealUK.chunk_11972 s73
  have s71 : leavesOK ctxLitU 475300000000 2 ((leaves.drop 23942).take 58) 476750000000 2 = true :=
    take_step (n := 2) (t := 58) (b := 23944) rfl rfl ArealUCore.ArealUK.chunk_11971 s72
  have s70 : leavesOK ctxLitU 475250000000 2 ((leaves.drop 23940).take 60) 476750000000 2 = true :=
    take_step (n := 2) (t := 60) (b := 23942) rfl rfl ArealUCore.ArealUK.chunk_11970 s71
  have s69 : leavesOK ctxLitU 475200000000 2 ((leaves.drop 23938).take 62) 476750000000 2 = true :=
    take_step (n := 2) (t := 62) (b := 23940) rfl rfl ArealUCore.ArealUK.chunk_11969 s70
  have s68 : leavesOK ctxLitU 475150000000 2 ((leaves.drop 23936).take 64) 476750000000 2 = true :=
    take_step (n := 2) (t := 64) (b := 23938) rfl rfl ArealUCore.ArealUK.chunk_11968 s69
  have s67 : leavesOK ctxLitU 475100000000 2 ((leaves.drop 23934).take 66) 476750000000 2 = true :=
    take_step (n := 2) (t := 66) (b := 23936) rfl rfl ArealUCore.ArealUK.chunk_11967 s68
  have s66 : leavesOK ctxLitU 475050000000 2 ((leaves.drop 23932).take 68) 476750000000 2 = true :=
    take_step (n := 2) (t := 68) (b := 23934) rfl rfl ArealUCore.ArealUK.chunk_11966 s67
  have s65 : leavesOK ctxLitU 475000000000 2 ((leaves.drop 23930).take 70) 476750000000 2 = true :=
    take_step (n := 2) (t := 70) (b := 23932) rfl rfl ArealUCore.ArealUK.chunk_11965 s66
  have s64 : leavesOK ctxLitU 474950000000 2 ((leaves.drop 23928).take 72) 476750000000 2 = true :=
    take_step (n := 2) (t := 72) (b := 23930) rfl rfl ArealUCore.ArealUK.chunk_11964 s65
  have s63 : leavesOK ctxLitU 474900000000 2 ((leaves.drop 23926).take 74) 476750000000 2 = true :=
    take_step (n := 2) (t := 74) (b := 23928) rfl rfl ArealUCore.ArealUK.chunk_11963 s64
  have s62 : leavesOK ctxLitU 474850000000 2 ((leaves.drop 23924).take 76) 476750000000 2 = true :=
    take_step (n := 2) (t := 76) (b := 23926) rfl rfl ArealUCore.ArealUK.chunk_11962 s63
  have s61 : leavesOK ctxLitU 474800000000 2 ((leaves.drop 23922).take 78) 476750000000 2 = true :=
    take_step (n := 2) (t := 78) (b := 23924) rfl rfl ArealUCore.ArealUK.chunk_11961 s62
  have s60 : leavesOK ctxLitU 474750000000 2 ((leaves.drop 23920).take 80) 476750000000 2 = true :=
    take_step (n := 2) (t := 80) (b := 23922) rfl rfl ArealUCore.ArealUK.chunk_11960 s61
  have s59 : leavesOK ctxLitU 474700000000 2 ((leaves.drop 23918).take 82) 476750000000 2 = true :=
    take_step (n := 2) (t := 82) (b := 23920) rfl rfl ArealUCore.ArealUK.chunk_11959 s60
  have s58 : leavesOK ctxLitU 474650000000 2 ((leaves.drop 23916).take 84) 476750000000 2 = true :=
    take_step (n := 2) (t := 84) (b := 23918) rfl rfl ArealUCore.ArealUK.chunk_11958 s59
  have s57 : leavesOK ctxLitU 474600000000 2 ((leaves.drop 23914).take 86) 476750000000 2 = true :=
    take_step (n := 2) (t := 86) (b := 23916) rfl rfl ArealUCore.ArealUK.chunk_11957 s58
  have s56 : leavesOK ctxLitU 474550000000 2 ((leaves.drop 23912).take 88) 476750000000 2 = true :=
    take_step (n := 2) (t := 88) (b := 23914) rfl rfl ArealUCore.ArealUK.chunk_11956 s57
  have s55 : leavesOK ctxLitU 474500000000 2 ((leaves.drop 23910).take 90) 476750000000 2 = true :=
    take_step (n := 2) (t := 90) (b := 23912) rfl rfl ArealUCore.ArealUK.chunk_11955 s56
  have s54 : leavesOK ctxLitU 474450000000 2 ((leaves.drop 23908).take 92) 476750000000 2 = true :=
    take_step (n := 2) (t := 92) (b := 23910) rfl rfl ArealUCore.ArealUK.chunk_11954 s55
  have s53 : leavesOK ctxLitU 474400000000 2 ((leaves.drop 23906).take 94) 476750000000 2 = true :=
    take_step (n := 2) (t := 94) (b := 23908) rfl rfl ArealUCore.ArealUK.chunk_11953 s54
  have s52 : leavesOK ctxLitU 474350000000 2 ((leaves.drop 23904).take 96) 476750000000 2 = true :=
    take_step (n := 2) (t := 96) (b := 23906) rfl rfl ArealUCore.ArealUK.chunk_11952 s53
  have s51 : leavesOK ctxLitU 474300000000 2 ((leaves.drop 23902).take 98) 476750000000 2 = true :=
    take_step (n := 2) (t := 98) (b := 23904) rfl rfl ArealUCore.ArealUK.chunk_11951 s52
  have s50 : leavesOK ctxLitU 474250000000 2 ((leaves.drop 23900).take 100) 476750000000 2 = true :=
    take_step (n := 2) (t := 100) (b := 23902) rfl rfl ArealUCore.ArealUK.chunk_11950 s51
  have s49 : leavesOK ctxLitU 474200000000 2 ((leaves.drop 23898).take 102) 476750000000 2 = true :=
    take_step (n := 2) (t := 102) (b := 23900) rfl rfl ArealUCore.ArealUK.chunk_11949 s50
  have s48 : leavesOK ctxLitU 474150000000 2 ((leaves.drop 23896).take 104) 476750000000 2 = true :=
    take_step (n := 2) (t := 104) (b := 23898) rfl rfl ArealUCore.ArealUK.chunk_11948 s49
  have s47 : leavesOK ctxLitU 474100000000 2 ((leaves.drop 23894).take 106) 476750000000 2 = true :=
    take_step (n := 2) (t := 106) (b := 23896) rfl rfl ArealUCore.ArealUK.chunk_11947 s48
  have s46 : leavesOK ctxLitU 474050000000 2 ((leaves.drop 23892).take 108) 476750000000 2 = true :=
    take_step (n := 2) (t := 108) (b := 23894) rfl rfl ArealUCore.ArealUK.chunk_11946 s47
  have s45 : leavesOK ctxLitU 474000000000 2 ((leaves.drop 23890).take 110) 476750000000 2 = true :=
    take_step (n := 2) (t := 110) (b := 23892) rfl rfl ArealUCore.ArealUK.chunk_11945 s46
  have s44 : leavesOK ctxLitU 473950000000 2 ((leaves.drop 23888).take 112) 476750000000 2 = true :=
    take_step (n := 2) (t := 112) (b := 23890) rfl rfl ArealUCore.ArealUK.chunk_11944 s45
  have s43 : leavesOK ctxLitU 473900000000 2 ((leaves.drop 23886).take 114) 476750000000 2 = true :=
    take_step (n := 2) (t := 114) (b := 23888) rfl rfl ArealUCore.ArealUK.chunk_11943 s44
  have s42 : leavesOK ctxLitU 473850000000 2 ((leaves.drop 23884).take 116) 476750000000 2 = true :=
    take_step (n := 2) (t := 116) (b := 23886) rfl rfl ArealUCore.ArealUK.chunk_11942 s43
  have s41 : leavesOK ctxLitU 473800000000 2 ((leaves.drop 23882).take 118) 476750000000 2 = true :=
    take_step (n := 2) (t := 118) (b := 23884) rfl rfl ArealUCore.ArealUK.chunk_11941 s42
  have s40 : leavesOK ctxLitU 473750000000 2 ((leaves.drop 23880).take 120) 476750000000 2 = true :=
    take_step (n := 2) (t := 120) (b := 23882) rfl rfl ArealUCore.ArealUK.chunk_11940 s41
  have s39 : leavesOK ctxLitU 473700000000 2 ((leaves.drop 23878).take 122) 476750000000 2 = true :=
    take_step (n := 2) (t := 122) (b := 23880) rfl rfl ArealUCore.ArealUK.chunk_11939 s40
  have s38 : leavesOK ctxLitU 473650000000 2 ((leaves.drop 23876).take 124) 476750000000 2 = true :=
    take_step (n := 2) (t := 124) (b := 23878) rfl rfl ArealUCore.ArealUK.chunk_11938 s39
  have s37 : leavesOK ctxLitU 473600000000 2 ((leaves.drop 23874).take 126) 476750000000 2 = true :=
    take_step (n := 2) (t := 126) (b := 23876) rfl rfl ArealUCore.ArealUK.chunk_11937 s38
  have s36 : leavesOK ctxLitU 473550000000 2 ((leaves.drop 23872).take 128) 476750000000 2 = true :=
    take_step (n := 2) (t := 128) (b := 23874) rfl rfl ArealUCore.ArealUK.chunk_11936 s37
  have s35 : leavesOK ctxLitU 473500000000 2 ((leaves.drop 23870).take 130) 476750000000 2 = true :=
    take_step (n := 2) (t := 130) (b := 23872) rfl rfl ArealUCore.ArealUK.chunk_11935 s36
  have s34 : leavesOK ctxLitU 473450000000 2 ((leaves.drop 23868).take 132) 476750000000 2 = true :=
    take_step (n := 2) (t := 132) (b := 23870) rfl rfl ArealUCore.ArealUK.chunk_11934 s35
  have s33 : leavesOK ctxLitU 473400000000 2 ((leaves.drop 23866).take 134) 476750000000 2 = true :=
    take_step (n := 2) (t := 134) (b := 23868) rfl rfl ArealUCore.ArealUK.chunk_11933 s34
  have s32 : leavesOK ctxLitU 473350000000 2 ((leaves.drop 23864).take 136) 476750000000 2 = true :=
    take_step (n := 2) (t := 136) (b := 23866) rfl rfl ArealUCore.ArealUK.chunk_11932 s33
  have s31 : leavesOK ctxLitU 473300000000 2 ((leaves.drop 23862).take 138) 476750000000 2 = true :=
    take_step (n := 2) (t := 138) (b := 23864) rfl rfl ArealUCore.ArealUK.chunk_11931 s32
  have s30 : leavesOK ctxLitU 473250000000 2 ((leaves.drop 23860).take 140) 476750000000 2 = true :=
    take_step (n := 2) (t := 140) (b := 23862) rfl rfl ArealUCore.ArealUK.chunk_11930 s31
  have s29 : leavesOK ctxLitU 473200000000 2 ((leaves.drop 23858).take 142) 476750000000 2 = true :=
    take_step (n := 2) (t := 142) (b := 23860) rfl rfl ArealUCore.ArealUK.chunk_11929 s30
  have s28 : leavesOK ctxLitU 473150000000 2 ((leaves.drop 23856).take 144) 476750000000 2 = true :=
    take_step (n := 2) (t := 144) (b := 23858) rfl rfl ArealUCore.ArealUK.chunk_11928 s29
  have s27 : leavesOK ctxLitU 473100000000 2 ((leaves.drop 23854).take 146) 476750000000 2 = true :=
    take_step (n := 2) (t := 146) (b := 23856) rfl rfl ArealUCore.ArealUK.chunk_11927 s28
  have s26 : leavesOK ctxLitU 473050000000 2 ((leaves.drop 23852).take 148) 476750000000 2 = true :=
    take_step (n := 2) (t := 148) (b := 23854) rfl rfl ArealUCore.ArealUK.chunk_11926 s27
  have s25 : leavesOK ctxLitU 473000000000 2 ((leaves.drop 23850).take 150) 476750000000 2 = true :=
    take_step (n := 2) (t := 150) (b := 23852) rfl rfl ArealUCore.ArealUK.chunk_11925 s26
  have s24 : leavesOK ctxLitU 472950000000 2 ((leaves.drop 23848).take 152) 476750000000 2 = true :=
    take_step (n := 2) (t := 152) (b := 23850) rfl rfl ArealUCore.ArealUK.chunk_11924 s25
  have s23 : leavesOK ctxLitU 472900000000 2 ((leaves.drop 23846).take 154) 476750000000 2 = true :=
    take_step (n := 2) (t := 154) (b := 23848) rfl rfl ArealUCore.ArealUK.chunk_11923 s24
  have s22 : leavesOK ctxLitU 472850000000 2 ((leaves.drop 23844).take 156) 476750000000 2 = true :=
    take_step (n := 2) (t := 156) (b := 23846) rfl rfl ArealUCore.ArealUK.chunk_11922 s23
  have s21 : leavesOK ctxLitU 472800000000 2 ((leaves.drop 23842).take 158) 476750000000 2 = true :=
    take_step (n := 2) (t := 158) (b := 23844) rfl rfl ArealUCore.ArealUK.chunk_11921 s22
  have s20 : leavesOK ctxLitU 472750000000 2 ((leaves.drop 23840).take 160) 476750000000 2 = true :=
    take_step (n := 2) (t := 160) (b := 23842) rfl rfl ArealUCore.ArealUK.chunk_11920 s21
  have s19 : leavesOK ctxLitU 472700000000 2 ((leaves.drop 23838).take 162) 476750000000 2 = true :=
    take_step (n := 2) (t := 162) (b := 23840) rfl rfl ArealUCore.ArealUK.chunk_11919 s20
  have s18 : leavesOK ctxLitU 472650000000 2 ((leaves.drop 23836).take 164) 476750000000 2 = true :=
    take_step (n := 2) (t := 164) (b := 23838) rfl rfl ArealUCore.ArealUK.chunk_11918 s19
  have s17 : leavesOK ctxLitU 472600000000 2 ((leaves.drop 23834).take 166) 476750000000 2 = true :=
    take_step (n := 2) (t := 166) (b := 23836) rfl rfl ArealUCore.ArealUK.chunk_11917 s18
  have s16 : leavesOK ctxLitU 472550000000 2 ((leaves.drop 23832).take 168) 476750000000 2 = true :=
    take_step (n := 2) (t := 168) (b := 23834) rfl rfl ArealUCore.ArealUK.chunk_11916 s17
  have s15 : leavesOK ctxLitU 472500000000 2 ((leaves.drop 23830).take 170) 476750000000 2 = true :=
    take_step (n := 2) (t := 170) (b := 23832) rfl rfl ArealUCore.ArealUK.chunk_11915 s16
  have s14 : leavesOK ctxLitU 472450000000 2 ((leaves.drop 23828).take 172) 476750000000 2 = true :=
    take_step (n := 2) (t := 172) (b := 23830) rfl rfl ArealUCore.ArealUK.chunk_11914 s15
  have s13 : leavesOK ctxLitU 472400000000 2 ((leaves.drop 23826).take 174) 476750000000 2 = true :=
    take_step (n := 2) (t := 174) (b := 23828) rfl rfl ArealUCore.ArealUK.chunk_11913 s14
  have s12 : leavesOK ctxLitU 472350000000 2 ((leaves.drop 23824).take 176) 476750000000 2 = true :=
    take_step (n := 2) (t := 176) (b := 23826) rfl rfl ArealUCore.ArealUK.chunk_11912 s13
  have s11 : leavesOK ctxLitU 472300000000 2 ((leaves.drop 23822).take 178) 476750000000 2 = true :=
    take_step (n := 2) (t := 178) (b := 23824) rfl rfl ArealUCore.ArealUK.chunk_11911 s12
  have s10 : leavesOK ctxLitU 472250000000 2 ((leaves.drop 23820).take 180) 476750000000 2 = true :=
    take_step (n := 2) (t := 180) (b := 23822) rfl rfl ArealUCore.ArealUK.chunk_11910 s11
  have s9 : leavesOK ctxLitU 472200000000 2 ((leaves.drop 23818).take 182) 476750000000 2 = true :=
    take_step (n := 2) (t := 182) (b := 23820) rfl rfl ArealUCore.ArealUK.chunk_11909 s10
  have s8 : leavesOK ctxLitU 472150000000 2 ((leaves.drop 23816).take 184) 476750000000 2 = true :=
    take_step (n := 2) (t := 184) (b := 23818) rfl rfl ArealUCore.ArealUK.chunk_11908 s9
  have s7 : leavesOK ctxLitU 472100000000 2 ((leaves.drop 23814).take 186) 476750000000 2 = true :=
    take_step (n := 2) (t := 186) (b := 23816) rfl rfl ArealUCore.ArealUK.chunk_11907 s8
  have s6 : leavesOK ctxLitU 472050000000 2 ((leaves.drop 23812).take 188) 476750000000 2 = true :=
    take_step (n := 2) (t := 188) (b := 23814) rfl rfl ArealUCore.ArealUK.chunk_11906 s7
  have s5 : leavesOK ctxLitU 472000000000 2 ((leaves.drop 23810).take 190) 476750000000 2 = true :=
    take_step (n := 2) (t := 190) (b := 23812) rfl rfl ArealUCore.ArealUK.chunk_11905 s6
  have s4 : leavesOK ctxLitU 471950000000 2 ((leaves.drop 23808).take 192) 476750000000 2 = true :=
    take_step (n := 2) (t := 192) (b := 23810) rfl rfl ArealUCore.ArealUK.chunk_11904 s5
  have s3 : leavesOK ctxLitU 471900000000 2 ((leaves.drop 23806).take 194) 476750000000 2 = true :=
    take_step (n := 2) (t := 194) (b := 23808) rfl rfl ArealUCore.ArealUK.chunk_11903 s4
  have s2 : leavesOK ctxLitU 471850000000 2 ((leaves.drop 23804).take 196) 476750000000 2 = true :=
    take_step (n := 2) (t := 196) (b := 23806) rfl rfl ArealUCore.ArealUK.chunk_11902 s3
  have s1 : leavesOK ctxLitU 471800000000 2 ((leaves.drop 23802).take 198) 476750000000 2 = true :=
    take_step (n := 2) (t := 198) (b := 23804) rfl rfl ArealUCore.ArealUK.chunk_11901 s2
  have s0 : leavesOK ctxLitU 471750000000 2 ((leaves.drop 23800).take 200) 476750000000 2 = true :=
    take_step (n := 2) (t := 200) (b := 23802) rfl rfl ArealUCore.ArealUK.chunk_11900 s1
  exact s0

end Areal.UCert

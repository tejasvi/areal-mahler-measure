import ArealUK.Chunk8900
import ArealUK.Chunk8901
import ArealUK.Chunk8902
import ArealUK.Chunk8903
import ArealUK.Chunk8904
import ArealUK.Chunk8905
import ArealUK.Chunk8906
import ArealUK.Chunk8907
import ArealUK.Chunk8908
import ArealUK.Chunk8909
import ArealUK.Chunk8910
import ArealUK.Chunk8911
import ArealUK.Chunk8912
import ArealUK.Chunk8913
import ArealUK.Chunk8914
import ArealUK.Chunk8915
import ArealUK.Chunk8916
import ArealUK.Chunk8917
import ArealUK.Chunk8918
import ArealUK.Chunk8919
import ArealUK.Chunk8920
import ArealUK.Chunk8921
import ArealUK.Chunk8922
import ArealUK.Chunk8923
import ArealUK.Chunk8924
import ArealUK.Chunk8925
import ArealUK.Chunk8926
import ArealUK.Chunk8927
import ArealUK.Chunk8928
import ArealUK.Chunk8929
import ArealUK.Chunk8930
import ArealUK.Chunk8931
import ArealUK.Chunk8932
import ArealUK.Chunk8933
import ArealUK.Chunk8934
import ArealUK.Chunk8935
import ArealUK.Chunk8936
import ArealUK.Chunk8937
import ArealUK.Chunk8938
import ArealUK.Chunk8939
import ArealUK.Chunk8940
import ArealUK.Chunk8941
import ArealUK.Chunk8942
import ArealUK.Chunk8943
import ArealUK.Chunk8944
import ArealUK.Chunk8945
import ArealUK.Chunk8946
import ArealUK.Chunk8947
import ArealUK.Chunk8948
import ArealUK.Chunk8949
import ArealUK.Chunk8950
import ArealUK.Chunk8951
import ArealUK.Chunk8952
import ArealUK.Chunk8953
import ArealUK.Chunk8954
import ArealUK.Chunk8955
import ArealUK.Chunk8956
import ArealUK.Chunk8957
import ArealUK.Chunk8958
import ArealUK.Chunk8959
import ArealUK.Chunk8960
import ArealUK.Chunk8961
import ArealUK.Chunk8962
import ArealUK.Chunk8963
import ArealUK.Chunk8964
import ArealUK.Chunk8965
import ArealUK.Chunk8966
import ArealUK.Chunk8967
import ArealUK.Chunk8968
import ArealUK.Chunk8969
import ArealUK.Chunk8970
import ArealUK.Chunk8971
import ArealUK.Chunk8972
import ArealUK.Chunk8973
import ArealUK.Chunk8974
import ArealUK.Chunk8975
import ArealUK.Chunk8976
import ArealUK.Chunk8977
import ArealUK.Chunk8978
import ArealUK.Chunk8979
import ArealUK.Chunk8980
import ArealUK.Chunk8981
import ArealUK.Chunk8982
import ArealUK.Chunk8983
import ArealUK.Chunk8984
import ArealUK.Chunk8985
import ArealUK.Chunk8986
import ArealUK.Chunk8987
import ArealUK.Chunk8988
import ArealUK.Chunk8989
import ArealUK.Chunk8990
import ArealUK.Chunk8991
import ArealUK.Chunk8992
import ArealUK.Chunk8993
import ArealUK.Chunk8994
import ArealUK.Chunk8995
import ArealUK.Chunk8996
import ArealUK.Chunk8997
import ArealUK.Chunk8998
import ArealUK.Chunk8999
import Areal.UCert.LeavesKGen

/-! Group 89 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_89 : leavesOK ctxLitU 73150000000 0 ((leaves.drop 17800).take 200) 296400000000 2 = true := by
  have s99 := ArealUCore.ArealUK.chunk_8999
  have s98 : leavesOK ctxLitU 296300000000 2 ((leaves.drop 17996).take 4) 296400000000 2 = true :=
    take_step (n := 2) (t := 4) (b := 17998) rfl rfl ArealUCore.ArealUK.chunk_8998 s99
  have s97 : leavesOK ctxLitU 296250000000 2 ((leaves.drop 17994).take 6) 296400000000 2 = true :=
    take_step (n := 2) (t := 6) (b := 17996) rfl rfl ArealUCore.ArealUK.chunk_8997 s98
  have s96 : leavesOK ctxLitU 296200000000 2 ((leaves.drop 17992).take 8) 296400000000 2 = true :=
    take_step (n := 2) (t := 8) (b := 17994) rfl rfl ArealUCore.ArealUK.chunk_8996 s97
  have s95 : leavesOK ctxLitU 296150000000 2 ((leaves.drop 17990).take 10) 296400000000 2 = true :=
    take_step (n := 2) (t := 10) (b := 17992) rfl rfl ArealUCore.ArealUK.chunk_8995 s96
  have s94 : leavesOK ctxLitU 296100000000 2 ((leaves.drop 17988).take 12) 296400000000 2 = true :=
    take_step (n := 2) (t := 12) (b := 17990) rfl rfl ArealUCore.ArealUK.chunk_8994 s95
  have s93 : leavesOK ctxLitU 296050000000 2 ((leaves.drop 17986).take 14) 296400000000 2 = true :=
    take_step (n := 2) (t := 14) (b := 17988) rfl rfl ArealUCore.ArealUK.chunk_8993 s94
  have s92 : leavesOK ctxLitU 296000000000 2 ((leaves.drop 17984).take 16) 296400000000 2 = true :=
    take_step (n := 2) (t := 16) (b := 17986) rfl rfl ArealUCore.ArealUK.chunk_8992 s93
  have s91 : leavesOK ctxLitU 295950000000 2 ((leaves.drop 17982).take 18) 296400000000 2 = true :=
    take_step (n := 2) (t := 18) (b := 17984) rfl rfl ArealUCore.ArealUK.chunk_8991 s92
  have s90 : leavesOK ctxLitU 295900000000 2 ((leaves.drop 17980).take 20) 296400000000 2 = true :=
    take_step (n := 2) (t := 20) (b := 17982) rfl rfl ArealUCore.ArealUK.chunk_8990 s91
  have s89 : leavesOK ctxLitU 295850000000 2 ((leaves.drop 17978).take 22) 296400000000 2 = true :=
    take_step (n := 2) (t := 22) (b := 17980) rfl rfl ArealUCore.ArealUK.chunk_8989 s90
  have s88 : leavesOK ctxLitU 295800000000 2 ((leaves.drop 17976).take 24) 296400000000 2 = true :=
    take_step (n := 2) (t := 24) (b := 17978) rfl rfl ArealUCore.ArealUK.chunk_8988 s89
  have s87 : leavesOK ctxLitU 295750000000 2 ((leaves.drop 17974).take 26) 296400000000 2 = true :=
    take_step (n := 2) (t := 26) (b := 17976) rfl rfl ArealUCore.ArealUK.chunk_8987 s88
  have s86 : leavesOK ctxLitU 295700000000 2 ((leaves.drop 17972).take 28) 296400000000 2 = true :=
    take_step (n := 2) (t := 28) (b := 17974) rfl rfl ArealUCore.ArealUK.chunk_8986 s87
  have s85 : leavesOK ctxLitU 295650000000 2 ((leaves.drop 17970).take 30) 296400000000 2 = true :=
    take_step (n := 2) (t := 30) (b := 17972) rfl rfl ArealUCore.ArealUK.chunk_8985 s86
  have s84 : leavesOK ctxLitU 295600000000 2 ((leaves.drop 17968).take 32) 296400000000 2 = true :=
    take_step (n := 2) (t := 32) (b := 17970) rfl rfl ArealUCore.ArealUK.chunk_8984 s85
  have s83 : leavesOK ctxLitU 295550000000 2 ((leaves.drop 17966).take 34) 296400000000 2 = true :=
    take_step (n := 2) (t := 34) (b := 17968) rfl rfl ArealUCore.ArealUK.chunk_8983 s84
  have s82 : leavesOK ctxLitU 295500000000 2 ((leaves.drop 17964).take 36) 296400000000 2 = true :=
    take_step (n := 2) (t := 36) (b := 17966) rfl rfl ArealUCore.ArealUK.chunk_8982 s83
  have s81 : leavesOK ctxLitU 295450000000 2 ((leaves.drop 17962).take 38) 296400000000 2 = true :=
    take_step (n := 2) (t := 38) (b := 17964) rfl rfl ArealUCore.ArealUK.chunk_8981 s82
  have s80 : leavesOK ctxLitU 295400000000 2 ((leaves.drop 17960).take 40) 296400000000 2 = true :=
    take_step (n := 2) (t := 40) (b := 17962) rfl rfl ArealUCore.ArealUK.chunk_8980 s81
  have s79 : leavesOK ctxLitU 295350000000 2 ((leaves.drop 17958).take 42) 296400000000 2 = true :=
    take_step (n := 2) (t := 42) (b := 17960) rfl rfl ArealUCore.ArealUK.chunk_8979 s80
  have s78 : leavesOK ctxLitU 295300000000 2 ((leaves.drop 17956).take 44) 296400000000 2 = true :=
    take_step (n := 2) (t := 44) (b := 17958) rfl rfl ArealUCore.ArealUK.chunk_8978 s79
  have s77 : leavesOK ctxLitU 590550000000 3 ((leaves.drop 17954).take 46) 296400000000 2 = true :=
    take_step (n := 2) (t := 46) (b := 17956) rfl rfl ArealUCore.ArealUK.chunk_8977 s78
  have s76 : leavesOK ctxLitU 295225000000 2 ((leaves.drop 17952).take 48) 296400000000 2 = true :=
    take_step (n := 2) (t := 48) (b := 17954) rfl rfl ArealUCore.ArealUK.chunk_8976 s77
  have s75 : leavesOK ctxLitU 295175000000 2 ((leaves.drop 17950).take 50) 296400000000 2 = true :=
    take_step (n := 2) (t := 50) (b := 17952) rfl rfl ArealUCore.ArealUK.chunk_8975 s76
  have s74 : leavesOK ctxLitU 295125000000 2 ((leaves.drop 17948).take 52) 296400000000 2 = true :=
    take_step (n := 2) (t := 52) (b := 17950) rfl rfl ArealUCore.ArealUK.chunk_8974 s75
  have s73 : leavesOK ctxLitU 590200000000 3 ((leaves.drop 17946).take 54) 296400000000 2 = true :=
    take_step (n := 2) (t := 54) (b := 17948) rfl rfl ArealUCore.ArealUK.chunk_8973 s74
  have s72 : leavesOK ctxLitU 295050000000 2 ((leaves.drop 17944).take 56) 296400000000 2 = true :=
    take_step (n := 2) (t := 56) (b := 17946) rfl rfl ArealUCore.ArealUK.chunk_8972 s73
  have s71 : leavesOK ctxLitU 295000000000 2 ((leaves.drop 17942).take 58) 296400000000 2 = true :=
    take_step (n := 2) (t := 58) (b := 17944) rfl rfl ArealUCore.ArealUK.chunk_8971 s72
  have s70 : leavesOK ctxLitU 294950000000 2 ((leaves.drop 17940).take 60) 296400000000 2 = true :=
    take_step (n := 2) (t := 60) (b := 17942) rfl rfl ArealUCore.ArealUK.chunk_8970 s71
  have s69 : leavesOK ctxLitU 294900000000 2 ((leaves.drop 17938).take 62) 296400000000 2 = true :=
    take_step (n := 2) (t := 62) (b := 17940) rfl rfl ArealUCore.ArealUK.chunk_8969 s70
  have s68 : leavesOK ctxLitU 589750000000 3 ((leaves.drop 17936).take 64) 296400000000 2 = true :=
    take_step (n := 2) (t := 64) (b := 17938) rfl rfl ArealUCore.ArealUK.chunk_8968 s69
  have s67 : leavesOK ctxLitU 294825000000 2 ((leaves.drop 17934).take 66) 296400000000 2 = true :=
    take_step (n := 2) (t := 66) (b := 17936) rfl rfl ArealUCore.ArealUK.chunk_8967 s68
  have s66 : leavesOK ctxLitU 294775000000 2 ((leaves.drop 17932).take 68) 296400000000 2 = true :=
    take_step (n := 2) (t := 68) (b := 17934) rfl rfl ArealUCore.ArealUK.chunk_8966 s67
  have s65 : leavesOK ctxLitU 294725000000 2 ((leaves.drop 17930).take 70) 296400000000 2 = true :=
    take_step (n := 2) (t := 70) (b := 17932) rfl rfl ArealUCore.ArealUK.chunk_8965 s66
  have s64 : leavesOK ctxLitU 294675000000 2 ((leaves.drop 17928).take 72) 296400000000 2 = true :=
    take_step (n := 2) (t := 72) (b := 17930) rfl rfl ArealUCore.ArealUK.chunk_8964 s65
  have s63 : leavesOK ctxLitU 294625000000 2 ((leaves.drop 17926).take 74) 296400000000 2 = true :=
    take_step (n := 2) (t := 74) (b := 17928) rfl rfl ArealUCore.ArealUK.chunk_8963 s64
  have s62 : leavesOK ctxLitU 294575000000 2 ((leaves.drop 17924).take 76) 296400000000 2 = true :=
    take_step (n := 2) (t := 76) (b := 17926) rfl rfl ArealUCore.ArealUK.chunk_8962 s63
  have s61 : leavesOK ctxLitU 294525000000 2 ((leaves.drop 17922).take 78) 296400000000 2 = true :=
    take_step (n := 2) (t := 78) (b := 17924) rfl rfl ArealUCore.ArealUK.chunk_8961 s62
  have s60 : leavesOK ctxLitU 294475000000 2 ((leaves.drop 17920).take 80) 296400000000 2 = true :=
    take_step (n := 2) (t := 80) (b := 17922) rfl rfl ArealUCore.ArealUK.chunk_8960 s61
  have s59 : leavesOK ctxLitU 294425000000 2 ((leaves.drop 17918).take 82) 296400000000 2 = true :=
    take_step (n := 2) (t := 82) (b := 17920) rfl rfl ArealUCore.ArealUK.chunk_8959 s60
  have s58 : leavesOK ctxLitU 294375000000 2 ((leaves.drop 17916).take 84) 296400000000 2 = true :=
    take_step (n := 2) (t := 84) (b := 17918) rfl rfl ArealUCore.ArealUK.chunk_8958 s59
  have s57 : leavesOK ctxLitU 294325000000 2 ((leaves.drop 17914).take 86) 296400000000 2 = true :=
    take_step (n := 2) (t := 86) (b := 17916) rfl rfl ArealUCore.ArealUK.chunk_8957 s58
  have s56 : leavesOK ctxLitU 294275000000 2 ((leaves.drop 17912).take 88) 296400000000 2 = true :=
    take_step (n := 2) (t := 88) (b := 17914) rfl rfl ArealUCore.ArealUK.chunk_8956 s57
  have s55 : leavesOK ctxLitU 294225000000 2 ((leaves.drop 17910).take 90) 296400000000 2 = true :=
    take_step (n := 2) (t := 90) (b := 17912) rfl rfl ArealUCore.ArealUK.chunk_8955 s56
  have s54 : leavesOK ctxLitU 294175000000 2 ((leaves.drop 17908).take 92) 296400000000 2 = true :=
    take_step (n := 2) (t := 92) (b := 17910) rfl rfl ArealUCore.ArealUK.chunk_8954 s55
  have s53 : leavesOK ctxLitU 294125000000 2 ((leaves.drop 17906).take 94) 296400000000 2 = true :=
    take_step (n := 2) (t := 94) (b := 17908) rfl rfl ArealUCore.ArealUK.chunk_8953 s54
  have s52 : leavesOK ctxLitU 588200000000 3 ((leaves.drop 17904).take 96) 296400000000 2 = true :=
    take_step (n := 2) (t := 96) (b := 17906) rfl rfl ArealUCore.ArealUK.chunk_8952 s53
  have s51 : leavesOK ctxLitU 588150000000 3 ((leaves.drop 17902).take 98) 296400000000 2 = true :=
    take_step (n := 2) (t := 98) (b := 17904) rfl rfl ArealUCore.ArealUK.chunk_8951 s52
  have s50 : leavesOK ctxLitU 588100000000 3 ((leaves.drop 17900).take 100) 296400000000 2 = true :=
    take_step (n := 2) (t := 100) (b := 17902) rfl rfl ArealUCore.ArealUK.chunk_8950 s51
  have s49 : leavesOK ctxLitU 588050000000 3 ((leaves.drop 17898).take 102) 296400000000 2 = true :=
    take_step (n := 2) (t := 102) (b := 17900) rfl rfl ArealUCore.ArealUK.chunk_8949 s50
  have s48 : leavesOK ctxLitU 588000000000 3 ((leaves.drop 17896).take 104) 296400000000 2 = true :=
    take_step (n := 2) (t := 104) (b := 17898) rfl rfl ArealUCore.ArealUK.chunk_8948 s49
  have s47 : leavesOK ctxLitU 587950000000 3 ((leaves.drop 17894).take 106) 296400000000 2 = true :=
    take_step (n := 2) (t := 106) (b := 17896) rfl rfl ArealUCore.ArealUK.chunk_8947 s48
  have s46 : leavesOK ctxLitU 587900000000 3 ((leaves.drop 17892).take 108) 296400000000 2 = true :=
    take_step (n := 2) (t := 108) (b := 17894) rfl rfl ArealUCore.ArealUK.chunk_8946 s47
  have s45 : leavesOK ctxLitU 587850000000 3 ((leaves.drop 17890).take 110) 296400000000 2 = true :=
    take_step (n := 2) (t := 110) (b := 17892) rfl rfl ArealUCore.ArealUK.chunk_8945 s46
  have s44 : leavesOK ctxLitU 587800000000 3 ((leaves.drop 17888).take 112) 296400000000 2 = true :=
    take_step (n := 2) (t := 112) (b := 17890) rfl rfl ArealUCore.ArealUK.chunk_8944 s45
  have s43 : leavesOK ctxLitU 587750000000 3 ((leaves.drop 17886).take 114) 296400000000 2 = true :=
    take_step (n := 2) (t := 114) (b := 17888) rfl rfl ArealUCore.ArealUK.chunk_8943 s44
  have s42 : leavesOK ctxLitU 293825000000 2 ((leaves.drop 17884).take 116) 296400000000 2 = true :=
    take_step (n := 2) (t := 116) (b := 17886) rfl rfl ArealUCore.ArealUK.chunk_8942 s43
  have s41 : leavesOK ctxLitU 293775000000 2 ((leaves.drop 17882).take 118) 296400000000 2 = true :=
    take_step (n := 2) (t := 118) (b := 17884) rfl rfl ArealUCore.ArealUK.chunk_8941 s42
  have s40 : leavesOK ctxLitU 587475000000 3 ((leaves.drop 17880).take 120) 296400000000 2 = true :=
    take_step (n := 2) (t := 120) (b := 17882) rfl rfl ArealUCore.ArealUK.chunk_8940 s41
  have s39 : leavesOK ctxLitU 587425000000 3 ((leaves.drop 17878).take 122) 296400000000 2 = true :=
    take_step (n := 2) (t := 122) (b := 17880) rfl rfl ArealUCore.ArealUK.chunk_8939 s40
  have s38 : leavesOK ctxLitU 587375000000 3 ((leaves.drop 17876).take 124) 296400000000 2 = true :=
    take_step (n := 2) (t := 124) (b := 17878) rfl rfl ArealUCore.ArealUK.chunk_8938 s39
  have s37 : leavesOK ctxLitU 587325000000 3 ((leaves.drop 17874).take 126) 296400000000 2 = true :=
    take_step (n := 2) (t := 126) (b := 17876) rfl rfl ArealUCore.ArealUK.chunk_8937 s38
  have s36 : leavesOK ctxLitU 587275000000 3 ((leaves.drop 17872).take 128) 296400000000 2 = true :=
    take_step (n := 2) (t := 128) (b := 17874) rfl rfl ArealUCore.ArealUK.chunk_8936 s37
  have s35 : leavesOK ctxLitU 587225000000 3 ((leaves.drop 17870).take 130) 296400000000 2 = true :=
    take_step (n := 2) (t := 130) (b := 17872) rfl rfl ArealUCore.ArealUK.chunk_8935 s36
  have s34 : leavesOK ctxLitU 587175000000 3 ((leaves.drop 17868).take 132) 296400000000 2 = true :=
    take_step (n := 2) (t := 132) (b := 17870) rfl rfl ArealUCore.ArealUK.chunk_8934 s35
  have s33 : leavesOK ctxLitU 587125000000 3 ((leaves.drop 17866).take 134) 296400000000 2 = true :=
    take_step (n := 2) (t := 134) (b := 17868) rfl rfl ArealUCore.ArealUK.chunk_8933 s34
  have s32 : leavesOK ctxLitU 587075000000 3 ((leaves.drop 17864).take 136) 296400000000 2 = true :=
    take_step (n := 2) (t := 136) (b := 17866) rfl rfl ArealUCore.ArealUK.chunk_8932 s33
  have s31 : leavesOK ctxLitU 587025000000 3 ((leaves.drop 17862).take 138) 296400000000 2 = true :=
    take_step (n := 2) (t := 138) (b := 17864) rfl rfl ArealUCore.ArealUK.chunk_8931 s32
  have s30 : leavesOK ctxLitU 586975000000 3 ((leaves.drop 17860).take 140) 296400000000 2 = true :=
    take_step (n := 2) (t := 140) (b := 17862) rfl rfl ArealUCore.ArealUK.chunk_8930 s31
  have s29 : leavesOK ctxLitU 586925000000 3 ((leaves.drop 17858).take 142) 296400000000 2 = true :=
    take_step (n := 2) (t := 142) (b := 17860) rfl rfl ArealUCore.ArealUK.chunk_8929 s30
  have s28 : leavesOK ctxLitU 293425000000 2 ((leaves.drop 17856).take 144) 296400000000 2 = true :=
    take_step (n := 2) (t := 144) (b := 17858) rfl rfl ArealUCore.ArealUK.chunk_8928 s29
  have s27 : leavesOK ctxLitU 293375000000 2 ((leaves.drop 17854).take 146) 296400000000 2 = true :=
    take_step (n := 2) (t := 146) (b := 17856) rfl rfl ArealUCore.ArealUK.chunk_8927 s28
  have s26 : leavesOK ctxLitU 586675000000 3 ((leaves.drop 17852).take 148) 296400000000 2 = true :=
    take_step (n := 2) (t := 148) (b := 17854) rfl rfl ArealUCore.ArealUK.chunk_8926 s27
  have s25 : leavesOK ctxLitU 586625000000 3 ((leaves.drop 17850).take 150) 296400000000 2 = true :=
    take_step (n := 2) (t := 150) (b := 17852) rfl rfl ArealUCore.ArealUK.chunk_8925 s26
  have s24 : leavesOK ctxLitU 586575000000 3 ((leaves.drop 17848).take 152) 296400000000 2 = true :=
    take_step (n := 2) (t := 152) (b := 17850) rfl rfl ArealUCore.ArealUK.chunk_8924 s25
  have s23 : leavesOK ctxLitU 586525000000 3 ((leaves.drop 17846).take 154) 296400000000 2 = true :=
    take_step (n := 2) (t := 154) (b := 17848) rfl rfl ArealUCore.ArealUK.chunk_8923 s24
  have s22 : leavesOK ctxLitU 586475000000 3 ((leaves.drop 17844).take 156) 296400000000 2 = true :=
    take_step (n := 2) (t := 156) (b := 17846) rfl rfl ArealUCore.ArealUK.chunk_8922 s23
  have s21 : leavesOK ctxLitU 586425000000 3 ((leaves.drop 17842).take 158) 296400000000 2 = true :=
    take_step (n := 2) (t := 158) (b := 17844) rfl rfl ArealUCore.ArealUK.chunk_8921 s22
  have s20 : leavesOK ctxLitU 586375000000 3 ((leaves.drop 17840).take 160) 296400000000 2 = true :=
    take_step (n := 2) (t := 160) (b := 17842) rfl rfl ArealUCore.ArealUK.chunk_8920 s21
  have s19 : leavesOK ctxLitU 586325000000 3 ((leaves.drop 17838).take 162) 296400000000 2 = true :=
    take_step (n := 2) (t := 162) (b := 17840) rfl rfl ArealUCore.ArealUK.chunk_8919 s20
  have s18 : leavesOK ctxLitU 586275000000 3 ((leaves.drop 17836).take 164) 296400000000 2 = true :=
    take_step (n := 2) (t := 164) (b := 17838) rfl rfl ArealUCore.ArealUK.chunk_8918 s19
  have s17 : leavesOK ctxLitU 586225000000 3 ((leaves.drop 17834).take 166) 296400000000 2 = true :=
    take_step (n := 2) (t := 166) (b := 17836) rfl rfl ArealUCore.ArealUK.chunk_8917 s18
  have s16 : leavesOK ctxLitU 586175000000 3 ((leaves.drop 17832).take 168) 296400000000 2 = true :=
    take_step (n := 2) (t := 168) (b := 17834) rfl rfl ArealUCore.ArealUK.chunk_8916 s17
  have s15 : leavesOK ctxLitU 586125000000 3 ((leaves.drop 17830).take 170) 296400000000 2 = true :=
    take_step (n := 2) (t := 170) (b := 17832) rfl rfl ArealUCore.ArealUK.chunk_8915 s16
  have s14 : leavesOK ctxLitU 586075000000 3 ((leaves.drop 17828).take 172) 296400000000 2 = true :=
    take_step (n := 2) (t := 172) (b := 17830) rfl rfl ArealUCore.ArealUK.chunk_8914 s15
  have s13 : leavesOK ctxLitU 586025000000 3 ((leaves.drop 17826).take 174) 296400000000 2 = true :=
    take_step (n := 2) (t := 174) (b := 17828) rfl rfl ArealUCore.ArealUK.chunk_8913 s14
  have s12 : leavesOK ctxLitU 585975000000 3 ((leaves.drop 17824).take 176) 296400000000 2 = true :=
    take_step (n := 2) (t := 176) (b := 17826) rfl rfl ArealUCore.ArealUK.chunk_8912 s13
  have s11 : leavesOK ctxLitU 585925000000 3 ((leaves.drop 17822).take 178) 296400000000 2 = true :=
    take_step (n := 2) (t := 178) (b := 17824) rfl rfl ArealUCore.ArealUK.chunk_8911 s12
  have s10 : leavesOK ctxLitU 585875000000 3 ((leaves.drop 17820).take 180) 296400000000 2 = true :=
    take_step (n := 2) (t := 180) (b := 17822) rfl rfl ArealUCore.ArealUK.chunk_8910 s11
  have s9 : leavesOK ctxLitU 585825000000 3 ((leaves.drop 17818).take 182) 296400000000 2 = true :=
    take_step (n := 2) (t := 182) (b := 17820) rfl rfl ArealUCore.ArealUK.chunk_8909 s10
  have s8 : leavesOK ctxLitU 146437500000 1 ((leaves.drop 17816).take 184) 296400000000 2 = true :=
    take_step (n := 2) (t := 184) (b := 17818) rfl rfl ArealUCore.ArealUK.chunk_8908 s9
  have s7 : leavesOK ctxLitU 146412500000 1 ((leaves.drop 17814).take 186) 296400000000 2 = true :=
    take_step (n := 2) (t := 186) (b := 17816) rfl rfl ArealUCore.ArealUK.chunk_8907 s8
  have s6 : leavesOK ctxLitU 73193750000 0 ((leaves.drop 17812).take 188) 296400000000 2 = true :=
    take_step (n := 2) (t := 188) (b := 17814) rfl rfl ArealUCore.ArealUK.chunk_8906 s7
  have s5 : leavesOK ctxLitU 292756250000 2 ((leaves.drop 17810).take 190) 296400000000 2 = true :=
    take_step (n := 2) (t := 190) (b := 17812) rfl rfl ArealUCore.ArealUK.chunk_8905 s6
  have s4 : leavesOK ctxLitU 585500000000 3 ((leaves.drop 17808).take 192) 296400000000 2 = true :=
    take_step (n := 2) (t := 192) (b := 17810) rfl rfl ArealUCore.ArealUK.chunk_8904 s5
  have s3 : leavesOK ctxLitU 292737500000 2 ((leaves.drop 17806).take 194) 296400000000 2 = true :=
    take_step (n := 2) (t := 194) (b := 17808) rfl rfl ArealUCore.ArealUK.chunk_8903 s4
  have s2 : leavesOK ctxLitU 73175000000 0 ((leaves.drop 17804).take 196) 296400000000 2 = true :=
    take_step (n := 2) (t := 196) (b := 17806) rfl rfl ArealUCore.ArealUK.chunk_8902 s3
  have s1 : leavesOK ctxLitU 73162500000 0 ((leaves.drop 17802).take 198) 296400000000 2 = true :=
    take_step (n := 2) (t := 198) (b := 17804) rfl rfl ArealUCore.ArealUK.chunk_8901 s2
  have s0 : leavesOK ctxLitU 73150000000 0 ((leaves.drop 17800).take 200) 296400000000 2 = true :=
    take_step (n := 2) (t := 200) (b := 17802) rfl rfl ArealUCore.ArealUK.chunk_8900 s1
  exact s0

end Areal.UCert

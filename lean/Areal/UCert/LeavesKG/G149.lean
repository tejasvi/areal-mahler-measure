import ArealUK.Chunk14900
import ArealUK.Chunk14901
import ArealUK.Chunk14902
import ArealUK.Chunk14903
import ArealUK.Chunk14904
import ArealUK.Chunk14905
import ArealUK.Chunk14906
import ArealUK.Chunk14907
import ArealUK.Chunk14908
import ArealUK.Chunk14909
import ArealUK.Chunk14910
import ArealUK.Chunk14911
import ArealUK.Chunk14912
import ArealUK.Chunk14913
import ArealUK.Chunk14914
import ArealUK.Chunk14915
import ArealUK.Chunk14916
import ArealUK.Chunk14917
import ArealUK.Chunk14918
import ArealUK.Chunk14919
import ArealUK.Chunk14920
import ArealUK.Chunk14921
import ArealUK.Chunk14922
import ArealUK.Chunk14923
import ArealUK.Chunk14924
import ArealUK.Chunk14925
import ArealUK.Chunk14926
import ArealUK.Chunk14927
import ArealUK.Chunk14928
import ArealUK.Chunk14929
import ArealUK.Chunk14930
import ArealUK.Chunk14931
import ArealUK.Chunk14932
import ArealUK.Chunk14933
import ArealUK.Chunk14934
import ArealUK.Chunk14935
import ArealUK.Chunk14936
import ArealUK.Chunk14937
import ArealUK.Chunk14938
import ArealUK.Chunk14939
import ArealUK.Chunk14940
import ArealUK.Chunk14941
import ArealUK.Chunk14942
import ArealUK.Chunk14943
import ArealUK.Chunk14944
import ArealUK.Chunk14945
import ArealUK.Chunk14946
import ArealUK.Chunk14947
import ArealUK.Chunk14948
import ArealUK.Chunk14949
import ArealUK.Chunk14950
import ArealUK.Chunk14951
import ArealUK.Chunk14952
import ArealUK.Chunk14953
import ArealUK.Chunk14954
import ArealUK.Chunk14955
import ArealUK.Chunk14956
import ArealUK.Chunk14957
import ArealUK.Chunk14958
import ArealUK.Chunk14959
import ArealUK.Chunk14960
import ArealUK.Chunk14961
import ArealUK.Chunk14962
import ArealUK.Chunk14963
import ArealUK.Chunk14964
import ArealUK.Chunk14965
import ArealUK.Chunk14966
import ArealUK.Chunk14967
import ArealUK.Chunk14968
import ArealUK.Chunk14969
import ArealUK.Chunk14970
import ArealUK.Chunk14971
import ArealUK.Chunk14972
import ArealUK.Chunk14973
import ArealUK.Chunk14974
import ArealUK.Chunk14975
import ArealUK.Chunk14976
import ArealUK.Chunk14977
import ArealUK.Chunk14978
import ArealUK.Chunk14979
import ArealUK.Chunk14980
import ArealUK.Chunk14981
import ArealUK.Chunk14982
import ArealUK.Chunk14983
import ArealUK.Chunk14984
import ArealUK.Chunk14985
import ArealUK.Chunk14986
import ArealUK.Chunk14987
import ArealUK.Chunk14988
import ArealUK.Chunk14989
import ArealUK.Chunk14990
import ArealUK.Chunk14991
import ArealUK.Chunk14992
import ArealUK.Chunk14993
import ArealUK.Chunk14994
import ArealUK.Chunk14995
import ArealUK.Chunk14996
import ArealUK.Chunk14997
import ArealUK.Chunk14998
import ArealUK.Chunk14999
import Areal.UCert.LeavesKGen

/-! Group 149 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_149 : leavesOK ctxLitU 155056250000 0 ((leaves.drop 29800).take 200) 156425000000 0 = true := by
  have s99 := ArealUCore.ArealUK.chunk_14999
  have s98 : leavesOK ctxLitU 312800000000 1 ((leaves.drop 29996).take 4) 156425000000 0 = true :=
    take_step (n := 2) (t := 4) (b := 29998) rfl rfl ArealUCore.ArealUK.chunk_14998 s99
  have s97 : leavesOK ctxLitU 312762500000 1 ((leaves.drop 29994).take 6) 156425000000 0 = true :=
    take_step (n := 2) (t := 6) (b := 29996) rfl rfl ArealUCore.ArealUK.chunk_14997 s98
  have s96 : leavesOK ctxLitU 156368750000 0 ((leaves.drop 29992).take 8) 156425000000 0 = true :=
    take_step (n := 2) (t := 8) (b := 29994) rfl rfl ArealUCore.ArealUK.chunk_14996 s97
  have s95 : leavesOK ctxLitU 156356250000 0 ((leaves.drop 29990).take 10) 156425000000 0 = true :=
    take_step (n := 2) (t := 10) (b := 29992) rfl rfl ArealUCore.ArealUK.chunk_14995 s96
  have s94 : leavesOK ctxLitU 156343750000 0 ((leaves.drop 29988).take 12) 156425000000 0 = true :=
    take_step (n := 2) (t := 12) (b := 29990) rfl rfl ArealUCore.ArealUK.chunk_14994 s95
  have s93 : leavesOK ctxLitU 156331250000 0 ((leaves.drop 29986).take 14) 156425000000 0 = true :=
    take_step (n := 2) (t := 14) (b := 29988) rfl rfl ArealUCore.ArealUK.chunk_14993 s94
  have s92 : leavesOK ctxLitU 312637500000 1 ((leaves.drop 29984).take 16) 156425000000 0 = true :=
    take_step (n := 2) (t := 16) (b := 29986) rfl rfl ArealUCore.ArealUK.chunk_14992 s93
  have s91 : leavesOK ctxLitU 312612500000 1 ((leaves.drop 29982).take 18) 156425000000 0 = true :=
    take_step (n := 2) (t := 18) (b := 29984) rfl rfl ArealUCore.ArealUK.chunk_14991 s92
  have s90 : leavesOK ctxLitU 312587500000 1 ((leaves.drop 29980).take 20) 156425000000 0 = true :=
    take_step (n := 2) (t := 20) (b := 29982) rfl rfl ArealUCore.ArealUK.chunk_14990 s91
  have s89 : leavesOK ctxLitU 156275000000 0 ((leaves.drop 29978).take 22) 156425000000 0 = true :=
    take_step (n := 2) (t := 22) (b := 29980) rfl rfl ArealUCore.ArealUK.chunk_14989 s90
  have s88 : leavesOK ctxLitU 156262500000 0 ((leaves.drop 29976).take 24) 156425000000 0 = true :=
    take_step (n := 2) (t := 24) (b := 29978) rfl rfl ArealUCore.ArealUK.chunk_14988 s89
  have s87 : leavesOK ctxLitU 156250000000 0 ((leaves.drop 29974).take 26) 156425000000 0 = true :=
    take_step (n := 2) (t := 26) (b := 29976) rfl rfl ArealUCore.ArealUK.chunk_14987 s88
  have s86 : leavesOK ctxLitU 156237500000 0 ((leaves.drop 29972).take 28) 156425000000 0 = true :=
    take_step (n := 2) (t := 28) (b := 29974) rfl rfl ArealUCore.ArealUK.chunk_14986 s87
  have s85 : leavesOK ctxLitU 156225000000 0 ((leaves.drop 29970).take 30) 156425000000 0 = true :=
    take_step (n := 2) (t := 30) (b := 29972) rfl rfl ArealUCore.ArealUK.chunk_14985 s86
  have s84 : leavesOK ctxLitU 312425000000 1 ((leaves.drop 29968).take 32) 156425000000 0 = true :=
    take_step (n := 2) (t := 32) (b := 29970) rfl rfl ArealUCore.ArealUK.chunk_14984 s85
  have s83 : leavesOK ctxLitU 156187500000 0 ((leaves.drop 29966).take 34) 156425000000 0 = true :=
    take_step (n := 2) (t := 34) (b := 29968) rfl rfl ArealUCore.ArealUK.chunk_14983 s84
  have s82 : leavesOK ctxLitU 312350000000 1 ((leaves.drop 29964).take 36) 156425000000 0 = true :=
    take_step (n := 2) (t := 36) (b := 29966) rfl rfl ArealUCore.ArealUK.chunk_14982 s83
  have s81 : leavesOK ctxLitU 156162500000 0 ((leaves.drop 29962).take 38) 156425000000 0 = true :=
    take_step (n := 2) (t := 38) (b := 29964) rfl rfl ArealUCore.ArealUK.chunk_14981 s82
  have s80 : leavesOK ctxLitU 156150000000 0 ((leaves.drop 29960).take 40) 156425000000 0 = true :=
    take_step (n := 2) (t := 40) (b := 29962) rfl rfl ArealUCore.ArealUK.chunk_14980 s81
  have s79 : leavesOK ctxLitU 156137500000 0 ((leaves.drop 29958).take 42) 156425000000 0 = true :=
    take_step (n := 2) (t := 42) (b := 29960) rfl rfl ArealUCore.ArealUK.chunk_14979 s80
  have s78 : leavesOK ctxLitU 156125000000 0 ((leaves.drop 29956).take 44) 156425000000 0 = true :=
    take_step (n := 2) (t := 44) (b := 29958) rfl rfl ArealUCore.ArealUK.chunk_14978 s79
  have s77 : leavesOK ctxLitU 312212500000 1 ((leaves.drop 29954).take 46) 156425000000 0 = true :=
    take_step (n := 2) (t := 46) (b := 29956) rfl rfl ArealUCore.ArealUK.chunk_14977 s78
  have s76 : leavesOK ctxLitU 312187500000 1 ((leaves.drop 29952).take 48) 156425000000 0 = true :=
    take_step (n := 2) (t := 48) (b := 29954) rfl rfl ArealUCore.ArealUK.chunk_14976 s77
  have s75 : leavesOK ctxLitU 312162500000 1 ((leaves.drop 29950).take 50) 156425000000 0 = true :=
    take_step (n := 2) (t := 50) (b := 29952) rfl rfl ArealUCore.ArealUK.chunk_14975 s76
  have s74 : leavesOK ctxLitU 156068750000 0 ((leaves.drop 29948).take 52) 156425000000 0 = true :=
    take_step (n := 2) (t := 52) (b := 29950) rfl rfl ArealUCore.ArealUK.chunk_14974 s75
  have s73 : leavesOK ctxLitU 156056250000 0 ((leaves.drop 29946).take 54) 156425000000 0 = true :=
    take_step (n := 2) (t := 54) (b := 29948) rfl rfl ArealUCore.ArealUK.chunk_14973 s74
  have s72 : leavesOK ctxLitU 156043750000 0 ((leaves.drop 29944).take 56) 156425000000 0 = true :=
    take_step (n := 2) (t := 56) (b := 29946) rfl rfl ArealUCore.ArealUK.chunk_14972 s73
  have s71 : leavesOK ctxLitU 156031250000 0 ((leaves.drop 29942).take 58) 156425000000 0 = true :=
    take_step (n := 2) (t := 58) (b := 29944) rfl rfl ArealUCore.ArealUK.chunk_14971 s72
  have s70 : leavesOK ctxLitU 156012500000 0 ((leaves.drop 29940).take 60) 156425000000 0 = true :=
    take_step (n := 2) (t := 60) (b := 29942) rfl rfl ArealUCore.ArealUK.chunk_14970 s71
  have s69 : leavesOK ctxLitU 311987500000 1 ((leaves.drop 29938).take 62) 156425000000 0 = true :=
    take_step (n := 2) (t := 62) (b := 29940) rfl rfl ArealUCore.ArealUK.chunk_14969 s70
  have s68 : leavesOK ctxLitU 311962500000 1 ((leaves.drop 29936).take 64) 156425000000 0 = true :=
    take_step (n := 2) (t := 64) (b := 29938) rfl rfl ArealUCore.ArealUK.chunk_14968 s69
  have s67 : leavesOK ctxLitU 155968750000 0 ((leaves.drop 29934).take 66) 156425000000 0 = true :=
    take_step (n := 2) (t := 66) (b := 29936) rfl rfl ArealUCore.ArealUK.chunk_14967 s68
  have s66 : leavesOK ctxLitU 155956250000 0 ((leaves.drop 29932).take 68) 156425000000 0 = true :=
    take_step (n := 2) (t := 68) (b := 29934) rfl rfl ArealUCore.ArealUK.chunk_14966 s67
  have s65 : leavesOK ctxLitU 155943750000 0 ((leaves.drop 29930).take 70) 156425000000 0 = true :=
    take_step (n := 2) (t := 70) (b := 29932) rfl rfl ArealUCore.ArealUK.chunk_14965 s66
  have s64 : leavesOK ctxLitU 155931250000 0 ((leaves.drop 29928).take 72) 156425000000 0 = true :=
    take_step (n := 2) (t := 72) (b := 29930) rfl rfl ArealUCore.ArealUK.chunk_14964 s65
  have s63 : leavesOK ctxLitU 311837500000 1 ((leaves.drop 29926).take 74) 156425000000 0 = true :=
    take_step (n := 2) (t := 74) (b := 29928) rfl rfl ArealUCore.ArealUK.chunk_14963 s64
  have s62 : leavesOK ctxLitU 311812500000 1 ((leaves.drop 29924).take 76) 156425000000 0 = true :=
    take_step (n := 2) (t := 76) (b := 29926) rfl rfl ArealUCore.ArealUK.chunk_14962 s63
  have s61 : leavesOK ctxLitU 311787500000 1 ((leaves.drop 29922).take 78) 156425000000 0 = true :=
    take_step (n := 2) (t := 78) (b := 29924) rfl rfl ArealUCore.ArealUK.chunk_14961 s62
  have s60 : leavesOK ctxLitU 311762500000 1 ((leaves.drop 29920).take 80) 156425000000 0 = true :=
    take_step (n := 2) (t := 80) (b := 29922) rfl rfl ArealUCore.ArealUK.chunk_14960 s61
  have s59 : leavesOK ctxLitU 155868750000 0 ((leaves.drop 29918).take 82) 156425000000 0 = true :=
    take_step (n := 2) (t := 82) (b := 29920) rfl rfl ArealUCore.ArealUK.chunk_14959 s60
  have s58 : leavesOK ctxLitU 155856250000 0 ((leaves.drop 29916).take 84) 156425000000 0 = true :=
    take_step (n := 2) (t := 84) (b := 29918) rfl rfl ArealUCore.ArealUK.chunk_14958 s59
  have s57 : leavesOK ctxLitU 155843750000 0 ((leaves.drop 29914).take 86) 156425000000 0 = true :=
    take_step (n := 2) (t := 86) (b := 29916) rfl rfl ArealUCore.ArealUK.chunk_14957 s58
  have s56 : leavesOK ctxLitU 155831250000 0 ((leaves.drop 29912).take 88) 156425000000 0 = true :=
    take_step (n := 2) (t := 88) (b := 29914) rfl rfl ArealUCore.ArealUK.chunk_14956 s57
  have s55 : leavesOK ctxLitU 311637500000 1 ((leaves.drop 29910).take 90) 156425000000 0 = true :=
    take_step (n := 2) (t := 90) (b := 29912) rfl rfl ArealUCore.ArealUK.chunk_14955 s56
  have s54 : leavesOK ctxLitU 311612500000 1 ((leaves.drop 29908).take 92) 156425000000 0 = true :=
    take_step (n := 2) (t := 92) (b := 29910) rfl rfl ArealUCore.ArealUK.chunk_14954 s55
  have s53 : leavesOK ctxLitU 155787500000 0 ((leaves.drop 29906).take 94) 156425000000 0 = true :=
    take_step (n := 2) (t := 94) (b := 29908) rfl rfl ArealUCore.ArealUK.chunk_14953 s54
  have s52 : leavesOK ctxLitU 311550000000 1 ((leaves.drop 29904).take 96) 156425000000 0 = true :=
    take_step (n := 2) (t := 96) (b := 29906) rfl rfl ArealUCore.ArealUK.chunk_14952 s53
  have s51 : leavesOK ctxLitU 155762500000 0 ((leaves.drop 29902).take 98) 156425000000 0 = true :=
    take_step (n := 2) (t := 98) (b := 29904) rfl rfl ArealUCore.ArealUK.chunk_14951 s52
  have s50 : leavesOK ctxLitU 155750000000 0 ((leaves.drop 29900).take 100) 156425000000 0 = true :=
    take_step (n := 2) (t := 100) (b := 29902) rfl rfl ArealUCore.ArealUK.chunk_14950 s51
  have s49 : leavesOK ctxLitU 155737500000 0 ((leaves.drop 29898).take 102) 156425000000 0 = true :=
    take_step (n := 2) (t := 102) (b := 29900) rfl rfl ArealUCore.ArealUK.chunk_14949 s50
  have s48 : leavesOK ctxLitU 155725000000 0 ((leaves.drop 29896).take 104) 156425000000 0 = true :=
    take_step (n := 2) (t := 104) (b := 29898) rfl rfl ArealUCore.ArealUK.chunk_14948 s49
  have s47 : leavesOK ctxLitU 311425000000 1 ((leaves.drop 29894).take 106) 156425000000 0 = true :=
    take_step (n := 2) (t := 106) (b := 29896) rfl rfl ArealUCore.ArealUK.chunk_14947 s48
  have s46 : leavesOK ctxLitU 311400000000 1 ((leaves.drop 29892).take 108) 156425000000 0 = true :=
    take_step (n := 2) (t := 108) (b := 29894) rfl rfl ArealUCore.ArealUK.chunk_14946 s47
  have s45 : leavesOK ctxLitU 311375000000 1 ((leaves.drop 29890).take 110) 156425000000 0 = true :=
    take_step (n := 2) (t := 110) (b := 29892) rfl rfl ArealUCore.ArealUK.chunk_14945 s46
  have s44 : leavesOK ctxLitU 155668750000 0 ((leaves.drop 29888).take 112) 156425000000 0 = true :=
    take_step (n := 2) (t := 112) (b := 29890) rfl rfl ArealUCore.ArealUK.chunk_14944 s45
  have s43 : leavesOK ctxLitU 155656250000 0 ((leaves.drop 29886).take 114) 156425000000 0 = true :=
    take_step (n := 2) (t := 114) (b := 29888) rfl rfl ArealUCore.ArealUK.chunk_14943 s44
  have s42 : leavesOK ctxLitU 155643750000 0 ((leaves.drop 29884).take 116) 156425000000 0 = true :=
    take_step (n := 2) (t := 116) (b := 29886) rfl rfl ArealUCore.ArealUK.chunk_14942 s43
  have s41 : leavesOK ctxLitU 155631250000 0 ((leaves.drop 29882).take 118) 156425000000 0 = true :=
    take_step (n := 2) (t := 118) (b := 29884) rfl rfl ArealUCore.ArealUK.chunk_14941 s42
  have s40 : leavesOK ctxLitU 155612500000 0 ((leaves.drop 29880).take 120) 156425000000 0 = true :=
    take_step (n := 2) (t := 120) (b := 29882) rfl rfl ArealUCore.ArealUK.chunk_14940 s41
  have s39 : leavesOK ctxLitU 155587500000 0 ((leaves.drop 29878).take 122) 156425000000 0 = true :=
    take_step (n := 2) (t := 122) (b := 29880) rfl rfl ArealUCore.ArealUK.chunk_14939 s40
  have s38 : leavesOK ctxLitU 311150000000 1 ((leaves.drop 29876).take 124) 156425000000 0 = true :=
    take_step (n := 2) (t := 124) (b := 29878) rfl rfl ArealUCore.ArealUK.chunk_14938 s39
  have s37 : leavesOK ctxLitU 155562500000 0 ((leaves.drop 29874).take 126) 156425000000 0 = true :=
    take_step (n := 2) (t := 126) (b := 29876) rfl rfl ArealUCore.ArealUK.chunk_14937 s38
  have s36 : leavesOK ctxLitU 155550000000 0 ((leaves.drop 29872).take 128) 156425000000 0 = true :=
    take_step (n := 2) (t := 128) (b := 29874) rfl rfl ArealUCore.ArealUK.chunk_14936 s37
  have s35 : leavesOK ctxLitU 155537500000 0 ((leaves.drop 29870).take 130) 156425000000 0 = true :=
    take_step (n := 2) (t := 130) (b := 29872) rfl rfl ArealUCore.ArealUK.chunk_14935 s36
  have s34 : leavesOK ctxLitU 155525000000 0 ((leaves.drop 29868).take 132) 156425000000 0 = true :=
    take_step (n := 2) (t := 132) (b := 29870) rfl rfl ArealUCore.ArealUK.chunk_14934 s35
  have s33 : leavesOK ctxLitU 311012500000 1 ((leaves.drop 29866).take 134) 156425000000 0 = true :=
    take_step (n := 2) (t := 134) (b := 29868) rfl rfl ArealUCore.ArealUK.chunk_14933 s34
  have s32 : leavesOK ctxLitU 310987500000 1 ((leaves.drop 29864).take 136) 156425000000 0 = true :=
    take_step (n := 2) (t := 136) (b := 29866) rfl rfl ArealUCore.ArealUK.chunk_14932 s33
  have s31 : leavesOK ctxLitU 310962500000 1 ((leaves.drop 29862).take 138) 156425000000 0 = true :=
    take_step (n := 2) (t := 138) (b := 29864) rfl rfl ArealUCore.ArealUK.chunk_14931 s32
  have s30 : leavesOK ctxLitU 155468750000 0 ((leaves.drop 29860).take 140) 156425000000 0 = true :=
    take_step (n := 2) (t := 140) (b := 29862) rfl rfl ArealUCore.ArealUK.chunk_14930 s31
  have s29 : leavesOK ctxLitU 155456250000 0 ((leaves.drop 29858).take 142) 156425000000 0 = true :=
    take_step (n := 2) (t := 142) (b := 29860) rfl rfl ArealUCore.ArealUK.chunk_14929 s30
  have s28 : leavesOK ctxLitU 155443750000 0 ((leaves.drop 29856).take 144) 156425000000 0 = true :=
    take_step (n := 2) (t := 144) (b := 29858) rfl rfl ArealUCore.ArealUK.chunk_14928 s29
  have s27 : leavesOK ctxLitU 155431250000 0 ((leaves.drop 29854).take 146) 156425000000 0 = true :=
    take_step (n := 2) (t := 146) (b := 29856) rfl rfl ArealUCore.ArealUK.chunk_14927 s28
  have s26 : leavesOK ctxLitU 155412500000 0 ((leaves.drop 29852).take 148) 156425000000 0 = true :=
    take_step (n := 2) (t := 148) (b := 29854) rfl rfl ArealUCore.ArealUK.chunk_14926 s27
  have s25 : leavesOK ctxLitU 310787500000 1 ((leaves.drop 29850).take 150) 156425000000 0 = true :=
    take_step (n := 2) (t := 150) (b := 29852) rfl rfl ArealUCore.ArealUK.chunk_14925 s26
  have s24 : leavesOK ctxLitU 155375000000 0 ((leaves.drop 29848).take 152) 156425000000 0 = true :=
    take_step (n := 2) (t := 152) (b := 29850) rfl rfl ArealUCore.ArealUK.chunk_14924 s25
  have s23 : leavesOK ctxLitU 155362500000 0 ((leaves.drop 29846).take 154) 156425000000 0 = true :=
    take_step (n := 2) (t := 154) (b := 29848) rfl rfl ArealUCore.ArealUK.chunk_14923 s24
  have s22 : leavesOK ctxLitU 155350000000 0 ((leaves.drop 29844).take 156) 156425000000 0 = true :=
    take_step (n := 2) (t := 156) (b := 29846) rfl rfl ArealUCore.ArealUK.chunk_14922 s23
  have s21 : leavesOK ctxLitU 310675000000 1 ((leaves.drop 29842).take 158) 156425000000 0 = true :=
    take_step (n := 2) (t := 158) (b := 29844) rfl rfl ArealUCore.ArealUK.chunk_14921 s22
  have s20 : leavesOK ctxLitU 310650000000 1 ((leaves.drop 29840).take 160) 156425000000 0 = true :=
    take_step (n := 2) (t := 160) (b := 29842) rfl rfl ArealUCore.ArealUK.chunk_14920 s21
  have s19 : leavesOK ctxLitU 621225000000 2 ((leaves.drop 29838).take 162) 156425000000 0 = true :=
    take_step (n := 2) (t := 162) (b := 29840) rfl rfl ArealUCore.ArealUK.chunk_14919 s20
  have s18 : leavesOK ctxLitU 310587500000 1 ((leaves.drop 29836).take 164) 156425000000 0 = true :=
    take_step (n := 2) (t := 164) (b := 29838) rfl rfl ArealUCore.ArealUK.chunk_14918 s19
  have s17 : leavesOK ctxLitU 310562500000 1 ((leaves.drop 29834).take 166) 156425000000 0 = true :=
    take_step (n := 2) (t := 166) (b := 29836) rfl rfl ArealUCore.ArealUK.chunk_14917 s18
  have s16 : leavesOK ctxLitU 155268750000 0 ((leaves.drop 29832).take 168) 156425000000 0 = true :=
    take_step (n := 2) (t := 168) (b := 29834) rfl rfl ArealUCore.ArealUK.chunk_14916 s17
  have s15 : leavesOK ctxLitU 155256250000 0 ((leaves.drop 29830).take 170) 156425000000 0 = true :=
    take_step (n := 2) (t := 170) (b := 29832) rfl rfl ArealUCore.ArealUK.chunk_14915 s16
  have s14 : leavesOK ctxLitU 155243750000 0 ((leaves.drop 29828).take 172) 156425000000 0 = true :=
    take_step (n := 2) (t := 172) (b := 29830) rfl rfl ArealUCore.ArealUK.chunk_14914 s15
  have s13 : leavesOK ctxLitU 155231250000 0 ((leaves.drop 29826).take 174) 156425000000 0 = true :=
    take_step (n := 2) (t := 174) (b := 29828) rfl rfl ArealUCore.ArealUK.chunk_14913 s14
  have s12 : leavesOK ctxLitU 310437500000 1 ((leaves.drop 29824).take 176) 156425000000 0 = true :=
    take_step (n := 2) (t := 176) (b := 29826) rfl rfl ArealUCore.ArealUK.chunk_14912 s13
  have s11 : leavesOK ctxLitU 155200000000 0 ((leaves.drop 29822).take 178) 156425000000 0 = true :=
    take_step (n := 2) (t := 178) (b := 29824) rfl rfl ArealUCore.ArealUK.chunk_14911 s12
  have s10 : leavesOK ctxLitU 310362500000 1 ((leaves.drop 29820).take 180) 156425000000 0 = true :=
    take_step (n := 2) (t := 180) (b := 29822) rfl rfl ArealUCore.ArealUK.chunk_14910 s11
  have s9 : leavesOK ctxLitU 155168750000 0 ((leaves.drop 29818).take 182) 156425000000 0 = true :=
    take_step (n := 2) (t := 182) (b := 29820) rfl rfl ArealUCore.ArealUK.chunk_14909 s10
  have s8 : leavesOK ctxLitU 155156250000 0 ((leaves.drop 29816).take 184) 156425000000 0 = true :=
    take_step (n := 2) (t := 184) (b := 29818) rfl rfl ArealUCore.ArealUK.chunk_14908 s9
  have s7 : leavesOK ctxLitU 155143750000 0 ((leaves.drop 29814).take 186) 156425000000 0 = true :=
    take_step (n := 2) (t := 186) (b := 29816) rfl rfl ArealUCore.ArealUK.chunk_14907 s8
  have s6 : leavesOK ctxLitU 155131250000 0 ((leaves.drop 29812).take 188) 156425000000 0 = true :=
    take_step (n := 2) (t := 188) (b := 29814) rfl rfl ArealUCore.ArealUK.chunk_14906 s7
  have s5 : leavesOK ctxLitU 310237500000 1 ((leaves.drop 29810).take 190) 156425000000 0 = true :=
    take_step (n := 2) (t := 190) (b := 29812) rfl rfl ArealUCore.ArealUK.chunk_14905 s6
  have s4 : leavesOK ctxLitU 310212500000 1 ((leaves.drop 29808).take 192) 156425000000 0 = true :=
    take_step (n := 2) (t := 192) (b := 29810) rfl rfl ArealUCore.ArealUK.chunk_14904 s5
  have s3 : leavesOK ctxLitU 310187500000 1 ((leaves.drop 29806).take 194) 156425000000 0 = true :=
    take_step (n := 2) (t := 194) (b := 29808) rfl rfl ArealUCore.ArealUK.chunk_14903 s4
  have s2 : leavesOK ctxLitU 310162500000 1 ((leaves.drop 29804).take 196) 156425000000 0 = true :=
    take_step (n := 2) (t := 196) (b := 29806) rfl rfl ArealUCore.ArealUK.chunk_14902 s3
  have s1 : leavesOK ctxLitU 155068750000 0 ((leaves.drop 29802).take 198) 156425000000 0 = true :=
    take_step (n := 2) (t := 198) (b := 29804) rfl rfl ArealUCore.ArealUK.chunk_14901 s2
  have s0 : leavesOK ctxLitU 155056250000 0 ((leaves.drop 29800).take 200) 156425000000 0 = true :=
    take_step (n := 2) (t := 200) (b := 29802) rfl rfl ArealUCore.ArealUK.chunk_14900 s1
  exact s0

end Areal.UCert

import ArealUK.Chunk12900
import ArealUK.Chunk12901
import ArealUK.Chunk12902
import ArealUK.Chunk12903
import ArealUK.Chunk12904
import ArealUK.Chunk12905
import ArealUK.Chunk12906
import ArealUK.Chunk12907
import ArealUK.Chunk12908
import ArealUK.Chunk12909
import ArealUK.Chunk12910
import ArealUK.Chunk12911
import ArealUK.Chunk12912
import ArealUK.Chunk12913
import ArealUK.Chunk12914
import ArealUK.Chunk12915
import ArealUK.Chunk12916
import ArealUK.Chunk12917
import ArealUK.Chunk12918
import ArealUK.Chunk12919
import ArealUK.Chunk12920
import ArealUK.Chunk12921
import ArealUK.Chunk12922
import ArealUK.Chunk12923
import ArealUK.Chunk12924
import ArealUK.Chunk12925
import ArealUK.Chunk12926
import ArealUK.Chunk12927
import ArealUK.Chunk12928
import ArealUK.Chunk12929
import ArealUK.Chunk12930
import ArealUK.Chunk12931
import ArealUK.Chunk12932
import ArealUK.Chunk12933
import ArealUK.Chunk12934
import ArealUK.Chunk12935
import ArealUK.Chunk12936
import ArealUK.Chunk12937
import ArealUK.Chunk12938
import ArealUK.Chunk12939
import ArealUK.Chunk12940
import ArealUK.Chunk12941
import ArealUK.Chunk12942
import ArealUK.Chunk12943
import ArealUK.Chunk12944
import ArealUK.Chunk12945
import ArealUK.Chunk12946
import ArealUK.Chunk12947
import ArealUK.Chunk12948
import ArealUK.Chunk12949
import ArealUK.Chunk12950
import ArealUK.Chunk12951
import ArealUK.Chunk12952
import ArealUK.Chunk12953
import ArealUK.Chunk12954
import ArealUK.Chunk12955
import ArealUK.Chunk12956
import ArealUK.Chunk12957
import ArealUK.Chunk12958
import ArealUK.Chunk12959
import ArealUK.Chunk12960
import ArealUK.Chunk12961
import ArealUK.Chunk12962
import ArealUK.Chunk12963
import ArealUK.Chunk12964
import ArealUK.Chunk12965
import ArealUK.Chunk12966
import ArealUK.Chunk12967
import ArealUK.Chunk12968
import ArealUK.Chunk12969
import ArealUK.Chunk12970
import ArealUK.Chunk12971
import ArealUK.Chunk12972
import ArealUK.Chunk12973
import ArealUK.Chunk12974
import ArealUK.Chunk12975
import ArealUK.Chunk12976
import ArealUK.Chunk12977
import ArealUK.Chunk12978
import ArealUK.Chunk12979
import ArealUK.Chunk12980
import ArealUK.Chunk12981
import ArealUK.Chunk12982
import ArealUK.Chunk12983
import ArealUK.Chunk12984
import ArealUK.Chunk12985
import ArealUK.Chunk12986
import ArealUK.Chunk12987
import ArealUK.Chunk12988
import ArealUK.Chunk12989
import ArealUK.Chunk12990
import ArealUK.Chunk12991
import ArealUK.Chunk12992
import ArealUK.Chunk12993
import ArealUK.Chunk12994
import ArealUK.Chunk12995
import ArealUK.Chunk12996
import ArealUK.Chunk12997
import ArealUK.Chunk12998
import ArealUK.Chunk12999
import Areal.UCert.LeavesKGen

/-! Group 129 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_129 : leavesOK ctxLitU 523700000000 2 ((leaves.drop 25800).take 200) 528350000000 2 = true := by
  have s99 := ArealUCore.ArealUK.chunk_12999
  have s98 : leavesOK ctxLitU 528250000000 2 ((leaves.drop 25996).take 4) 528350000000 2 = true :=
    take_step (n := 2) (t := 4) (b := 25998) rfl rfl ArealUCore.ArealUK.chunk_12998 s99
  have s97 : leavesOK ctxLitU 528200000000 2 ((leaves.drop 25994).take 6) 528350000000 2 = true :=
    take_step (n := 2) (t := 6) (b := 25996) rfl rfl ArealUCore.ArealUK.chunk_12997 s98
  have s96 : leavesOK ctxLitU 528150000000 2 ((leaves.drop 25992).take 8) 528350000000 2 = true :=
    take_step (n := 2) (t := 8) (b := 25994) rfl rfl ArealUCore.ArealUK.chunk_12996 s97
  have s95 : leavesOK ctxLitU 528100000000 2 ((leaves.drop 25990).take 10) 528350000000 2 = true :=
    take_step (n := 2) (t := 10) (b := 25992) rfl rfl ArealUCore.ArealUK.chunk_12995 s96
  have s94 : leavesOK ctxLitU 528050000000 2 ((leaves.drop 25988).take 12) 528350000000 2 = true :=
    take_step (n := 2) (t := 12) (b := 25990) rfl rfl ArealUCore.ArealUK.chunk_12994 s95
  have s93 : leavesOK ctxLitU 528000000000 2 ((leaves.drop 25986).take 14) 528350000000 2 = true :=
    take_step (n := 2) (t := 14) (b := 25988) rfl rfl ArealUCore.ArealUK.chunk_12993 s94
  have s92 : leavesOK ctxLitU 527950000000 2 ((leaves.drop 25984).take 16) 528350000000 2 = true :=
    take_step (n := 2) (t := 16) (b := 25986) rfl rfl ArealUCore.ArealUK.chunk_12992 s93
  have s91 : leavesOK ctxLitU 527900000000 2 ((leaves.drop 25982).take 18) 528350000000 2 = true :=
    take_step (n := 2) (t := 18) (b := 25984) rfl rfl ArealUCore.ArealUK.chunk_12991 s92
  have s90 : leavesOK ctxLitU 527850000000 2 ((leaves.drop 25980).take 20) 528350000000 2 = true :=
    take_step (n := 2) (t := 20) (b := 25982) rfl rfl ArealUCore.ArealUK.chunk_12990 s91
  have s89 : leavesOK ctxLitU 527800000000 2 ((leaves.drop 25978).take 22) 528350000000 2 = true :=
    take_step (n := 2) (t := 22) (b := 25980) rfl rfl ArealUCore.ArealUK.chunk_12989 s90
  have s88 : leavesOK ctxLitU 263875000000 1 ((leaves.drop 25976).take 24) 528350000000 2 = true :=
    take_step (n := 2) (t := 24) (b := 25978) rfl rfl ArealUCore.ArealUK.chunk_12988 s89
  have s87 : leavesOK ctxLitU 263850000000 1 ((leaves.drop 25974).take 26) 528350000000 2 = true :=
    take_step (n := 2) (t := 26) (b := 25976) rfl rfl ArealUCore.ArealUK.chunk_12987 s88
  have s86 : leavesOK ctxLitU 131912500000 0 ((leaves.drop 25972).take 28) 528350000000 2 = true :=
    take_step (n := 2) (t := 28) (b := 25974) rfl rfl ArealUCore.ArealUK.chunk_12986 s87
  have s85 : leavesOK ctxLitU 131900000000 0 ((leaves.drop 25970).take 30) 528350000000 2 = true :=
    take_step (n := 2) (t := 30) (b := 25972) rfl rfl ArealUCore.ArealUK.chunk_12985 s86
  have s84 : leavesOK ctxLitU 527562500000 2 ((leaves.drop 25968).take 32) 528350000000 2 = true :=
    take_step (n := 2) (t := 32) (b := 25970) rfl rfl ArealUCore.ArealUK.chunk_12984 s85
  have s83 : leavesOK ctxLitU 527537500000 2 ((leaves.drop 25966).take 34) 528350000000 2 = true :=
    take_step (n := 2) (t := 34) (b := 25968) rfl rfl ArealUCore.ArealUK.chunk_12983 s84
  have s82 : leavesOK ctxLitU 263750000000 1 ((leaves.drop 25964).take 36) 528350000000 2 = true :=
    take_step (n := 2) (t := 36) (b := 25966) rfl rfl ArealUCore.ArealUK.chunk_12982 s83
  have s81 : leavesOK ctxLitU 263737500000 1 ((leaves.drop 25962).take 38) 528350000000 2 = true :=
    take_step (n := 2) (t := 38) (b := 25964) rfl rfl ArealUCore.ArealUK.chunk_12981 s82
  have s80 : leavesOK ctxLitU 131856250000 0 ((leaves.drop 25960).take 40) 528350000000 2 = true :=
    take_step (n := 2) (t := 40) (b := 25962) rfl rfl ArealUCore.ArealUK.chunk_12980 s81
  have s79 : leavesOK ctxLitU 131843750000 0 ((leaves.drop 25958).take 42) 528350000000 2 = true :=
    take_step (n := 2) (t := 42) (b := 25960) rfl rfl ArealUCore.ArealUK.chunk_12979 s80
  have s78 : leavesOK ctxLitU 263668750000 1 ((leaves.drop 25956).take 44) 528350000000 2 = true :=
    take_step (n := 2) (t := 44) (b := 25958) rfl rfl ArealUCore.ArealUK.chunk_12978 s79
  have s77 : leavesOK ctxLitU 263656250000 1 ((leaves.drop 25954).take 46) 528350000000 2 = true :=
    take_step (n := 2) (t := 46) (b := 25956) rfl rfl ArealUCore.ArealUK.chunk_12977 s78
  have s76 : leavesOK ctxLitU 263637500000 1 ((leaves.drop 25952).take 48) 528350000000 2 = true :=
    take_step (n := 2) (t := 48) (b := 25954) rfl rfl ArealUCore.ArealUK.chunk_12976 s77
  have s75 : leavesOK ctxLitU 263612500000 1 ((leaves.drop 25950).take 50) 528350000000 2 = true :=
    take_step (n := 2) (t := 50) (b := 25952) rfl rfl ArealUCore.ArealUK.chunk_12975 s76
  have s74 : leavesOK ctxLitU 263587500000 1 ((leaves.drop 25948).take 52) 528350000000 2 = true :=
    take_step (n := 2) (t := 52) (b := 25950) rfl rfl ArealUCore.ArealUK.chunk_12974 s75
  have s73 : leavesOK ctxLitU 263562500000 1 ((leaves.drop 25946).take 54) 528350000000 2 = true :=
    take_step (n := 2) (t := 54) (b := 25948) rfl rfl ArealUCore.ArealUK.chunk_12973 s74
  have s72 : leavesOK ctxLitU 131768750000 0 ((leaves.drop 25944).take 56) 528350000000 2 = true :=
    take_step (n := 2) (t := 56) (b := 25946) rfl rfl ArealUCore.ArealUK.chunk_12972 s73
  have s71 : leavesOK ctxLitU 131756250000 0 ((leaves.drop 25942).take 58) 528350000000 2 = true :=
    take_step (n := 2) (t := 58) (b := 25944) rfl rfl ArealUCore.ArealUK.chunk_12971 s72
  have s70 : leavesOK ctxLitU 131743750000 0 ((leaves.drop 25940).take 60) 528350000000 2 = true :=
    take_step (n := 2) (t := 60) (b := 25942) rfl rfl ArealUCore.ArealUK.chunk_12970 s71
  have s69 : leavesOK ctxLitU 131731250000 0 ((leaves.drop 25938).take 62) 528350000000 2 = true :=
    take_step (n := 2) (t := 62) (b := 25940) rfl rfl ArealUCore.ArealUK.chunk_12969 s70
  have s68 : leavesOK ctxLitU 263437500000 1 ((leaves.drop 25936).take 64) 528350000000 2 = true :=
    take_step (n := 2) (t := 64) (b := 25938) rfl rfl ArealUCore.ArealUK.chunk_12968 s69
  have s67 : leavesOK ctxLitU 263412500000 1 ((leaves.drop 25934).take 66) 528350000000 2 = true :=
    take_step (n := 2) (t := 66) (b := 25936) rfl rfl ArealUCore.ArealUK.chunk_12967 s68
  have s66 : leavesOK ctxLitU 526775000000 2 ((leaves.drop 25932).take 68) 528350000000 2 = true :=
    take_step (n := 2) (t := 68) (b := 25934) rfl rfl ArealUCore.ArealUK.chunk_12966 s67
  have s65 : leavesOK ctxLitU 526725000000 2 ((leaves.drop 25930).take 70) 528350000000 2 = true :=
    take_step (n := 2) (t := 70) (b := 25932) rfl rfl ArealUCore.ArealUK.chunk_12965 s66
  have s64 : leavesOK ctxLitU 526675000000 2 ((leaves.drop 25928).take 72) 528350000000 2 = true :=
    take_step (n := 2) (t := 72) (b := 25930) rfl rfl ArealUCore.ArealUK.chunk_12964 s65
  have s63 : leavesOK ctxLitU 526625000000 2 ((leaves.drop 25926).take 74) 528350000000 2 = true :=
    take_step (n := 2) (t := 74) (b := 25928) rfl rfl ArealUCore.ArealUK.chunk_12963 s64
  have s62 : leavesOK ctxLitU 526575000000 2 ((leaves.drop 25924).take 76) 528350000000 2 = true :=
    take_step (n := 2) (t := 76) (b := 25926) rfl rfl ArealUCore.ArealUK.chunk_12962 s63
  have s61 : leavesOK ctxLitU 526525000000 2 ((leaves.drop 25922).take 78) 528350000000 2 = true :=
    take_step (n := 2) (t := 78) (b := 25924) rfl rfl ArealUCore.ArealUK.chunk_12961 s62
  have s60 : leavesOK ctxLitU 526475000000 2 ((leaves.drop 25920).take 80) 528350000000 2 = true :=
    take_step (n := 2) (t := 80) (b := 25922) rfl rfl ArealUCore.ArealUK.chunk_12960 s61
  have s59 : leavesOK ctxLitU 526425000000 2 ((leaves.drop 25918).take 82) 528350000000 2 = true :=
    take_step (n := 2) (t := 82) (b := 25920) rfl rfl ArealUCore.ArealUK.chunk_12959 s60
  have s58 : leavesOK ctxLitU 263187500000 1 ((leaves.drop 25916).take 84) 528350000000 2 = true :=
    take_step (n := 2) (t := 84) (b := 25918) rfl rfl ArealUCore.ArealUK.chunk_12958 s59
  have s57 : leavesOK ctxLitU 263162500000 1 ((leaves.drop 25914).take 86) 528350000000 2 = true :=
    take_step (n := 2) (t := 86) (b := 25916) rfl rfl ArealUCore.ArealUK.chunk_12957 s58
  have s56 : leavesOK ctxLitU 131568750000 0 ((leaves.drop 25912).take 88) 528350000000 2 = true :=
    take_step (n := 2) (t := 88) (b := 25914) rfl rfl ArealUCore.ArealUK.chunk_12956 s57
  have s55 : leavesOK ctxLitU 131556250000 0 ((leaves.drop 25910).take 90) 528350000000 2 = true :=
    take_step (n := 2) (t := 90) (b := 25912) rfl rfl ArealUCore.ArealUK.chunk_12955 s56
  have s54 : leavesOK ctxLitU 131543750000 0 ((leaves.drop 25908).take 92) 528350000000 2 = true :=
    take_step (n := 2) (t := 92) (b := 25910) rfl rfl ArealUCore.ArealUK.chunk_12954 s55
  have s53 : leavesOK ctxLitU 131531250000 0 ((leaves.drop 25906).take 94) 528350000000 2 = true :=
    take_step (n := 2) (t := 94) (b := 25908) rfl rfl ArealUCore.ArealUK.chunk_12953 s54
  have s52 : leavesOK ctxLitU 263037500000 1 ((leaves.drop 25904).take 96) 528350000000 2 = true :=
    take_step (n := 2) (t := 96) (b := 25906) rfl rfl ArealUCore.ArealUK.chunk_12952 s53
  have s51 : leavesOK ctxLitU 263012500000 1 ((leaves.drop 25902).take 98) 528350000000 2 = true :=
    take_step (n := 2) (t := 98) (b := 25904) rfl rfl ArealUCore.ArealUK.chunk_12951 s52
  have s50 : leavesOK ctxLitU 262987500000 1 ((leaves.drop 25900).take 100) 528350000000 2 = true :=
    take_step (n := 2) (t := 100) (b := 25902) rfl rfl ArealUCore.ArealUK.chunk_12950 s51
  have s49 : leavesOK ctxLitU 262962500000 1 ((leaves.drop 25898).take 102) 528350000000 2 = true :=
    take_step (n := 2) (t := 102) (b := 25900) rfl rfl ArealUCore.ArealUK.chunk_12949 s50
  have s48 : leavesOK ctxLitU 131468750000 0 ((leaves.drop 25896).take 104) 528350000000 2 = true :=
    take_step (n := 2) (t := 104) (b := 25898) rfl rfl ArealUCore.ArealUK.chunk_12948 s49
  have s47 : leavesOK ctxLitU 131456250000 0 ((leaves.drop 25894).take 106) 528350000000 2 = true :=
    take_step (n := 2) (t := 106) (b := 25896) rfl rfl ArealUCore.ArealUK.chunk_12947 s48
  have s46 : leavesOK ctxLitU 131443750000 0 ((leaves.drop 25892).take 108) 528350000000 2 = true :=
    take_step (n := 2) (t := 108) (b := 25894) rfl rfl ArealUCore.ArealUK.chunk_12946 s47
  have s45 : leavesOK ctxLitU 131431250000 0 ((leaves.drop 25890).take 110) 528350000000 2 = true :=
    take_step (n := 2) (t := 110) (b := 25892) rfl rfl ArealUCore.ArealUK.chunk_12945 s46
  have s44 : leavesOK ctxLitU 262850000000 1 ((leaves.drop 25888).take 112) 528350000000 2 = true :=
    take_step (n := 2) (t := 112) (b := 25890) rfl rfl ArealUCore.ArealUK.chunk_12944 s45
  have s43 : leavesOK ctxLitU 262825000000 1 ((leaves.drop 25886).take 114) 528350000000 2 = true :=
    take_step (n := 2) (t := 114) (b := 25888) rfl rfl ArealUCore.ArealUK.chunk_12943 s44
  have s42 : leavesOK ctxLitU 262800000000 1 ((leaves.drop 25884).take 116) 528350000000 2 = true :=
    take_step (n := 2) (t := 116) (b := 25886) rfl rfl ArealUCore.ArealUK.chunk_12942 s43
  have s41 : leavesOK ctxLitU 262775000000 1 ((leaves.drop 25882).take 118) 528350000000 2 = true :=
    take_step (n := 2) (t := 118) (b := 25884) rfl rfl ArealUCore.ArealUK.chunk_12941 s42
  have s40 : leavesOK ctxLitU 262750000000 1 ((leaves.drop 25880).take 120) 528350000000 2 = true :=
    take_step (n := 2) (t := 120) (b := 25882) rfl rfl ArealUCore.ArealUK.chunk_12940 s41
  have s39 : leavesOK ctxLitU 262737500000 1 ((leaves.drop 25878).take 122) 528350000000 2 = true :=
    take_step (n := 2) (t := 122) (b := 25880) rfl rfl ArealUCore.ArealUK.chunk_12939 s40
  have s38 : leavesOK ctxLitU 262725000000 1 ((leaves.drop 25876).take 124) 528350000000 2 = true :=
    take_step (n := 2) (t := 124) (b := 25878) rfl rfl ArealUCore.ArealUK.chunk_12938 s39
  have s37 : leavesOK ctxLitU 131350000000 0 ((leaves.drop 25874).take 126) 528350000000 2 = true :=
    take_step (n := 2) (t := 126) (b := 25876) rfl rfl ArealUCore.ArealUK.chunk_12937 s38
  have s36 : leavesOK ctxLitU 131337500000 0 ((leaves.drop 25872).take 128) 528350000000 2 = true :=
    take_step (n := 2) (t := 128) (b := 25874) rfl rfl ArealUCore.ArealUK.chunk_12936 s37
  have s35 : leavesOK ctxLitU 131325000000 0 ((leaves.drop 25870).take 130) 528350000000 2 = true :=
    take_step (n := 2) (t := 130) (b := 25872) rfl rfl ArealUCore.ArealUK.chunk_12935 s36
  have s34 : leavesOK ctxLitU 262625000000 1 ((leaves.drop 25868).take 132) 528350000000 2 = true :=
    take_step (n := 2) (t := 132) (b := 25870) rfl rfl ArealUCore.ArealUK.chunk_12934 s35
  have s33 : leavesOK ctxLitU 262600000000 1 ((leaves.drop 25866).take 134) 528350000000 2 = true :=
    take_step (n := 2) (t := 134) (b := 25868) rfl rfl ArealUCore.ArealUK.chunk_12933 s34
  have s32 : leavesOK ctxLitU 262575000000 1 ((leaves.drop 25864).take 136) 528350000000 2 = true :=
    take_step (n := 2) (t := 136) (b := 25866) rfl rfl ArealUCore.ArealUK.chunk_12932 s33
  have s31 : leavesOK ctxLitU 262550000000 1 ((leaves.drop 25862).take 138) 528350000000 2 = true :=
    take_step (n := 2) (t := 138) (b := 25864) rfl rfl ArealUCore.ArealUK.chunk_12931 s32
  have s30 : leavesOK ctxLitU 131262500000 0 ((leaves.drop 25860).take 140) 528350000000 2 = true :=
    take_step (n := 2) (t := 140) (b := 25862) rfl rfl ArealUCore.ArealUK.chunk_12930 s31
  have s29 : leavesOK ctxLitU 131250000000 0 ((leaves.drop 25858).take 142) 528350000000 2 = true :=
    take_step (n := 2) (t := 142) (b := 25860) rfl rfl ArealUCore.ArealUK.chunk_12929 s30
  have s28 : leavesOK ctxLitU 131237500000 0 ((leaves.drop 25856).take 144) 528350000000 2 = true :=
    take_step (n := 2) (t := 144) (b := 25858) rfl rfl ArealUCore.ArealUK.chunk_12928 s29
  have s27 : leavesOK ctxLitU 262462500000 1 ((leaves.drop 25854).take 146) 528350000000 2 = true :=
    take_step (n := 2) (t := 146) (b := 25856) rfl rfl ArealUCore.ArealUK.chunk_12927 s28
  have s26 : leavesOK ctxLitU 262450000000 1 ((leaves.drop 25852).take 148) 528350000000 2 = true :=
    take_step (n := 2) (t := 148) (b := 25854) rfl rfl ArealUCore.ArealUK.chunk_12926 s27
  have s25 : leavesOK ctxLitU 262425000000 1 ((leaves.drop 25850).take 150) 528350000000 2 = true :=
    take_step (n := 2) (t := 150) (b := 25852) rfl rfl ArealUCore.ArealUK.chunk_12925 s26
  have s24 : leavesOK ctxLitU 262400000000 1 ((leaves.drop 25848).take 152) 528350000000 2 = true :=
    take_step (n := 2) (t := 152) (b := 25850) rfl rfl ArealUCore.ArealUK.chunk_12924 s25
  have s23 : leavesOK ctxLitU 262375000000 1 ((leaves.drop 25846).take 154) 528350000000 2 = true :=
    take_step (n := 2) (t := 154) (b := 25848) rfl rfl ArealUCore.ArealUK.chunk_12923 s24
  have s22 : leavesOK ctxLitU 262350000000 1 ((leaves.drop 25844).take 156) 528350000000 2 = true :=
    take_step (n := 2) (t := 156) (b := 25846) rfl rfl ArealUCore.ArealUK.chunk_12922 s23
  have s21 : leavesOK ctxLitU 131162500000 0 ((leaves.drop 25842).take 158) 528350000000 2 = true :=
    take_step (n := 2) (t := 158) (b := 25844) rfl rfl ArealUCore.ArealUK.chunk_12921 s22
  have s20 : leavesOK ctxLitU 131150000000 0 ((leaves.drop 25840).take 160) 528350000000 2 = true :=
    take_step (n := 2) (t := 160) (b := 25842) rfl rfl ArealUCore.ArealUK.chunk_12920 s21
  have s19 : leavesOK ctxLitU 131137500000 0 ((leaves.drop 25838).take 162) 528350000000 2 = true :=
    take_step (n := 2) (t := 162) (b := 25840) rfl rfl ArealUCore.ArealUK.chunk_12919 s20
  have s18 : leavesOK ctxLitU 262262500000 1 ((leaves.drop 25836).take 164) 528350000000 2 = true :=
    take_step (n := 2) (t := 164) (b := 25838) rfl rfl ArealUCore.ArealUK.chunk_12918 s19
  have s17 : leavesOK ctxLitU 262250000000 1 ((leaves.drop 25834).take 166) 528350000000 2 = true :=
    take_step (n := 2) (t := 166) (b := 25836) rfl rfl ArealUCore.ArealUK.chunk_12917 s18
  have s16 : leavesOK ctxLitU 524462500000 2 ((leaves.drop 25832).take 168) 528350000000 2 = true :=
    take_step (n := 2) (t := 168) (b := 25834) rfl rfl ArealUCore.ArealUK.chunk_12916 s17
  have s15 : leavesOK ctxLitU 524437500000 2 ((leaves.drop 25830).take 170) 528350000000 2 = true :=
    take_step (n := 2) (t := 170) (b := 25832) rfl rfl ArealUCore.ArealUK.chunk_12915 s16
  have s14 : leavesOK ctxLitU 262200000000 1 ((leaves.drop 25828).take 172) 528350000000 2 = true :=
    take_step (n := 2) (t := 172) (b := 25830) rfl rfl ArealUCore.ArealUK.chunk_12914 s15
  have s13 : leavesOK ctxLitU 524350000000 2 ((leaves.drop 25826).take 174) 528350000000 2 = true :=
    take_step (n := 2) (t := 174) (b := 25828) rfl rfl ArealUCore.ArealUK.chunk_12913 s14
  have s12 : leavesOK ctxLitU 524300000000 2 ((leaves.drop 25824).take 176) 528350000000 2 = true :=
    take_step (n := 2) (t := 176) (b := 25826) rfl rfl ArealUCore.ArealUK.chunk_12912 s13
  have s11 : leavesOK ctxLitU 524250000000 2 ((leaves.drop 25822).take 178) 528350000000 2 = true :=
    take_step (n := 2) (t := 178) (b := 25824) rfl rfl ArealUCore.ArealUK.chunk_12911 s12
  have s10 : leavesOK ctxLitU 524200000000 2 ((leaves.drop 25820).take 180) 528350000000 2 = true :=
    take_step (n := 2) (t := 180) (b := 25822) rfl rfl ArealUCore.ArealUK.chunk_12910 s11
  have s9 : leavesOK ctxLitU 524150000000 2 ((leaves.drop 25818).take 182) 528350000000 2 = true :=
    take_step (n := 2) (t := 182) (b := 25820) rfl rfl ArealUCore.ArealUK.chunk_12909 s10
  have s8 : leavesOK ctxLitU 524100000000 2 ((leaves.drop 25816).take 184) 528350000000 2 = true :=
    take_step (n := 2) (t := 184) (b := 25818) rfl rfl ArealUCore.ArealUK.chunk_12908 s9
  have s7 : leavesOK ctxLitU 524050000000 2 ((leaves.drop 25814).take 186) 528350000000 2 = true :=
    take_step (n := 2) (t := 186) (b := 25816) rfl rfl ArealUCore.ArealUK.chunk_12907 s8
  have s6 : leavesOK ctxLitU 524000000000 2 ((leaves.drop 25812).take 188) 528350000000 2 = true :=
    take_step (n := 2) (t := 188) (b := 25814) rfl rfl ArealUCore.ArealUK.chunk_12906 s7
  have s5 : leavesOK ctxLitU 523950000000 2 ((leaves.drop 25810).take 190) 528350000000 2 = true :=
    take_step (n := 2) (t := 190) (b := 25812) rfl rfl ArealUCore.ArealUK.chunk_12905 s6
  have s4 : leavesOK ctxLitU 523900000000 2 ((leaves.drop 25808).take 192) 528350000000 2 = true :=
    take_step (n := 2) (t := 192) (b := 25810) rfl rfl ArealUCore.ArealUK.chunk_12904 s5
  have s3 : leavesOK ctxLitU 523850000000 2 ((leaves.drop 25806).take 194) 528350000000 2 = true :=
    take_step (n := 2) (t := 194) (b := 25808) rfl rfl ArealUCore.ArealUK.chunk_12903 s4
  have s2 : leavesOK ctxLitU 523800000000 2 ((leaves.drop 25804).take 196) 528350000000 2 = true :=
    take_step (n := 2) (t := 196) (b := 25806) rfl rfl ArealUCore.ArealUK.chunk_12902 s3
  have s1 : leavesOK ctxLitU 523750000000 2 ((leaves.drop 25802).take 198) 528350000000 2 = true :=
    take_step (n := 2) (t := 198) (b := 25804) rfl rfl ArealUCore.ArealUK.chunk_12901 s2
  have s0 : leavesOK ctxLitU 523700000000 2 ((leaves.drop 25800).take 200) 528350000000 2 = true :=
    take_step (n := 2) (t := 200) (b := 25802) rfl rfl ArealUCore.ArealUK.chunk_12900 s1
  exact s0

end Areal.UCert

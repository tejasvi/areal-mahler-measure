import ArealUK.Chunk10900
import ArealUK.Chunk10901
import ArealUK.Chunk10902
import ArealUK.Chunk10903
import ArealUK.Chunk10904
import ArealUK.Chunk10905
import ArealUK.Chunk10906
import ArealUK.Chunk10907
import ArealUK.Chunk10908
import ArealUK.Chunk10909
import ArealUK.Chunk10910
import ArealUK.Chunk10911
import ArealUK.Chunk10912
import ArealUK.Chunk10913
import ArealUK.Chunk10914
import ArealUK.Chunk10915
import ArealUK.Chunk10916
import ArealUK.Chunk10917
import ArealUK.Chunk10918
import ArealUK.Chunk10919
import ArealUK.Chunk10920
import ArealUK.Chunk10921
import ArealUK.Chunk10922
import ArealUK.Chunk10923
import ArealUK.Chunk10924
import ArealUK.Chunk10925
import ArealUK.Chunk10926
import ArealUK.Chunk10927
import ArealUK.Chunk10928
import ArealUK.Chunk10929
import ArealUK.Chunk10930
import ArealUK.Chunk10931
import ArealUK.Chunk10932
import ArealUK.Chunk10933
import ArealUK.Chunk10934
import ArealUK.Chunk10935
import ArealUK.Chunk10936
import ArealUK.Chunk10937
import ArealUK.Chunk10938
import ArealUK.Chunk10939
import ArealUK.Chunk10940
import ArealUK.Chunk10941
import ArealUK.Chunk10942
import ArealUK.Chunk10943
import ArealUK.Chunk10944
import ArealUK.Chunk10945
import ArealUK.Chunk10946
import ArealUK.Chunk10947
import ArealUK.Chunk10948
import ArealUK.Chunk10949
import ArealUK.Chunk10950
import ArealUK.Chunk10951
import ArealUK.Chunk10952
import ArealUK.Chunk10953
import ArealUK.Chunk10954
import ArealUK.Chunk10955
import ArealUK.Chunk10956
import ArealUK.Chunk10957
import ArealUK.Chunk10958
import ArealUK.Chunk10959
import ArealUK.Chunk10960
import ArealUK.Chunk10961
import ArealUK.Chunk10962
import ArealUK.Chunk10963
import ArealUK.Chunk10964
import ArealUK.Chunk10965
import ArealUK.Chunk10966
import ArealUK.Chunk10967
import ArealUK.Chunk10968
import ArealUK.Chunk10969
import ArealUK.Chunk10970
import ArealUK.Chunk10971
import ArealUK.Chunk10972
import ArealUK.Chunk10973
import ArealUK.Chunk10974
import ArealUK.Chunk10975
import ArealUK.Chunk10976
import ArealUK.Chunk10977
import ArealUK.Chunk10978
import ArealUK.Chunk10979
import ArealUK.Chunk10980
import ArealUK.Chunk10981
import ArealUK.Chunk10982
import ArealUK.Chunk10983
import ArealUK.Chunk10984
import ArealUK.Chunk10985
import ArealUK.Chunk10986
import ArealUK.Chunk10987
import ArealUK.Chunk10988
import ArealUK.Chunk10989
import ArealUK.Chunk10990
import ArealUK.Chunk10991
import ArealUK.Chunk10992
import ArealUK.Chunk10993
import ArealUK.Chunk10994
import ArealUK.Chunk10995
import ArealUK.Chunk10996
import ArealUK.Chunk10997
import ArealUK.Chunk10998
import ArealUK.Chunk10999
import Areal.UCert.LeavesKGen

/-! Group 109 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_109 : leavesOK ctxLitU 412979200000000 12 ((leaves.drop 21800).take 200) 204281250000 1 = true := by
  have s99 := ArealUCore.ArealUK.chunk_10999
  have s98 : leavesOK ctxLitU 408506250000 2 ((leaves.drop 21996).take 4) 204281250000 1 = true :=
    take_step (n := 2) (t := 4) (b := 21998) rfl rfl ArealUCore.ArealUK.chunk_10998 s99
  have s97 : leavesOK ctxLitU 204243750000 1 ((leaves.drop 21994).take 6) 204281250000 1 = true :=
    take_step (n := 2) (t := 6) (b := 21996) rfl rfl ArealUCore.ArealUK.chunk_10997 s98
  have s96 : leavesOK ctxLitU 102112500000 0 ((leaves.drop 21992).take 8) 204281250000 1 = true :=
    take_step (n := 2) (t := 8) (b := 21994) rfl rfl ArealUCore.ArealUK.chunk_10996 s97
  have s95 : leavesOK ctxLitU 102100000000 0 ((leaves.drop 21990).take 10) 204281250000 1 = true :=
    take_step (n := 2) (t := 10) (b := 21992) rfl rfl ArealUCore.ArealUK.chunk_10995 s96
  have s94 : leavesOK ctxLitU 102087500000 0 ((leaves.drop 21988).take 12) 204281250000 1 = true :=
    take_step (n := 2) (t := 12) (b := 21990) rfl rfl ArealUCore.ArealUK.chunk_10994 s95
  have s93 : leavesOK ctxLitU 102075000000 0 ((leaves.drop 21986).take 14) 204281250000 1 = true :=
    take_step (n := 2) (t := 14) (b := 21988) rfl rfl ArealUCore.ArealUK.chunk_10993 s94
  have s92 : leavesOK ctxLitU 418053002734967 12 ((leaves.drop 21984).take 16) 204281250000 1 = true :=
    take_step (n := 2) (t := 16) (b := 21986) rfl rfl ArealUCore.ArealUK.chunk_10992 s93
  have s91 : leavesOK ctxLitU 102050000000 0 ((leaves.drop 21982).take 18) 204281250000 1 = true :=
    take_step (n := 2) (t := 18) (b := 21984) rfl rfl ArealUCore.ArealUK.chunk_10991 s92
  have s90 : leavesOK ctxLitU 102037500000 0 ((leaves.drop 21980).take 20) 204281250000 1 = true :=
    take_step (n := 2) (t := 20) (b := 21982) rfl rfl ArealUCore.ArealUK.chunk_10990 s91
  have s89 : leavesOK ctxLitU 102025000000 0 ((leaves.drop 21978).take 22) 204281250000 1 = true :=
    take_step (n := 2) (t := 22) (b := 21980) rfl rfl ArealUCore.ArealUK.chunk_10989 s90
  have s88 : leavesOK ctxLitU 102012500000 0 ((leaves.drop 21976).take 24) 204281250000 1 = true :=
    take_step (n := 2) (t := 24) (b := 21978) rfl rfl ArealUCore.ArealUK.chunk_10988 s89
  have s87 : leavesOK ctxLitU 204006250000 1 ((leaves.drop 21974).take 26) 204281250000 1 = true :=
    take_step (n := 2) (t := 26) (b := 21976) rfl rfl ArealUCore.ArealUK.chunk_10987 s88
  have s86 : leavesOK ctxLitU 815993750000 3 ((leaves.drop 21972).take 28) 204281250000 1 = true :=
    take_step (n := 2) (t := 28) (b := 21974) rfl rfl ArealUCore.ArealUK.chunk_10986 s87
  have s85 : leavesOK ctxLitU 407987500000 2 ((leaves.drop 21970).take 30) 204281250000 1 = true :=
    take_step (n := 2) (t := 30) (b := 21972) rfl rfl ArealUCore.ArealUK.chunk_10985 s86
  have s84 : leavesOK ctxLitU 101987500000 0 ((leaves.drop 21968).take 32) 204281250000 1 = true :=
    take_step (n := 2) (t := 32) (b := 21970) rfl rfl ArealUCore.ArealUK.chunk_10984 s85
  have s83 : leavesOK ctxLitU 203956250000 1 ((leaves.drop 21966).take 34) 204281250000 1 = true :=
    take_step (n := 2) (t := 34) (b := 21968) rfl rfl ArealUCore.ArealUK.chunk_10983 s84
  have s82 : leavesOK ctxLitU 407887500000 2 ((leaves.drop 21964).take 36) 204281250000 1 = true :=
    take_step (n := 2) (t := 36) (b := 21966) rfl rfl ArealUCore.ArealUK.chunk_10982 s83
  have s81 : leavesOK ctxLitU 407862500000 2 ((leaves.drop 21962).take 38) 204281250000 1 = true :=
    take_step (n := 2) (t := 38) (b := 21964) rfl rfl ArealUCore.ArealUK.chunk_10981 s82
  have s80 : leavesOK ctxLitU 407837500000 2 ((leaves.drop 21960).take 40) 204281250000 1 = true :=
    take_step (n := 2) (t := 40) (b := 21962) rfl rfl ArealUCore.ArealUK.chunk_10980 s81
  have s79 : leavesOK ctxLitU 407812500000 2 ((leaves.drop 21958).take 42) 204281250000 1 = true :=
    take_step (n := 2) (t := 42) (b := 21960) rfl rfl ArealUCore.ArealUK.chunk_10979 s80
  have s78 : leavesOK ctxLitU 815575000000 3 ((leaves.drop 21956).take 44) 204281250000 1 = true :=
    take_step (n := 2) (t := 44) (b := 21958) rfl rfl ArealUCore.ArealUK.chunk_10978 s79
  have s77 : leavesOK ctxLitU 815525000000 3 ((leaves.drop 21954).take 46) 204281250000 1 = true :=
    take_step (n := 2) (t := 46) (b := 21956) rfl rfl ArealUCore.ArealUK.chunk_10977 s78
  have s76 : leavesOK ctxLitU 815475000000 3 ((leaves.drop 21952).take 48) 204281250000 1 = true :=
    take_step (n := 2) (t := 48) (b := 21954) rfl rfl ArealUCore.ArealUK.chunk_10976 s77
  have s75 : leavesOK ctxLitU 815425000000 3 ((leaves.drop 21950).take 50) 204281250000 1 = true :=
    take_step (n := 2) (t := 50) (b := 21952) rfl rfl ArealUCore.ArealUK.chunk_10975 s76
  have s74 : leavesOK ctxLitU 815375000000 3 ((leaves.drop 21948).take 52) 204281250000 1 = true :=
    take_step (n := 2) (t := 52) (b := 21950) rfl rfl ArealUCore.ArealUK.chunk_10974 s75
  have s73 : leavesOK ctxLitU 815325000000 3 ((leaves.drop 21946).take 54) 204281250000 1 = true :=
    take_step (n := 2) (t := 54) (b := 21948) rfl rfl ArealUCore.ArealUK.chunk_10973 s74
  have s72 : leavesOK ctxLitU 815275000000 3 ((leaves.drop 21944).take 56) 204281250000 1 = true :=
    take_step (n := 2) (t := 56) (b := 21946) rfl rfl ArealUCore.ArealUK.chunk_10972 s73
  have s71 : leavesOK ctxLitU 815225000000 3 ((leaves.drop 21942).take 58) 204281250000 1 = true :=
    take_step (n := 2) (t := 58) (b := 21944) rfl rfl ArealUCore.ArealUK.chunk_10971 s72
  have s70 : leavesOK ctxLitU 815175000000 3 ((leaves.drop 21940).take 60) 204281250000 1 = true :=
    take_step (n := 2) (t := 60) (b := 21942) rfl rfl ArealUCore.ArealUK.chunk_10970 s71
  have s69 : leavesOK ctxLitU 815125000000 3 ((leaves.drop 21938).take 62) 204281250000 1 = true :=
    take_step (n := 2) (t := 62) (b := 21940) rfl rfl ArealUCore.ArealUK.chunk_10969 s70
  have s68 : leavesOK ctxLitU 407525000000 2 ((leaves.drop 21936).take 64) 204281250000 1 = true :=
    take_step (n := 2) (t := 64) (b := 21938) rfl rfl ArealUCore.ArealUK.chunk_10968 s69
  have s67 : leavesOK ctxLitU 407475000000 2 ((leaves.drop 21934).take 66) 204281250000 1 = true :=
    take_step (n := 2) (t := 66) (b := 21936) rfl rfl ArealUCore.ArealUK.chunk_10967 s68
  have s66 : leavesOK ctxLitU 407425000000 2 ((leaves.drop 21932).take 68) 204281250000 1 = true :=
    take_step (n := 2) (t := 68) (b := 21934) rfl rfl ArealUCore.ArealUK.chunk_10966 s67
  have s65 : leavesOK ctxLitU 814800000000 3 ((leaves.drop 21930).take 70) 204281250000 1 = true :=
    take_step (n := 2) (t := 70) (b := 21932) rfl rfl ArealUCore.ArealUK.chunk_10965 s66
  have s64 : leavesOK ctxLitU 814750000000 3 ((leaves.drop 21928).take 72) 204281250000 1 = true :=
    take_step (n := 2) (t := 72) (b := 21930) rfl rfl ArealUCore.ArealUK.chunk_10964 s65
  have s63 : leavesOK ctxLitU 814700000000 3 ((leaves.drop 21926).take 74) 204281250000 1 = true :=
    take_step (n := 2) (t := 74) (b := 21928) rfl rfl ArealUCore.ArealUK.chunk_10963 s64
  have s62 : leavesOK ctxLitU 814650000000 3 ((leaves.drop 21924).take 76) 204281250000 1 = true :=
    take_step (n := 2) (t := 76) (b := 21926) rfl rfl ArealUCore.ArealUK.chunk_10962 s63
  have s61 : leavesOK ctxLitU 814600000000 3 ((leaves.drop 21922).take 78) 204281250000 1 = true :=
    take_step (n := 2) (t := 78) (b := 21924) rfl rfl ArealUCore.ArealUK.chunk_10961 s62
  have s60 : leavesOK ctxLitU 814550000000 3 ((leaves.drop 21920).take 80) 204281250000 1 = true :=
    take_step (n := 2) (t := 80) (b := 21922) rfl rfl ArealUCore.ArealUK.chunk_10960 s61
  have s59 : leavesOK ctxLitU 814500000000 3 ((leaves.drop 21918).take 82) 204281250000 1 = true :=
    take_step (n := 2) (t := 82) (b := 21920) rfl rfl ArealUCore.ArealUK.chunk_10959 s60
  have s58 : leavesOK ctxLitU 407200000000 2 ((leaves.drop 21916).take 84) 204281250000 1 = true :=
    take_step (n := 2) (t := 84) (b := 21918) rfl rfl ArealUCore.ArealUK.chunk_10958 s59
  have s57 : leavesOK ctxLitU 407150000000 2 ((leaves.drop 21914).take 86) 204281250000 1 = true :=
    take_step (n := 2) (t := 86) (b := 21916) rfl rfl ArealUCore.ArealUK.chunk_10957 s58
  have s56 : leavesOK ctxLitU 814225000000 3 ((leaves.drop 21912).take 88) 204281250000 1 = true :=
    take_step (n := 2) (t := 88) (b := 21914) rfl rfl ArealUCore.ArealUK.chunk_10956 s57
  have s55 : leavesOK ctxLitU 407075000000 2 ((leaves.drop 21910).take 90) 204281250000 1 = true :=
    take_step (n := 2) (t := 90) (b := 21912) rfl rfl ArealUCore.ArealUK.chunk_10955 s56
  have s54 : leavesOK ctxLitU 407025000000 2 ((leaves.drop 21908).take 92) 204281250000 1 = true :=
    take_step (n := 2) (t := 92) (b := 21910) rfl rfl ArealUCore.ArealUK.chunk_10954 s55
  have s53 : leavesOK ctxLitU 406975000000 2 ((leaves.drop 21906).take 94) 204281250000 1 = true :=
    take_step (n := 2) (t := 94) (b := 21908) rfl rfl ArealUCore.ArealUK.chunk_10953 s54
  have s52 : leavesOK ctxLitU 406925000000 2 ((leaves.drop 21904).take 96) 204281250000 1 = true :=
    take_step (n := 2) (t := 96) (b := 21906) rfl rfl ArealUCore.ArealUK.chunk_10952 s53
  have s51 : leavesOK ctxLitU 813775000000 3 ((leaves.drop 21902).take 98) 204281250000 1 = true :=
    take_step (n := 2) (t := 98) (b := 21904) rfl rfl ArealUCore.ArealUK.chunk_10951 s52
  have s50 : leavesOK ctxLitU 406850000000 2 ((leaves.drop 21900).take 100) 204281250000 1 = true :=
    take_step (n := 2) (t := 100) (b := 21902) rfl rfl ArealUCore.ArealUK.chunk_10950 s51
  have s49 : leavesOK ctxLitU 406800000000 2 ((leaves.drop 21898).take 102) 204281250000 1 = true :=
    take_step (n := 2) (t := 102) (b := 21900) rfl rfl ArealUCore.ArealUK.chunk_10949 s50
  have s48 : leavesOK ctxLitU 406750000000 2 ((leaves.drop 21896).take 104) 204281250000 1 = true :=
    take_step (n := 2) (t := 104) (b := 21898) rfl rfl ArealUCore.ArealUK.chunk_10948 s49
  have s47 : leavesOK ctxLitU 406700000000 2 ((leaves.drop 21894).take 106) 204281250000 1 = true :=
    take_step (n := 2) (t := 106) (b := 21896) rfl rfl ArealUCore.ArealUK.chunk_10947 s48
  have s46 : leavesOK ctxLitU 406650000000 2 ((leaves.drop 21892).take 108) 204281250000 1 = true :=
    take_step (n := 2) (t := 108) (b := 21894) rfl rfl ArealUCore.ArealUK.chunk_10946 s47
  have s45 : leavesOK ctxLitU 406600000000 2 ((leaves.drop 21890).take 110) 204281250000 1 = true :=
    take_step (n := 2) (t := 110) (b := 21892) rfl rfl ArealUCore.ArealUK.chunk_10945 s46
  have s44 : leavesOK ctxLitU 406550000000 2 ((leaves.drop 21888).take 112) 204281250000 1 = true :=
    take_step (n := 2) (t := 112) (b := 21890) rfl rfl ArealUCore.ArealUK.chunk_10944 s45
  have s43 : leavesOK ctxLitU 406500000000 2 ((leaves.drop 21886).take 114) 204281250000 1 = true :=
    take_step (n := 2) (t := 114) (b := 21888) rfl rfl ArealUCore.ArealUK.chunk_10943 s44
  have s42 : leavesOK ctxLitU 406450000000 2 ((leaves.drop 21884).take 116) 204281250000 1 = true :=
    take_step (n := 2) (t := 116) (b := 21886) rfl rfl ArealUCore.ArealUK.chunk_10942 s43
  have s41 : leavesOK ctxLitU 406400000000 2 ((leaves.drop 21882).take 118) 204281250000 1 = true :=
    take_step (n := 2) (t := 118) (b := 21884) rfl rfl ArealUCore.ArealUK.chunk_10941 s42
  have s40 : leavesOK ctxLitU 406350000000 2 ((leaves.drop 21880).take 120) 204281250000 1 = true :=
    take_step (n := 2) (t := 120) (b := 21882) rfl rfl ArealUCore.ArealUK.chunk_10940 s41
  have s39 : leavesOK ctxLitU 406300000000 2 ((leaves.drop 21878).take 122) 204281250000 1 = true :=
    take_step (n := 2) (t := 122) (b := 21880) rfl rfl ArealUCore.ArealUK.chunk_10939 s40
  have s38 : leavesOK ctxLitU 406250000000 2 ((leaves.drop 21876).take 124) 204281250000 1 = true :=
    take_step (n := 2) (t := 124) (b := 21878) rfl rfl ArealUCore.ArealUK.chunk_10938 s39
  have s37 : leavesOK ctxLitU 406200000000 2 ((leaves.drop 21874).take 126) 204281250000 1 = true :=
    take_step (n := 2) (t := 126) (b := 21876) rfl rfl ArealUCore.ArealUK.chunk_10937 s38
  have s36 : leavesOK ctxLitU 406150000000 2 ((leaves.drop 21872).take 128) 204281250000 1 = true :=
    take_step (n := 2) (t := 128) (b := 21874) rfl rfl ArealUCore.ArealUK.chunk_10936 s37
  have s35 : leavesOK ctxLitU 406100000000 2 ((leaves.drop 21870).take 130) 204281250000 1 = true :=
    take_step (n := 2) (t := 130) (b := 21872) rfl rfl ArealUCore.ArealUK.chunk_10935 s36
  have s34 : leavesOK ctxLitU 406050000000 2 ((leaves.drop 21868).take 132) 204281250000 1 = true :=
    take_step (n := 2) (t := 132) (b := 21870) rfl rfl ArealUCore.ArealUK.chunk_10934 s35
  have s33 : leavesOK ctxLitU 406000000000 2 ((leaves.drop 21866).take 134) 204281250000 1 = true :=
    take_step (n := 2) (t := 134) (b := 21868) rfl rfl ArealUCore.ArealUK.chunk_10933 s34
  have s32 : leavesOK ctxLitU 405950000000 2 ((leaves.drop 21864).take 136) 204281250000 1 = true :=
    take_step (n := 2) (t := 136) (b := 21866) rfl rfl ArealUCore.ArealUK.chunk_10932 s33
  have s31 : leavesOK ctxLitU 405900000000 2 ((leaves.drop 21862).take 138) 204281250000 1 = true :=
    take_step (n := 2) (t := 138) (b := 21864) rfl rfl ArealUCore.ArealUK.chunk_10931 s32
  have s30 : leavesOK ctxLitU 405850000000 2 ((leaves.drop 21860).take 140) 204281250000 1 = true :=
    take_step (n := 2) (t := 140) (b := 21862) rfl rfl ArealUCore.ArealUK.chunk_10930 s31
  have s29 : leavesOK ctxLitU 405800000000 2 ((leaves.drop 21858).take 142) 204281250000 1 = true :=
    take_step (n := 2) (t := 142) (b := 21860) rfl rfl ArealUCore.ArealUK.chunk_10929 s30
  have s28 : leavesOK ctxLitU 405750000000 2 ((leaves.drop 21856).take 144) 204281250000 1 = true :=
    take_step (n := 2) (t := 144) (b := 21858) rfl rfl ArealUCore.ArealUK.chunk_10928 s29
  have s27 : leavesOK ctxLitU 405700000000 2 ((leaves.drop 21854).take 146) 204281250000 1 = true :=
    take_step (n := 2) (t := 146) (b := 21856) rfl rfl ArealUCore.ArealUK.chunk_10927 s28
  have s26 : leavesOK ctxLitU 405650000000 2 ((leaves.drop 21852).take 148) 204281250000 1 = true :=
    take_step (n := 2) (t := 148) (b := 21854) rfl rfl ArealUCore.ArealUK.chunk_10926 s27
  have s25 : leavesOK ctxLitU 405600000000 2 ((leaves.drop 21850).take 150) 204281250000 1 = true :=
    take_step (n := 2) (t := 150) (b := 21852) rfl rfl ArealUCore.ArealUK.chunk_10925 s26
  have s24 : leavesOK ctxLitU 405562500000 2 ((leaves.drop 21848).take 152) 204281250000 1 = true :=
    take_step (n := 2) (t := 152) (b := 21850) rfl rfl ArealUCore.ArealUK.chunk_10924 s25
  have s23 : leavesOK ctxLitU 811100000000 3 ((leaves.drop 21846).take 154) 204281250000 1 = true :=
    take_step (n := 2) (t := 154) (b := 21848) rfl rfl ArealUCore.ArealUK.chunk_10923 s24
  have s22 : leavesOK ctxLitU 405525000000 2 ((leaves.drop 21844).take 156) 204281250000 1 = true :=
    take_step (n := 2) (t := 156) (b := 21846) rfl rfl ArealUCore.ArealUK.chunk_10922 s23
  have s21 : leavesOK ctxLitU 202743750000 1 ((leaves.drop 21842).take 158) 204281250000 1 = true :=
    take_step (n := 2) (t := 158) (b := 21844) rfl rfl ArealUCore.ArealUK.chunk_10921 s22
  have s20 : leavesOK ctxLitU 202731250000 1 ((leaves.drop 21840).take 160) 204281250000 1 = true :=
    take_step (n := 2) (t := 160) (b := 21842) rfl rfl ArealUCore.ArealUK.chunk_10920 s21
  have s19 : leavesOK ctxLitU 101356250000 0 ((leaves.drop 21838).take 162) 204281250000 1 = true :=
    take_step (n := 2) (t := 162) (b := 21840) rfl rfl ArealUCore.ArealUK.chunk_10919 s20
  have s18 : leavesOK ctxLitU 202693750000 1 ((leaves.drop 21836).take 164) 204281250000 1 = true :=
    take_step (n := 2) (t := 164) (b := 21838) rfl rfl ArealUCore.ArealUK.chunk_10918 s19
  have s17 : leavesOK ctxLitU 202681250000 1 ((leaves.drop 21834).take 166) 204281250000 1 = true :=
    take_step (n := 2) (t := 166) (b := 21836) rfl rfl ArealUCore.ArealUK.chunk_10917 s18
  have s16 : leavesOK ctxLitU 202668750000 1 ((leaves.drop 21832).take 168) 204281250000 1 = true :=
    take_step (n := 2) (t := 168) (b := 21834) rfl rfl ArealUCore.ArealUK.chunk_10916 s17
  have s15 : leavesOK ctxLitU 101325000000 0 ((leaves.drop 21830).take 170) 204281250000 1 = true :=
    take_step (n := 2) (t := 170) (b := 21832) rfl rfl ArealUCore.ArealUK.chunk_10915 s16
  have s14 : leavesOK ctxLitU 202631250000 1 ((leaves.drop 21828).take 172) 204281250000 1 = true :=
    take_step (n := 2) (t := 172) (b := 21830) rfl rfl ArealUCore.ArealUK.chunk_10914 s15
  have s13 : leavesOK ctxLitU 101306250000 0 ((leaves.drop 21826).take 174) 204281250000 1 = true :=
    take_step (n := 2) (t := 174) (b := 21828) rfl rfl ArealUCore.ArealUK.chunk_10913 s14
  have s12 : leavesOK ctxLitU 101293750000 0 ((leaves.drop 21824).take 176) 204281250000 1 = true :=
    take_step (n := 2) (t := 176) (b := 21826) rfl rfl ArealUCore.ArealUK.chunk_10912 s13
  have s11 : leavesOK ctxLitU 101281250000 0 ((leaves.drop 21822).take 178) 204281250000 1 = true :=
    take_step (n := 2) (t := 178) (b := 21824) rfl rfl ArealUCore.ArealUK.chunk_10911 s12
  have s10 : leavesOK ctxLitU 101262500000 0 ((leaves.drop 21820).take 180) 204281250000 1 = true :=
    take_step (n := 2) (t := 180) (b := 21822) rfl rfl ArealUCore.ArealUK.chunk_10910 s11
  have s9 : leavesOK ctxLitU 101225000000 0 ((leaves.drop 21818).take 182) 204281250000 1 = true :=
    take_step (n := 2) (t := 182) (b := 21820) rfl rfl ArealUCore.ArealUK.chunk_10909 s10
  have s8 : leavesOK ctxLitU 101175000000 0 ((leaves.drop 21816).take 184) 204281250000 1 = true :=
    take_step (n := 2) (t := 184) (b := 21818) rfl rfl ArealUCore.ArealUK.chunk_10908 s9
  have s7 : leavesOK ctxLitU 101125000000 0 ((leaves.drop 21814).take 186) 204281250000 1 = true :=
    take_step (n := 2) (t := 186) (b := 21816) rfl rfl ArealUCore.ArealUK.chunk_10907 s8
  have s6 : leavesOK ctxLitU 101075000000 0 ((leaves.drop 21812).take 188) 204281250000 1 = true :=
    take_step (n := 2) (t := 188) (b := 21814) rfl rfl ArealUCore.ArealUK.chunk_10906 s7
  have s5 : leavesOK ctxLitU 101025000000 0 ((leaves.drop 21810).take 190) 204281250000 1 = true :=
    take_step (n := 2) (t := 190) (b := 21812) rfl rfl ArealUCore.ArealUK.chunk_10905 s6
  have s4 : leavesOK ctxLitU 100975000000 0 ((leaves.drop 21808).take 192) 204281250000 1 = true :=
    take_step (n := 2) (t := 192) (b := 21810) rfl rfl ArealUCore.ArealUK.chunk_10904 s5
  have s3 : leavesOK ctxLitU 100925000000 0 ((leaves.drop 21806).take 194) 204281250000 1 = true :=
    take_step (n := 2) (t := 194) (b := 21808) rfl rfl ArealUCore.ArealUK.chunk_10903 s4
  have s2 : leavesOK ctxLitU 100875000000 0 ((leaves.drop 21804).take 196) 204281250000 1 = true :=
    take_step (n := 2) (t := 196) (b := 21806) rfl rfl ArealUCore.ArealUK.chunk_10902 s3
  have s1 : leavesOK ctxLitU 413012587815104 12 ((leaves.drop 21802).take 198) 204281250000 1 = true :=
    take_step (n := 2) (t := 198) (b := 21804) rfl rfl ArealUCore.ArealUK.chunk_10901 s2
  have s0 : leavesOK ctxLitU 412979200000000 12 ((leaves.drop 21800).take 200) 204281250000 1 = true :=
    take_step (n := 2) (t := 200) (b := 21802) rfl rfl ArealUCore.ArealUK.chunk_10900 s1
  exact s0

end Areal.UCert

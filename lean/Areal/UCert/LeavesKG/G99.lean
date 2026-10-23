import ArealUK.Chunk9900
import ArealUK.Chunk9901
import ArealUK.Chunk9902
import ArealUK.Chunk9903
import ArealUK.Chunk9904
import ArealUK.Chunk9905
import ArealUK.Chunk9906
import ArealUK.Chunk9907
import ArealUK.Chunk9908
import ArealUK.Chunk9909
import ArealUK.Chunk9910
import ArealUK.Chunk9911
import ArealUK.Chunk9912
import ArealUK.Chunk9913
import ArealUK.Chunk9914
import ArealUK.Chunk9915
import ArealUK.Chunk9916
import ArealUK.Chunk9917
import ArealUK.Chunk9918
import ArealUK.Chunk9919
import ArealUK.Chunk9920
import ArealUK.Chunk9921
import ArealUK.Chunk9922
import ArealUK.Chunk9923
import ArealUK.Chunk9924
import ArealUK.Chunk9925
import ArealUK.Chunk9926
import ArealUK.Chunk9927
import ArealUK.Chunk9928
import ArealUK.Chunk9929
import ArealUK.Chunk9930
import ArealUK.Chunk9931
import ArealUK.Chunk9932
import ArealUK.Chunk9933
import ArealUK.Chunk9934
import ArealUK.Chunk9935
import ArealUK.Chunk9936
import ArealUK.Chunk9937
import ArealUK.Chunk9938
import ArealUK.Chunk9939
import ArealUK.Chunk9940
import ArealUK.Chunk9941
import ArealUK.Chunk9942
import ArealUK.Chunk9943
import ArealUK.Chunk9944
import ArealUK.Chunk9945
import ArealUK.Chunk9946
import ArealUK.Chunk9947
import ArealUK.Chunk9948
import ArealUK.Chunk9949
import ArealUK.Chunk9950
import ArealUK.Chunk9951
import ArealUK.Chunk9952
import ArealUK.Chunk9953
import ArealUK.Chunk9954
import ArealUK.Chunk9955
import ArealUK.Chunk9956
import ArealUK.Chunk9957
import ArealUK.Chunk9958
import ArealUK.Chunk9959
import ArealUK.Chunk9960
import ArealUK.Chunk9961
import ArealUK.Chunk9962
import ArealUK.Chunk9963
import ArealUK.Chunk9964
import ArealUK.Chunk9965
import ArealUK.Chunk9966
import ArealUK.Chunk9967
import ArealUK.Chunk9968
import ArealUK.Chunk9969
import ArealUK.Chunk9970
import ArealUK.Chunk9971
import ArealUK.Chunk9972
import ArealUK.Chunk9973
import ArealUK.Chunk9974
import ArealUK.Chunk9975
import ArealUK.Chunk9976
import ArealUK.Chunk9977
import ArealUK.Chunk9978
import ArealUK.Chunk9979
import ArealUK.Chunk9980
import ArealUK.Chunk9981
import ArealUK.Chunk9982
import ArealUK.Chunk9983
import ArealUK.Chunk9984
import ArealUK.Chunk9985
import ArealUK.Chunk9986
import ArealUK.Chunk9987
import ArealUK.Chunk9988
import ArealUK.Chunk9989
import ArealUK.Chunk9990
import ArealUK.Chunk9991
import ArealUK.Chunk9992
import ArealUK.Chunk9993
import ArealUK.Chunk9994
import ArealUK.Chunk9995
import ArealUK.Chunk9996
import ArealUK.Chunk9997
import ArealUK.Chunk9998
import ArealUK.Chunk9999
import Areal.UCert.LeavesKGen

/-! Group 99 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_99 : leavesOK ctxLitU 699075000000 3 ((leaves.drop 19800).take 200) 357175000000 2 = true := by
  have s99 := ArealUCore.ArealUK.chunk_9999
  have s98 : leavesOK ctxLitU 357075000000 2 ((leaves.drop 19996).take 4) 357175000000 2 = true :=
    take_step (n := 2) (t := 4) (b := 19998) rfl rfl ArealUCore.ArealUK.chunk_9998 s99
  have s97 : leavesOK ctxLitU 357025000000 2 ((leaves.drop 19994).take 6) 357175000000 2 = true :=
    take_step (n := 2) (t := 6) (b := 19996) rfl rfl ArealUCore.ArealUK.chunk_9997 s98
  have s96 : leavesOK ctxLitU 356975000000 2 ((leaves.drop 19992).take 8) 357175000000 2 = true :=
    take_step (n := 2) (t := 8) (b := 19994) rfl rfl ArealUCore.ArealUK.chunk_9996 s97
  have s95 : leavesOK ctxLitU 356925000000 2 ((leaves.drop 19990).take 10) 357175000000 2 = true :=
    take_step (n := 2) (t := 10) (b := 19992) rfl rfl ArealUCore.ArealUK.chunk_9995 s96
  have s94 : leavesOK ctxLitU 356875000000 2 ((leaves.drop 19988).take 12) 357175000000 2 = true :=
    take_step (n := 2) (t := 12) (b := 19990) rfl rfl ArealUCore.ArealUK.chunk_9994 s95
  have s93 : leavesOK ctxLitU 713675000000 3 ((leaves.drop 19986).take 14) 357175000000 2 = true :=
    take_step (n := 2) (t := 14) (b := 19988) rfl rfl ArealUCore.ArealUK.chunk_9993 s94
  have s92 : leavesOK ctxLitU 713625000000 3 ((leaves.drop 19984).take 16) 357175000000 2 = true :=
    take_step (n := 2) (t := 16) (b := 19986) rfl rfl ArealUCore.ArealUK.chunk_9992 s93
  have s91 : leavesOK ctxLitU 713575000000 3 ((leaves.drop 19982).take 18) 357175000000 2 = true :=
    take_step (n := 2) (t := 18) (b := 19984) rfl rfl ArealUCore.ArealUK.chunk_9991 s92
  have s90 : leavesOK ctxLitU 713525000000 3 ((leaves.drop 19980).take 20) 357175000000 2 = true :=
    take_step (n := 2) (t := 20) (b := 19982) rfl rfl ArealUCore.ArealUK.chunk_9990 s91
  have s89 : leavesOK ctxLitU 713475000000 3 ((leaves.drop 19978).take 22) 357175000000 2 = true :=
    take_step (n := 2) (t := 22) (b := 19980) rfl rfl ArealUCore.ArealUK.chunk_9989 s90
  have s88 : leavesOK ctxLitU 356700000000 2 ((leaves.drop 19976).take 24) 357175000000 2 = true :=
    take_step (n := 2) (t := 24) (b := 19978) rfl rfl ArealUCore.ArealUK.chunk_9988 s89
  have s87 : leavesOK ctxLitU 178325000000 1 ((leaves.drop 19974).take 26) 357175000000 2 = true :=
    take_step (n := 2) (t := 26) (b := 19976) rfl rfl ArealUCore.ArealUK.chunk_9987 s88
  have s86 : leavesOK ctxLitU 356625000000 2 ((leaves.drop 19972).take 28) 357175000000 2 = true :=
    take_step (n := 2) (t := 28) (b := 19974) rfl rfl ArealUCore.ArealUK.chunk_9986 s87
  have s85 : leavesOK ctxLitU 356600000000 2 ((leaves.drop 19970).take 30) 357175000000 2 = true :=
    take_step (n := 2) (t := 30) (b := 19972) rfl rfl ArealUCore.ArealUK.chunk_9985 s86
  have s84 : leavesOK ctxLitU 178287500000 1 ((leaves.drop 19968).take 32) 357175000000 2 = true :=
    take_step (n := 2) (t := 32) (b := 19970) rfl rfl ArealUCore.ArealUK.chunk_9984 s85
  have s83 : leavesOK ctxLitU 356556250000 2 ((leaves.drop 19966).take 34) 357175000000 2 = true :=
    take_step (n := 2) (t := 34) (b := 19968) rfl rfl ArealUCore.ArealUK.chunk_9983 s84
  have s82 : leavesOK ctxLitU 356543750000 2 ((leaves.drop 19964).take 36) 357175000000 2 = true :=
    take_step (n := 2) (t := 36) (b := 19966) rfl rfl ArealUCore.ArealUK.chunk_9982 s83
  have s81 : leavesOK ctxLitU 178262500000 1 ((leaves.drop 19962).take 38) 357175000000 2 = true :=
    take_step (n := 2) (t := 38) (b := 19964) rfl rfl ArealUCore.ArealUK.chunk_9981 s82
  have s80 : leavesOK ctxLitU 178250000000 1 ((leaves.drop 19960).take 40) 357175000000 2 = true :=
    take_step (n := 2) (t := 40) (b := 19962) rfl rfl ArealUCore.ArealUK.chunk_9980 s81
  have s79 : leavesOK ctxLitU 356487500000 2 ((leaves.drop 19958).take 42) 357175000000 2 = true :=
    take_step (n := 2) (t := 42) (b := 19960) rfl rfl ArealUCore.ArealUK.chunk_9979 s80
  have s78 : leavesOK ctxLitU 89112500000 0 ((leaves.drop 19956).take 44) 357175000000 2 = true :=
    take_step (n := 2) (t := 44) (b := 19958) rfl rfl ArealUCore.ArealUK.chunk_9978 s79
  have s77 : leavesOK ctxLitU 356431250000 2 ((leaves.drop 19954).take 46) 357175000000 2 = true :=
    take_step (n := 2) (t := 46) (b := 19956) rfl rfl ArealUCore.ArealUK.chunk_9977 s78
  have s76 : leavesOK ctxLitU 178206250000 1 ((leaves.drop 19952).take 48) 357175000000 2 = true :=
    take_step (n := 2) (t := 48) (b := 19954) rfl rfl ArealUCore.ArealUK.chunk_9976 s77
  have s75 : leavesOK ctxLitU 178193750000 1 ((leaves.drop 19950).take 50) 357175000000 2 = true :=
    take_step (n := 2) (t := 50) (b := 19952) rfl rfl ArealUCore.ArealUK.chunk_9975 s76
  have s74 : leavesOK ctxLitU 712756250000 3 ((leaves.drop 19948).take 52) 357175000000 2 = true :=
    take_step (n := 2) (t := 52) (b := 19950) rfl rfl ArealUCore.ArealUK.chunk_9974 s75
  have s73 : leavesOK ctxLitU 356368750000 2 ((leaves.drop 19946).take 54) 357175000000 2 = true :=
    take_step (n := 2) (t := 54) (b := 19948) rfl rfl ArealUCore.ArealUK.chunk_9973 s74
  have s72 : leavesOK ctxLitU 178175000000 1 ((leaves.drop 19944).take 56) 357175000000 2 = true :=
    take_step (n := 2) (t := 56) (b := 19946) rfl rfl ArealUCore.ArealUK.chunk_9972 s73
  have s71 : leavesOK ctxLitU 89075000000 0 ((leaves.drop 19942).take 58) 357175000000 2 = true :=
    take_step (n := 2) (t := 58) (b := 19944) rfl rfl ArealUCore.ArealUK.chunk_9971 s72
  have s70 : leavesOK ctxLitU 89050000000 0 ((leaves.drop 19940).take 60) 357175000000 2 = true :=
    take_step (n := 2) (t := 60) (b := 19942) rfl rfl ArealUCore.ArealUK.chunk_9970 s71
  have s69 : leavesOK ctxLitU 89000000000 0 ((leaves.drop 19938).take 62) 357175000000 2 = true :=
    take_step (n := 2) (t := 62) (b := 19940) rfl rfl ArealUCore.ArealUK.chunk_9969 s70
  have s68 : leavesOK ctxLitU 88950000000 0 ((leaves.drop 19936).take 64) 357175000000 2 = true :=
    take_step (n := 2) (t := 64) (b := 19938) rfl rfl ArealUCore.ArealUK.chunk_9968 s69
  have s67 : leavesOK ctxLitU 88900000000 0 ((leaves.drop 19934).take 66) 357175000000 2 = true :=
    take_step (n := 2) (t := 66) (b := 19936) rfl rfl ArealUCore.ArealUK.chunk_9967 s68
  have s66 : leavesOK ctxLitU 88850000000 0 ((leaves.drop 19932).take 68) 357175000000 2 = true :=
    take_step (n := 2) (t := 68) (b := 19934) rfl rfl ArealUCore.ArealUK.chunk_9966 s67
  have s65 : leavesOK ctxLitU 363857370884834 12 ((leaves.drop 19930).take 70) 357175000000 2 = true :=
    take_step (n := 2) (t := 70) (b := 19932) rfl rfl ArealUCore.ArealUK.chunk_9965 s66
  have s64 : leavesOK ctxLitU 88800000000 0 ((leaves.drop 19928).take 72) 357175000000 2 = true :=
    take_step (n := 2) (t := 72) (b := 19930) rfl rfl ArealUCore.ArealUK.chunk_9964 s65
  have s63 : leavesOK ctxLitU 88750000000 0 ((leaves.drop 19926).take 74) 357175000000 2 = true :=
    take_step (n := 2) (t := 74) (b := 19928) rfl rfl ArealUCore.ArealUK.chunk_9963 s64
  have s62 : leavesOK ctxLitU 88700000000 0 ((leaves.drop 19924).take 76) 357175000000 2 = true :=
    take_step (n := 2) (t := 76) (b := 19926) rfl rfl ArealUCore.ArealUK.chunk_9962 s63
  have s61 : leavesOK ctxLitU 88650000000 0 ((leaves.drop 19922).take 78) 357175000000 2 = true :=
    take_step (n := 2) (t := 78) (b := 19924) rfl rfl ArealUCore.ArealUK.chunk_9961 s62
  have s60 : leavesOK ctxLitU 88600000000 0 ((leaves.drop 19920).take 80) 357175000000 2 = true :=
    take_step (n := 2) (t := 80) (b := 19922) rfl rfl ArealUCore.ArealUK.chunk_9960 s61
  have s59 : leavesOK ctxLitU 88550000000 0 ((leaves.drop 19918).take 82) 357175000000 2 = true :=
    take_step (n := 2) (t := 82) (b := 19920) rfl rfl ArealUCore.ArealUK.chunk_9959 s60
  have s58 : leavesOK ctxLitU 88500000000 0 ((leaves.drop 19916).take 84) 357175000000 2 = true :=
    take_step (n := 2) (t := 84) (b := 19918) rfl rfl ArealUCore.ArealUK.chunk_9958 s59
  have s57 : leavesOK ctxLitU 88450000000 0 ((leaves.drop 19914).take 86) 357175000000 2 = true :=
    take_step (n := 2) (t := 86) (b := 19916) rfl rfl ArealUCore.ArealUK.chunk_9957 s58
  have s56 : leavesOK ctxLitU 88400000000 0 ((leaves.drop 19912).take 88) 357175000000 2 = true :=
    take_step (n := 2) (t := 88) (b := 19914) rfl rfl ArealUCore.ArealUK.chunk_9956 s57
  have s55 : leavesOK ctxLitU 88350000000 0 ((leaves.drop 19910).take 90) 357175000000 2 = true :=
    take_step (n := 2) (t := 90) (b := 19912) rfl rfl ArealUCore.ArealUK.chunk_9955 s56
  have s54 : leavesOK ctxLitU 88300000000 0 ((leaves.drop 19908).take 92) 357175000000 2 = true :=
    take_step (n := 2) (t := 92) (b := 19910) rfl rfl ArealUCore.ArealUK.chunk_9954 s55
  have s53 : leavesOK ctxLitU 88250000000 0 ((leaves.drop 19906).take 94) 357175000000 2 = true :=
    take_step (n := 2) (t := 94) (b := 19908) rfl rfl ArealUCore.ArealUK.chunk_9953 s54
  have s52 : leavesOK ctxLitU 88200000000 0 ((leaves.drop 19904).take 96) 357175000000 2 = true :=
    take_step (n := 2) (t := 96) (b := 19906) rfl rfl ArealUCore.ArealUK.chunk_9952 s53
  have s51 : leavesOK ctxLitU 361230018674926 12 ((leaves.drop 19902).take 98) 357175000000 2 = true :=
    take_step (n := 2) (t := 98) (b := 19904) rfl rfl ArealUCore.ArealUK.chunk_9951 s52
  have s50 : leavesOK ctxLitU 88150000000 0 ((leaves.drop 19900).take 100) 357175000000 2 = true :=
    take_step (n := 2) (t := 100) (b := 19902) rfl rfl ArealUCore.ArealUK.chunk_9950 s51
  have s49 : leavesOK ctxLitU 88100000000 0 ((leaves.drop 19898).take 102) 357175000000 2 = true :=
    take_step (n := 2) (t := 102) (b := 19900) rfl rfl ArealUCore.ArealUK.chunk_9949 s50
  have s48 : leavesOK ctxLitU 88050000000 0 ((leaves.drop 19896).take 104) 357175000000 2 = true :=
    take_step (n := 2) (t := 104) (b := 19898) rfl rfl ArealUCore.ArealUK.chunk_9948 s49
  have s47 : leavesOK ctxLitU 88000000000 0 ((leaves.drop 19894).take 106) 357175000000 2 = true :=
    take_step (n := 2) (t := 106) (b := 19896) rfl rfl ArealUCore.ArealUK.chunk_9947 s48
  have s46 : leavesOK ctxLitU 87950000000 0 ((leaves.drop 19892).take 108) 357175000000 2 = true :=
    take_step (n := 2) (t := 108) (b := 19894) rfl rfl ArealUCore.ArealUK.chunk_9946 s47
  have s45 : leavesOK ctxLitU 87900000000 0 ((leaves.drop 19890).take 110) 357175000000 2 = true :=
    take_step (n := 2) (t := 110) (b := 19892) rfl rfl ArealUCore.ArealUK.chunk_9945 s46
  have s44 : leavesOK ctxLitU 87850000000 0 ((leaves.drop 19888).take 112) 357175000000 2 = true :=
    take_step (n := 2) (t := 112) (b := 19890) rfl rfl ArealUCore.ArealUK.chunk_9944 s45
  have s43 : leavesOK ctxLitU 87800000000 0 ((leaves.drop 19886).take 114) 357175000000 2 = true :=
    take_step (n := 2) (t := 114) (b := 19888) rfl rfl ArealUCore.ArealUK.chunk_9943 s44
  have s42 : leavesOK ctxLitU 87750000000 0 ((leaves.drop 19884).take 116) 357175000000 2 = true :=
    take_step (n := 2) (t := 116) (b := 19886) rfl rfl ArealUCore.ArealUK.chunk_9942 s43
  have s41 : leavesOK ctxLitU 87712500000 0 ((leaves.drop 19882).take 118) 357175000000 2 = true :=
    take_step (n := 2) (t := 118) (b := 19884) rfl rfl ArealUCore.ArealUK.chunk_9941 s42
  have s40 : leavesOK ctxLitU 87693750000 0 ((leaves.drop 19880).take 120) 357175000000 2 = true :=
    take_step (n := 2) (t := 120) (b := 19882) rfl rfl ArealUCore.ArealUK.chunk_9940 s41
  have s39 : leavesOK ctxLitU 87681250000 0 ((leaves.drop 19878).take 122) 357175000000 2 = true :=
    take_step (n := 2) (t := 122) (b := 19880) rfl rfl ArealUCore.ArealUK.chunk_9939 s40
  have s38 : leavesOK ctxLitU 175343750000 1 ((leaves.drop 19876).take 124) 357175000000 2 = true :=
    take_step (n := 2) (t := 124) (b := 19878) rfl rfl ArealUCore.ArealUK.chunk_9938 s39
  have s37 : leavesOK ctxLitU 350675000000 2 ((leaves.drop 19874).take 126) 357175000000 2 = true :=
    take_step (n := 2) (t := 126) (b := 19876) rfl rfl ArealUCore.ArealUK.chunk_9937 s38
  have s36 : leavesOK ctxLitU 701337500000 3 ((leaves.drop 19872).take 128) 357175000000 2 = true :=
    take_step (n := 2) (t := 128) (b := 19874) rfl rfl ArealUCore.ArealUK.chunk_9936 s37
  have s35 : leavesOK ctxLitU 175325000000 1 ((leaves.drop 19870).take 130) 357175000000 2 = true :=
    take_step (n := 2) (t := 130) (b := 19872) rfl rfl ArealUCore.ArealUK.chunk_9935 s36
  have s34 : leavesOK ctxLitU 175306250000 1 ((leaves.drop 19868).take 132) 357175000000 2 = true :=
    take_step (n := 2) (t := 132) (b := 19870) rfl rfl ArealUCore.ArealUK.chunk_9934 s35
  have s33 : leavesOK ctxLitU 175293750000 1 ((leaves.drop 19866).take 134) 357175000000 2 = true :=
    take_step (n := 2) (t := 134) (b := 19868) rfl rfl ArealUCore.ArealUK.chunk_9933 s34
  have s32 : leavesOK ctxLitU 87637500000 0 ((leaves.drop 19864).take 136) 357175000000 2 = true :=
    take_step (n := 2) (t := 136) (b := 19866) rfl rfl ArealUCore.ArealUK.chunk_9932 s33
  have s31 : leavesOK ctxLitU 175256250000 1 ((leaves.drop 19862).take 138) 357175000000 2 = true :=
    take_step (n := 2) (t := 138) (b := 19864) rfl rfl ArealUCore.ArealUK.chunk_9931 s32
  have s30 : leavesOK ctxLitU 350500000000 2 ((leaves.drop 19860).take 140) 357175000000 2 = true :=
    take_step (n := 2) (t := 140) (b := 19862) rfl rfl ArealUCore.ArealUK.chunk_9930 s31
  have s29 : leavesOK ctxLitU 700975000000 3 ((leaves.drop 19858).take 142) 357175000000 2 = true :=
    take_step (n := 2) (t := 142) (b := 19860) rfl rfl ArealUCore.ArealUK.chunk_9929 s30
  have s28 : leavesOK ctxLitU 175225000000 1 ((leaves.drop 19856).take 144) 357175000000 2 = true :=
    take_step (n := 2) (t := 144) (b := 19858) rfl rfl ArealUCore.ArealUK.chunk_9928 s29
  have s27 : leavesOK ctxLitU 175200000000 1 ((leaves.drop 19854).take 146) 357175000000 2 = true :=
    take_step (n := 2) (t := 146) (b := 19856) rfl rfl ArealUCore.ArealUK.chunk_9927 s28
  have s26 : leavesOK ctxLitU 700750000000 3 ((leaves.drop 19852).take 148) 357175000000 2 = true :=
    take_step (n := 2) (t := 148) (b := 19854) rfl rfl ArealUCore.ArealUK.chunk_9926 s27
  have s25 : leavesOK ctxLitU 700700000000 3 ((leaves.drop 19850).take 150) 357175000000 2 = true :=
    take_step (n := 2) (t := 150) (b := 19852) rfl rfl ArealUCore.ArealUK.chunk_9925 s26
  have s24 : leavesOK ctxLitU 700650000000 3 ((leaves.drop 19848).take 152) 357175000000 2 = true :=
    take_step (n := 2) (t := 152) (b := 19850) rfl rfl ArealUCore.ArealUK.chunk_9924 s25
  have s23 : leavesOK ctxLitU 700600000000 3 ((leaves.drop 19846).take 154) 357175000000 2 = true :=
    take_step (n := 2) (t := 154) (b := 19848) rfl rfl ArealUCore.ArealUK.chunk_9923 s24
  have s22 : leavesOK ctxLitU 350250000000 2 ((leaves.drop 19844).take 156) 357175000000 2 = true :=
    take_step (n := 2) (t := 156) (b := 19846) rfl rfl ArealUCore.ArealUK.chunk_9922 s23
  have s21 : leavesOK ctxLitU 350200000000 2 ((leaves.drop 19842).take 158) 357175000000 2 = true :=
    take_step (n := 2) (t := 158) (b := 19844) rfl rfl ArealUCore.ArealUK.chunk_9921 s22
  have s20 : leavesOK ctxLitU 350150000000 2 ((leaves.drop 19840).take 160) 357175000000 2 = true :=
    take_step (n := 2) (t := 160) (b := 19842) rfl rfl ArealUCore.ArealUK.chunk_9920 s21
  have s19 : leavesOK ctxLitU 350100000000 2 ((leaves.drop 19838).take 162) 357175000000 2 = true :=
    take_step (n := 2) (t := 162) (b := 19840) rfl rfl ArealUCore.ArealUK.chunk_9919 s20
  have s18 : leavesOK ctxLitU 700150000000 3 ((leaves.drop 19836).take 164) 357175000000 2 = true :=
    take_step (n := 2) (t := 164) (b := 19838) rfl rfl ArealUCore.ArealUK.chunk_9918 s19
  have s17 : leavesOK ctxLitU 700100000000 3 ((leaves.drop 19834).take 166) 357175000000 2 = true :=
    take_step (n := 2) (t := 166) (b := 19836) rfl rfl ArealUCore.ArealUK.chunk_9917 s18
  have s16 : leavesOK ctxLitU 700050000000 3 ((leaves.drop 19832).take 168) 357175000000 2 = true :=
    take_step (n := 2) (t := 168) (b := 19834) rfl rfl ArealUCore.ArealUK.chunk_9916 s17
  have s15 : leavesOK ctxLitU 700000000000 3 ((leaves.drop 19830).take 170) 357175000000 2 = true :=
    take_step (n := 2) (t := 170) (b := 19832) rfl rfl ArealUCore.ArealUK.chunk_9915 s16
  have s14 : leavesOK ctxLitU 699950000000 3 ((leaves.drop 19828).take 172) 357175000000 2 = true :=
    take_step (n := 2) (t := 172) (b := 19830) rfl rfl ArealUCore.ArealUK.chunk_9914 s15
  have s13 : leavesOK ctxLitU 699900000000 3 ((leaves.drop 19826).take 174) 357175000000 2 = true :=
    take_step (n := 2) (t := 174) (b := 19828) rfl rfl ArealUCore.ArealUK.chunk_9913 s14
  have s12 : leavesOK ctxLitU 699850000000 3 ((leaves.drop 19824).take 176) 357175000000 2 = true :=
    take_step (n := 2) (t := 176) (b := 19826) rfl rfl ArealUCore.ArealUK.chunk_9912 s13
  have s11 : leavesOK ctxLitU 699800000000 3 ((leaves.drop 19822).take 178) 357175000000 2 = true :=
    take_step (n := 2) (t := 178) (b := 19824) rfl rfl ArealUCore.ArealUK.chunk_9911 s12
  have s10 : leavesOK ctxLitU 349850000000 2 ((leaves.drop 19820).take 180) 357175000000 2 = true :=
    take_step (n := 2) (t := 180) (b := 19822) rfl rfl ArealUCore.ArealUK.chunk_9910 s11
  have s9 : leavesOK ctxLitU 349800000000 2 ((leaves.drop 19818).take 182) 357175000000 2 = true :=
    take_step (n := 2) (t := 182) (b := 19820) rfl rfl ArealUCore.ArealUK.chunk_9909 s10
  have s8 : leavesOK ctxLitU 349750000000 2 ((leaves.drop 19816).take 184) 357175000000 2 = true :=
    take_step (n := 2) (t := 184) (b := 19818) rfl rfl ArealUCore.ArealUK.chunk_9908 s9
  have s7 : leavesOK ctxLitU 699425000000 3 ((leaves.drop 19814).take 186) 357175000000 2 = true :=
    take_step (n := 2) (t := 186) (b := 19816) rfl rfl ArealUCore.ArealUK.chunk_9907 s8
  have s6 : leavesOK ctxLitU 699375000000 3 ((leaves.drop 19812).take 188) 357175000000 2 = true :=
    take_step (n := 2) (t := 188) (b := 19814) rfl rfl ArealUCore.ArealUK.chunk_9906 s7
  have s5 : leavesOK ctxLitU 699325000000 3 ((leaves.drop 19810).take 190) 357175000000 2 = true :=
    take_step (n := 2) (t := 190) (b := 19812) rfl rfl ArealUCore.ArealUK.chunk_9905 s6
  have s4 : leavesOK ctxLitU 699275000000 3 ((leaves.drop 19808).take 192) 357175000000 2 = true :=
    take_step (n := 2) (t := 192) (b := 19810) rfl rfl ArealUCore.ArealUK.chunk_9904 s5
  have s3 : leavesOK ctxLitU 699225000000 3 ((leaves.drop 19806).take 194) 357175000000 2 = true :=
    take_step (n := 2) (t := 194) (b := 19808) rfl rfl ArealUCore.ArealUK.chunk_9903 s4
  have s2 : leavesOK ctxLitU 699175000000 3 ((leaves.drop 19804).take 196) 357175000000 2 = true :=
    take_step (n := 2) (t := 196) (b := 19806) rfl rfl ArealUCore.ArealUK.chunk_9902 s3
  have s1 : leavesOK ctxLitU 699125000000 3 ((leaves.drop 19802).take 198) 357175000000 2 = true :=
    take_step (n := 2) (t := 198) (b := 19804) rfl rfl ArealUCore.ArealUK.chunk_9901 s2
  have s0 : leavesOK ctxLitU 699075000000 3 ((leaves.drop 19800).take 200) 357175000000 2 = true :=
    take_step (n := 2) (t := 200) (b := 19802) rfl rfl ArealUCore.ArealUK.chunk_9900 s1
  exact s0

end Areal.UCert

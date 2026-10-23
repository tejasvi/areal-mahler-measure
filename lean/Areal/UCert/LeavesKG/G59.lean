import ArealUK.Chunk5900
import ArealUK.Chunk5901
import ArealUK.Chunk5902
import ArealUK.Chunk5903
import ArealUK.Chunk5904
import ArealUK.Chunk5905
import ArealUK.Chunk5906
import ArealUK.Chunk5907
import ArealUK.Chunk5908
import ArealUK.Chunk5909
import ArealUK.Chunk5910
import ArealUK.Chunk5911
import ArealUK.Chunk5912
import ArealUK.Chunk5913
import ArealUK.Chunk5914
import ArealUK.Chunk5915
import ArealUK.Chunk5916
import ArealUK.Chunk5917
import ArealUK.Chunk5918
import ArealUK.Chunk5919
import ArealUK.Chunk5920
import ArealUK.Chunk5921
import ArealUK.Chunk5922
import ArealUK.Chunk5923
import ArealUK.Chunk5924
import ArealUK.Chunk5925
import ArealUK.Chunk5926
import ArealUK.Chunk5927
import ArealUK.Chunk5928
import ArealUK.Chunk5929
import ArealUK.Chunk5930
import ArealUK.Chunk5931
import ArealUK.Chunk5932
import ArealUK.Chunk5933
import ArealUK.Chunk5934
import ArealUK.Chunk5935
import ArealUK.Chunk5936
import ArealUK.Chunk5937
import ArealUK.Chunk5938
import ArealUK.Chunk5939
import ArealUK.Chunk5940
import ArealUK.Chunk5941
import ArealUK.Chunk5942
import ArealUK.Chunk5943
import ArealUK.Chunk5944
import ArealUK.Chunk5945
import ArealUK.Chunk5946
import ArealUK.Chunk5947
import ArealUK.Chunk5948
import ArealUK.Chunk5949
import ArealUK.Chunk5950
import ArealUK.Chunk5951
import ArealUK.Chunk5952
import ArealUK.Chunk5953
import ArealUK.Chunk5954
import ArealUK.Chunk5955
import ArealUK.Chunk5956
import ArealUK.Chunk5957
import ArealUK.Chunk5958
import ArealUK.Chunk5959
import ArealUK.Chunk5960
import ArealUK.Chunk5961
import ArealUK.Chunk5962
import ArealUK.Chunk5963
import ArealUK.Chunk5964
import ArealUK.Chunk5965
import ArealUK.Chunk5966
import ArealUK.Chunk5967
import ArealUK.Chunk5968
import ArealUK.Chunk5969
import ArealUK.Chunk5970
import ArealUK.Chunk5971
import ArealUK.Chunk5972
import ArealUK.Chunk5973
import ArealUK.Chunk5974
import ArealUK.Chunk5975
import ArealUK.Chunk5976
import ArealUK.Chunk5977
import ArealUK.Chunk5978
import ArealUK.Chunk5979
import ArealUK.Chunk5980
import ArealUK.Chunk5981
import ArealUK.Chunk5982
import ArealUK.Chunk5983
import ArealUK.Chunk5984
import ArealUK.Chunk5985
import ArealUK.Chunk5986
import ArealUK.Chunk5987
import ArealUK.Chunk5988
import ArealUK.Chunk5989
import ArealUK.Chunk5990
import ArealUK.Chunk5991
import ArealUK.Chunk5992
import ArealUK.Chunk5993
import ArealUK.Chunk5994
import ArealUK.Chunk5995
import ArealUK.Chunk5996
import ArealUK.Chunk5997
import ArealUK.Chunk5998
import ArealUK.Chunk5999
import Areal.UCert.LeavesKGen

/-! Group 59 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_59 : leavesOK ctxLitU 305500000000 3 ((leaves.drop 11800).take 200) 314275000000 3 = true := by
  have s99 := ArealUCore.ArealUK.chunk_5999
  have s98 : leavesOK ctxLitU 314175000000 3 ((leaves.drop 11996).take 4) 314275000000 3 = true :=
    take_step (n := 2) (t := 4) (b := 11998) rfl rfl ArealUCore.ArealUK.chunk_5998 s99
  have s97 : leavesOK ctxLitU 314125000000 3 ((leaves.drop 11994).take 6) 314275000000 3 = true :=
    take_step (n := 2) (t := 6) (b := 11996) rfl rfl ArealUCore.ArealUK.chunk_5997 s98
  have s96 : leavesOK ctxLitU 314075000000 3 ((leaves.drop 11992).take 8) 314275000000 3 = true :=
    take_step (n := 2) (t := 8) (b := 11994) rfl rfl ArealUCore.ArealUK.chunk_5996 s97
  have s95 : leavesOK ctxLitU 314025000000 3 ((leaves.drop 11990).take 10) 314275000000 3 = true :=
    take_step (n := 2) (t := 10) (b := 11992) rfl rfl ArealUCore.ArealUK.chunk_5995 s96
  have s94 : leavesOK ctxLitU 156987500000 2 ((leaves.drop 11988).take 12) 314275000000 3 = true :=
    take_step (n := 2) (t := 12) (b := 11990) rfl rfl ArealUCore.ArealUK.chunk_5994 s95
  have s93 : leavesOK ctxLitU 156962500000 2 ((leaves.drop 11986).take 14) 314275000000 3 = true :=
    take_step (n := 2) (t := 14) (b := 11988) rfl rfl ArealUCore.ArealUK.chunk_5993 s94
  have s92 : leavesOK ctxLitU 156937500000 2 ((leaves.drop 11984).take 16) 314275000000 3 = true :=
    take_step (n := 2) (t := 16) (b := 11986) rfl rfl ArealUCore.ArealUK.chunk_5992 s93
  have s91 : leavesOK ctxLitU 156912500000 2 ((leaves.drop 11982).take 18) 314275000000 3 = true :=
    take_step (n := 2) (t := 18) (b := 11984) rfl rfl ArealUCore.ArealUK.chunk_5991 s92
  have s90 : leavesOK ctxLitU 313800000000 3 ((leaves.drop 11980).take 20) 314275000000 3 = true :=
    take_step (n := 2) (t := 20) (b := 11982) rfl rfl ArealUCore.ArealUK.chunk_5990 s91
  have s89 : leavesOK ctxLitU 78437500000 1 ((leaves.drop 11978).take 22) 314275000000 3 = true :=
    take_step (n := 2) (t := 22) (b := 11980) rfl rfl ArealUCore.ArealUK.chunk_5989 s90
  have s88 : leavesOK ctxLitU 156856250000 2 ((leaves.drop 11976).take 24) 314275000000 3 = true :=
    take_step (n := 2) (t := 24) (b := 11978) rfl rfl ArealUCore.ArealUK.chunk_5988 s89
  have s87 : leavesOK ctxLitU 156843750000 2 ((leaves.drop 11974).take 26) 314275000000 3 = true :=
    take_step (n := 2) (t := 26) (b := 11976) rfl rfl ArealUCore.ArealUK.chunk_5987 s88
  have s86 : leavesOK ctxLitU 78412500000 1 ((leaves.drop 11972).take 28) 314275000000 3 = true :=
    take_step (n := 2) (t := 28) (b := 11974) rfl rfl ArealUCore.ArealUK.chunk_5986 s87
  have s85 : leavesOK ctxLitU 78400000000 1 ((leaves.drop 11970).take 30) 314275000000 3 = true :=
    take_step (n := 2) (t := 30) (b := 11972) rfl rfl ArealUCore.ArealUK.chunk_5985 s86
  have s84 : leavesOK ctxLitU 78387500000 1 ((leaves.drop 11968).take 32) 314275000000 3 = true :=
    take_step (n := 2) (t := 32) (b := 11970) rfl rfl ArealUCore.ArealUK.chunk_5984 s85
  have s83 : leavesOK ctxLitU 156762500000 2 ((leaves.drop 11966).take 34) 314275000000 3 = true :=
    take_step (n := 2) (t := 34) (b := 11968) rfl rfl ArealUCore.ArealUK.chunk_5983 s84
  have s82 : leavesOK ctxLitU 313506250000 3 ((leaves.drop 11964).take 36) 314275000000 3 = true :=
    take_step (n := 2) (t := 36) (b := 11966) rfl rfl ArealUCore.ArealUK.chunk_5982 s83
  have s81 : leavesOK ctxLitU 156743750000 2 ((leaves.drop 11962).take 38) 314275000000 3 = true :=
    take_step (n := 2) (t := 38) (b := 11964) rfl rfl ArealUCore.ArealUK.chunk_5981 s82
  have s80 : leavesOK ctxLitU 78362500000 1 ((leaves.drop 11960).take 40) 314275000000 3 = true :=
    take_step (n := 2) (t := 40) (b := 11962) rfl rfl ArealUCore.ArealUK.chunk_5980 s81
  have s79 : leavesOK ctxLitU 39168750000 0 ((leaves.drop 11958).take 42) 314275000000 3 = true :=
    take_step (n := 2) (t := 42) (b := 11960) rfl rfl ArealUCore.ArealUK.chunk_5979 s80
  have s78 : leavesOK ctxLitU 39156250000 0 ((leaves.drop 11956).take 44) 314275000000 3 = true :=
    take_step (n := 2) (t := 44) (b := 11958) rfl rfl ArealUCore.ArealUK.chunk_5978 s79
  have s77 : leavesOK ctxLitU 39143750000 0 ((leaves.drop 11954).take 46) 314275000000 3 = true :=
    take_step (n := 2) (t := 46) (b := 11956) rfl rfl ArealUCore.ArealUK.chunk_5977 s78
  have s76 : leavesOK ctxLitU 39131250000 0 ((leaves.drop 11952).take 48) 314275000000 3 = true :=
    take_step (n := 2) (t := 48) (b := 11954) rfl rfl ArealUCore.ArealUK.chunk_5976 s77
  have s75 : leavesOK ctxLitU 39112500000 0 ((leaves.drop 11950).take 50) 314275000000 3 = true :=
    take_step (n := 2) (t := 50) (b := 11952) rfl rfl ArealUCore.ArealUK.chunk_5975 s76
  have s74 : leavesOK ctxLitU 39075000000 0 ((leaves.drop 11948).take 52) 314275000000 3 = true :=
    take_step (n := 2) (t := 52) (b := 11950) rfl rfl ArealUCore.ArealUK.chunk_5974 s75
  have s73 : leavesOK ctxLitU 39025000000 0 ((leaves.drop 11946).take 54) 314275000000 3 = true :=
    take_step (n := 2) (t := 54) (b := 11948) rfl rfl ArealUCore.ArealUK.chunk_5973 s74
  have s72 : leavesOK ctxLitU 38975000000 0 ((leaves.drop 11944).take 56) 314275000000 3 = true :=
    take_step (n := 2) (t := 56) (b := 11946) rfl rfl ArealUCore.ArealUK.chunk_5972 s73
  have s71 : leavesOK ctxLitU 38925000000 0 ((leaves.drop 11942).take 58) 314275000000 3 = true :=
    take_step (n := 2) (t := 58) (b := 11944) rfl rfl ArealUCore.ArealUK.chunk_5971 s72
  have s70 : leavesOK ctxLitU 38887500000 0 ((leaves.drop 11940).take 60) 314275000000 3 = true :=
    take_step (n := 2) (t := 60) (b := 11942) rfl rfl ArealUCore.ArealUK.chunk_5970 s71
  have s69 : leavesOK ctxLitU 38868750000 0 ((leaves.drop 11938).take 62) 314275000000 3 = true :=
    take_step (n := 2) (t := 62) (b := 11940) rfl rfl ArealUCore.ArealUK.chunk_5969 s70
  have s68 : leavesOK ctxLitU 38856250000 0 ((leaves.drop 11936).take 64) 314275000000 3 = true :=
    take_step (n := 2) (t := 64) (b := 11938) rfl rfl ArealUCore.ArealUK.chunk_5968 s69
  have s67 : leavesOK ctxLitU 38843750000 0 ((leaves.drop 11934).take 66) 314275000000 3 = true :=
    take_step (n := 2) (t := 66) (b := 11936) rfl rfl ArealUCore.ArealUK.chunk_5967 s68
  have s66 : leavesOK ctxLitU 159056802175730 12 ((leaves.drop 11932).take 68) 314275000000 3 = true :=
    take_step (n := 2) (t := 68) (b := 11934) rfl rfl ArealUCore.ArealUK.chunk_5966 s67
  have s65 : leavesOK ctxLitU 159052800000000 12 ((leaves.drop 11930).take 70) 314275000000 3 = true :=
    take_step (n := 2) (t := 70) (b := 11932) rfl rfl ArealUCore.ArealUK.chunk_5965 s66
  have s64 : leavesOK ctxLitU 38818750000 0 ((leaves.drop 11928).take 72) 314275000000 3 = true :=
    take_step (n := 2) (t := 72) (b := 11930) rfl rfl ArealUCore.ArealUK.chunk_5964 s65
  have s63 : leavesOK ctxLitU 38806250000 0 ((leaves.drop 11926).take 74) 314275000000 3 = true :=
    take_step (n := 2) (t := 74) (b := 11928) rfl rfl ArealUCore.ArealUK.chunk_5963 s64
  have s62 : leavesOK ctxLitU 38787500000 0 ((leaves.drop 11924).take 76) 314275000000 3 = true :=
    take_step (n := 2) (t := 76) (b := 11926) rfl rfl ArealUCore.ArealUK.chunk_5962 s63
  have s61 : leavesOK ctxLitU 38750000000 0 ((leaves.drop 11922).take 78) 314275000000 3 = true :=
    take_step (n := 2) (t := 78) (b := 11924) rfl rfl ArealUCore.ArealUK.chunk_5961 s62
  have s60 : leavesOK ctxLitU 38700000000 0 ((leaves.drop 11920).take 80) 314275000000 3 = true :=
    take_step (n := 2) (t := 80) (b := 11922) rfl rfl ArealUCore.ArealUK.chunk_5960 s61
  have s59 : leavesOK ctxLitU 38650000000 0 ((leaves.drop 11918).take 82) 314275000000 3 = true :=
    take_step (n := 2) (t := 82) (b := 11920) rfl rfl ArealUCore.ArealUK.chunk_5959 s60
  have s58 : leavesOK ctxLitU 38600000000 0 ((leaves.drop 11916).take 84) 314275000000 3 = true :=
    take_step (n := 2) (t := 84) (b := 11918) rfl rfl ArealUCore.ArealUK.chunk_5958 s59
  have s57 : leavesOK ctxLitU 38562500000 0 ((leaves.drop 11914).take 86) 314275000000 3 = true :=
    take_step (n := 2) (t := 86) (b := 11916) rfl rfl ArealUCore.ArealUK.chunk_5957 s58
  have s56 : leavesOK ctxLitU 38543750000 0 ((leaves.drop 11912).take 88) 314275000000 3 = true :=
    take_step (n := 2) (t := 88) (b := 11914) rfl rfl ArealUCore.ArealUK.chunk_5956 s57
  have s55 : leavesOK ctxLitU 38531250000 0 ((leaves.drop 11910).take 90) 314275000000 3 = true :=
    take_step (n := 2) (t := 90) (b := 11912) rfl rfl ArealUCore.ArealUK.chunk_5955 s56
  have s54 : leavesOK ctxLitU 38518750000 0 ((leaves.drop 11908).take 92) 314275000000 3 = true :=
    take_step (n := 2) (t := 92) (b := 11910) rfl rfl ArealUCore.ArealUK.chunk_5954 s55
  have s53 : leavesOK ctxLitU 38506250000 0 ((leaves.drop 11906).take 94) 314275000000 3 = true :=
    take_step (n := 2) (t := 94) (b := 11908) rfl rfl ArealUCore.ArealUK.chunk_5953 s54
  have s52 : leavesOK ctxLitU 38493750000 0 ((leaves.drop 11904).take 96) 314275000000 3 = true :=
    take_step (n := 2) (t := 96) (b := 11906) rfl rfl ArealUCore.ArealUK.chunk_5952 s53
  have s51 : leavesOK ctxLitU 153956250000 2 ((leaves.drop 11902).take 98) 314275000000 3 = true :=
    take_step (n := 2) (t := 98) (b := 11904) rfl rfl ArealUCore.ArealUK.chunk_5951 s52
  have s50 : leavesOK ctxLitU 307893750000 3 ((leaves.drop 11900).take 100) 314275000000 3 = true :=
    take_step (n := 2) (t := 100) (b := 11902) rfl rfl ArealUCore.ArealUK.chunk_5950 s51
  have s49 : leavesOK ctxLitU 153937500000 2 ((leaves.drop 11898).take 102) 314275000000 3 = true :=
    take_step (n := 2) (t := 102) (b := 11900) rfl rfl ArealUCore.ArealUK.chunk_5949 s50
  have s48 : leavesOK ctxLitU 153925000000 2 ((leaves.drop 11896).take 104) 314275000000 3 = true :=
    take_step (n := 2) (t := 104) (b := 11898) rfl rfl ArealUCore.ArealUK.chunk_5948 s49
  have s47 : leavesOK ctxLitU 76950000000 1 ((leaves.drop 11894).take 106) 314275000000 3 = true :=
    take_step (n := 2) (t := 106) (b := 11896) rfl rfl ArealUCore.ArealUK.chunk_5947 s48
  have s46 : leavesOK ctxLitU 76937500000 1 ((leaves.drop 11892).take 108) 314275000000 3 = true :=
    take_step (n := 2) (t := 108) (b := 11894) rfl rfl ArealUCore.ArealUK.chunk_5946 s47
  have s45 : leavesOK ctxLitU 76925000000 1 ((leaves.drop 11890).take 110) 314275000000 3 = true :=
    take_step (n := 2) (t := 110) (b := 11892) rfl rfl ArealUCore.ArealUK.chunk_5945 s46
  have s44 : leavesOK ctxLitU 153831250000 2 ((leaves.drop 11888).take 112) 314275000000 3 = true :=
    take_step (n := 2) (t := 112) (b := 11890) rfl rfl ArealUCore.ArealUK.chunk_5944 s45
  have s43 : leavesOK ctxLitU 153818750000 2 ((leaves.drop 11886).take 114) 314275000000 3 = true :=
    take_step (n := 2) (t := 114) (b := 11888) rfl rfl ArealUCore.ArealUK.chunk_5943 s44
  have s42 : leavesOK ctxLitU 76900000000 1 ((leaves.drop 11884).take 116) 314275000000 3 = true :=
    take_step (n := 2) (t := 116) (b := 11886) rfl rfl ArealUCore.ArealUK.chunk_5942 s43
  have s41 : leavesOK ctxLitU 153775000000 2 ((leaves.drop 11882).take 118) 314275000000 3 = true :=
    take_step (n := 2) (t := 118) (b := 11884) rfl rfl ArealUCore.ArealUK.chunk_5941 s42
  have s40 : leavesOK ctxLitU 153750000000 2 ((leaves.drop 11880).take 120) 314275000000 3 = true :=
    take_step (n := 2) (t := 120) (b := 11882) rfl rfl ArealUCore.ArealUK.chunk_5940 s41
  have s39 : leavesOK ctxLitU 153725000000 2 ((leaves.drop 11878).take 122) 314275000000 3 = true :=
    take_step (n := 2) (t := 122) (b := 11880) rfl rfl ArealUCore.ArealUK.chunk_5939 s40
  have s38 : leavesOK ctxLitU 153700000000 2 ((leaves.drop 11876).take 124) 314275000000 3 = true :=
    take_step (n := 2) (t := 124) (b := 11878) rfl rfl ArealUCore.ArealUK.chunk_5938 s39
  have s37 : leavesOK ctxLitU 307350000000 3 ((leaves.drop 11874).take 126) 314275000000 3 = true :=
    take_step (n := 2) (t := 126) (b := 11876) rfl rfl ArealUCore.ArealUK.chunk_5937 s38
  have s36 : leavesOK ctxLitU 307300000000 3 ((leaves.drop 11872).take 128) 314275000000 3 = true :=
    take_step (n := 2) (t := 128) (b := 11874) rfl rfl ArealUCore.ArealUK.chunk_5936 s37
  have s35 : leavesOK ctxLitU 307250000000 3 ((leaves.drop 11870).take 130) 314275000000 3 = true :=
    take_step (n := 2) (t := 130) (b := 11872) rfl rfl ArealUCore.ArealUK.chunk_5935 s36
  have s34 : leavesOK ctxLitU 307200000000 3 ((leaves.drop 11868).take 132) 314275000000 3 = true :=
    take_step (n := 2) (t := 132) (b := 11870) rfl rfl ArealUCore.ArealUK.chunk_5934 s35
  have s33 : leavesOK ctxLitU 307150000000 3 ((leaves.drop 11866).take 134) 314275000000 3 = true :=
    take_step (n := 2) (t := 134) (b := 11868) rfl rfl ArealUCore.ArealUK.chunk_5933 s34
  have s32 : leavesOK ctxLitU 307100000000 3 ((leaves.drop 11864).take 136) 314275000000 3 = true :=
    take_step (n := 2) (t := 136) (b := 11866) rfl rfl ArealUCore.ArealUK.chunk_5932 s33
  have s31 : leavesOK ctxLitU 307050000000 3 ((leaves.drop 11862).take 138) 314275000000 3 = true :=
    take_step (n := 2) (t := 138) (b := 11864) rfl rfl ArealUCore.ArealUK.chunk_5931 s32
  have s30 : leavesOK ctxLitU 307000000000 3 ((leaves.drop 11860).take 140) 314275000000 3 = true :=
    take_step (n := 2) (t := 140) (b := 11862) rfl rfl ArealUCore.ArealUK.chunk_5930 s31
  have s29 : leavesOK ctxLitU 306950000000 3 ((leaves.drop 11858).take 142) 314275000000 3 = true :=
    take_step (n := 2) (t := 142) (b := 11860) rfl rfl ArealUCore.ArealUK.chunk_5929 s30
  have s28 : leavesOK ctxLitU 306900000000 3 ((leaves.drop 11856).take 144) 314275000000 3 = true :=
    take_step (n := 2) (t := 144) (b := 11858) rfl rfl ArealUCore.ArealUK.chunk_5928 s29
  have s27 : leavesOK ctxLitU 306850000000 3 ((leaves.drop 11854).take 146) 314275000000 3 = true :=
    take_step (n := 2) (t := 146) (b := 11856) rfl rfl ArealUCore.ArealUK.chunk_5927 s28
  have s26 : leavesOK ctxLitU 306800000000 3 ((leaves.drop 11852).take 148) 314275000000 3 = true :=
    take_step (n := 2) (t := 148) (b := 11854) rfl rfl ArealUCore.ArealUK.chunk_5926 s27
  have s25 : leavesOK ctxLitU 306750000000 3 ((leaves.drop 11850).take 150) 314275000000 3 = true :=
    take_step (n := 2) (t := 150) (b := 11852) rfl rfl ArealUCore.ArealUK.chunk_5925 s26
  have s24 : leavesOK ctxLitU 306700000000 3 ((leaves.drop 11848).take 152) 314275000000 3 = true :=
    take_step (n := 2) (t := 152) (b := 11850) rfl rfl ArealUCore.ArealUK.chunk_5924 s25
  have s23 : leavesOK ctxLitU 306650000000 3 ((leaves.drop 11846).take 154) 314275000000 3 = true :=
    take_step (n := 2) (t := 154) (b := 11848) rfl rfl ArealUCore.ArealUK.chunk_5923 s24
  have s22 : leavesOK ctxLitU 306600000000 3 ((leaves.drop 11844).take 156) 314275000000 3 = true :=
    take_step (n := 2) (t := 156) (b := 11846) rfl rfl ArealUCore.ArealUK.chunk_5922 s23
  have s21 : leavesOK ctxLitU 306550000000 3 ((leaves.drop 11842).take 158) 314275000000 3 = true :=
    take_step (n := 2) (t := 158) (b := 11844) rfl rfl ArealUCore.ArealUK.chunk_5921 s22
  have s20 : leavesOK ctxLitU 306500000000 3 ((leaves.drop 11840).take 160) 314275000000 3 = true :=
    take_step (n := 2) (t := 160) (b := 11842) rfl rfl ArealUCore.ArealUK.chunk_5920 s21
  have s19 : leavesOK ctxLitU 306450000000 3 ((leaves.drop 11838).take 162) 314275000000 3 = true :=
    take_step (n := 2) (t := 162) (b := 11840) rfl rfl ArealUCore.ArealUK.chunk_5919 s20
  have s18 : leavesOK ctxLitU 306400000000 3 ((leaves.drop 11836).take 164) 314275000000 3 = true :=
    take_step (n := 2) (t := 164) (b := 11838) rfl rfl ArealUCore.ArealUK.chunk_5918 s19
  have s17 : leavesOK ctxLitU 306350000000 3 ((leaves.drop 11834).take 166) 314275000000 3 = true :=
    take_step (n := 2) (t := 166) (b := 11836) rfl rfl ArealUCore.ArealUK.chunk_5917 s18
  have s16 : leavesOK ctxLitU 306300000000 3 ((leaves.drop 11832).take 168) 314275000000 3 = true :=
    take_step (n := 2) (t := 168) (b := 11834) rfl rfl ArealUCore.ArealUK.chunk_5916 s17
  have s15 : leavesOK ctxLitU 306250000000 3 ((leaves.drop 11830).take 170) 314275000000 3 = true :=
    take_step (n := 2) (t := 170) (b := 11832) rfl rfl ArealUCore.ArealUK.chunk_5915 s16
  have s14 : leavesOK ctxLitU 306200000000 3 ((leaves.drop 11828).take 172) 314275000000 3 = true :=
    take_step (n := 2) (t := 172) (b := 11830) rfl rfl ArealUCore.ArealUK.chunk_5914 s15
  have s13 : leavesOK ctxLitU 306150000000 3 ((leaves.drop 11826).take 174) 314275000000 3 = true :=
    take_step (n := 2) (t := 174) (b := 11828) rfl rfl ArealUCore.ArealUK.chunk_5913 s14
  have s12 : leavesOK ctxLitU 306100000000 3 ((leaves.drop 11824).take 176) 314275000000 3 = true :=
    take_step (n := 2) (t := 176) (b := 11826) rfl rfl ArealUCore.ArealUK.chunk_5912 s13
  have s11 : leavesOK ctxLitU 306050000000 3 ((leaves.drop 11822).take 178) 314275000000 3 = true :=
    take_step (n := 2) (t := 178) (b := 11824) rfl rfl ArealUCore.ArealUK.chunk_5911 s12
  have s10 : leavesOK ctxLitU 306000000000 3 ((leaves.drop 11820).take 180) 314275000000 3 = true :=
    take_step (n := 2) (t := 180) (b := 11822) rfl rfl ArealUCore.ArealUK.chunk_5910 s11
  have s9 : leavesOK ctxLitU 305950000000 3 ((leaves.drop 11818).take 182) 314275000000 3 = true :=
    take_step (n := 2) (t := 182) (b := 11820) rfl rfl ArealUCore.ArealUK.chunk_5909 s10
  have s8 : leavesOK ctxLitU 305900000000 3 ((leaves.drop 11816).take 184) 314275000000 3 = true :=
    take_step (n := 2) (t := 184) (b := 11818) rfl rfl ArealUCore.ArealUK.chunk_5908 s9
  have s7 : leavesOK ctxLitU 305850000000 3 ((leaves.drop 11814).take 186) 314275000000 3 = true :=
    take_step (n := 2) (t := 186) (b := 11816) rfl rfl ArealUCore.ArealUK.chunk_5907 s8
  have s6 : leavesOK ctxLitU 305800000000 3 ((leaves.drop 11812).take 188) 314275000000 3 = true :=
    take_step (n := 2) (t := 188) (b := 11814) rfl rfl ArealUCore.ArealUK.chunk_5906 s7
  have s5 : leavesOK ctxLitU 305750000000 3 ((leaves.drop 11810).take 190) 314275000000 3 = true :=
    take_step (n := 2) (t := 190) (b := 11812) rfl rfl ArealUCore.ArealUK.chunk_5905 s6
  have s4 : leavesOK ctxLitU 305700000000 3 ((leaves.drop 11808).take 192) 314275000000 3 = true :=
    take_step (n := 2) (t := 192) (b := 11810) rfl rfl ArealUCore.ArealUK.chunk_5904 s5
  have s3 : leavesOK ctxLitU 305650000000 3 ((leaves.drop 11806).take 194) 314275000000 3 = true :=
    take_step (n := 2) (t := 194) (b := 11808) rfl rfl ArealUCore.ArealUK.chunk_5903 s4
  have s2 : leavesOK ctxLitU 305600000000 3 ((leaves.drop 11804).take 196) 314275000000 3 = true :=
    take_step (n := 2) (t := 196) (b := 11806) rfl rfl ArealUCore.ArealUK.chunk_5902 s3
  have s1 : leavesOK ctxLitU 305550000000 3 ((leaves.drop 11802).take 198) 314275000000 3 = true :=
    take_step (n := 2) (t := 198) (b := 11804) rfl rfl ArealUCore.ArealUK.chunk_5901 s2
  have s0 : leavesOK ctxLitU 305500000000 3 ((leaves.drop 11800).take 200) 314275000000 3 = true :=
    take_step (n := 2) (t := 200) (b := 11802) rfl rfl ArealUCore.ArealUK.chunk_5900 s1
  exact s0

end Areal.UCert

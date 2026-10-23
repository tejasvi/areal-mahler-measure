import ArealUK.Chunk15900
import ArealUK.Chunk15901
import ArealUK.Chunk15902
import ArealUK.Chunk15903
import ArealUK.Chunk15904
import ArealUK.Chunk15905
import ArealUK.Chunk15906
import ArealUK.Chunk15907
import ArealUK.Chunk15908
import ArealUK.Chunk15909
import ArealUK.Chunk15910
import ArealUK.Chunk15911
import ArealUK.Chunk15912
import ArealUK.Chunk15913
import ArealUK.Chunk15914
import ArealUK.Chunk15915
import ArealUK.Chunk15916
import ArealUK.Chunk15917
import ArealUK.Chunk15918
import ArealUK.Chunk15919
import ArealUK.Chunk15920
import ArealUK.Chunk15921
import ArealUK.Chunk15922
import ArealUK.Chunk15923
import ArealUK.Chunk15924
import ArealUK.Chunk15925
import ArealUK.Chunk15926
import ArealUK.Chunk15927
import ArealUK.Chunk15928
import ArealUK.Chunk15929
import ArealUK.Chunk15930
import ArealUK.Chunk15931
import ArealUK.Chunk15932
import ArealUK.Chunk15933
import ArealUK.Chunk15934
import ArealUK.Chunk15935
import ArealUK.Chunk15936
import ArealUK.Chunk15937
import ArealUK.Chunk15938
import ArealUK.Chunk15939
import ArealUK.Chunk15940
import ArealUK.Chunk15941
import ArealUK.Chunk15942
import ArealUK.Chunk15943
import ArealUK.Chunk15944
import ArealUK.Chunk15945
import ArealUK.Chunk15946
import ArealUK.Chunk15947
import ArealUK.Chunk15948
import ArealUK.Chunk15949
import ArealUK.Chunk15950
import ArealUK.Chunk15951
import ArealUK.Chunk15952
import ArealUK.Chunk15953
import ArealUK.Chunk15954
import ArealUK.Chunk15955
import ArealUK.Chunk15956
import ArealUK.Chunk15957
import ArealUK.Chunk15958
import ArealUK.Chunk15959
import ArealUK.Chunk15960
import ArealUK.Chunk15961
import ArealUK.Chunk15962
import ArealUK.Chunk15963
import ArealUK.Chunk15964
import ArealUK.Chunk15965
import ArealUK.Chunk15966
import ArealUK.Chunk15967
import ArealUK.Chunk15968
import ArealUK.Chunk15969
import ArealUK.Chunk15970
import ArealUK.Chunk15971
import ArealUK.Chunk15972
import ArealUK.Chunk15973
import ArealUK.Chunk15974
import ArealUK.Chunk15975
import ArealUK.Chunk15976
import ArealUK.Chunk15977
import ArealUK.Chunk15978
import ArealUK.Chunk15979
import ArealUK.Chunk15980
import ArealUK.Chunk15981
import ArealUK.Chunk15982
import ArealUK.Chunk15983
import ArealUK.Chunk15984
import ArealUK.Chunk15985
import ArealUK.Chunk15986
import ArealUK.Chunk15987
import ArealUK.Chunk15988
import ArealUK.Chunk15989
import ArealUK.Chunk15990
import ArealUK.Chunk15991
import ArealUK.Chunk15992
import ArealUK.Chunk15993
import ArealUK.Chunk15994
import ArealUK.Chunk15995
import ArealUK.Chunk15996
import ArealUK.Chunk15997
import ArealUK.Chunk15998
import ArealUK.Chunk15999
import Areal.UCert.LeavesKGen

/-! Group 159 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_159 : leavesOK ctxLitU 169625000000 0 ((leaves.drop 31800).take 200) 171068750000 0 = true := by
  have s99 := ArealUCore.ArealUK.chunk_15999
  have s98 : leavesOK ctxLitU 171043750000 0 ((leaves.drop 31996).take 4) 171068750000 0 = true :=
    take_step (n := 2) (t := 4) (b := 31998) rfl rfl ArealUCore.ArealUK.chunk_15998 s99
  have s97 : leavesOK ctxLitU 171031250000 0 ((leaves.drop 31994).take 6) 171068750000 0 = true :=
    take_step (n := 2) (t := 6) (b := 31996) rfl rfl ArealUCore.ArealUK.chunk_15997 s98
  have s96 : leavesOK ctxLitU 171018750000 0 ((leaves.drop 31992).take 8) 171068750000 0 = true :=
    take_step (n := 2) (t := 8) (b := 31994) rfl rfl ArealUCore.ArealUK.chunk_15996 s97
  have s95 : leavesOK ctxLitU 171006250000 0 ((leaves.drop 31990).take 10) 171068750000 0 = true :=
    take_step (n := 2) (t := 10) (b := 31992) rfl rfl ArealUCore.ArealUK.chunk_15995 s96
  have s94 : leavesOK ctxLitU 170993750000 0 ((leaves.drop 31988).take 12) 171068750000 0 = true :=
    take_step (n := 2) (t := 12) (b := 31990) rfl rfl ArealUCore.ArealUK.chunk_15994 s95
  have s93 : leavesOK ctxLitU 170981250000 0 ((leaves.drop 31986).take 14) 171068750000 0 = true :=
    take_step (n := 2) (t := 14) (b := 31988) rfl rfl ArealUCore.ArealUK.chunk_15993 s94
  have s92 : leavesOK ctxLitU 170968750000 0 ((leaves.drop 31984).take 16) 171068750000 0 = true :=
    take_step (n := 2) (t := 16) (b := 31986) rfl rfl ArealUCore.ArealUK.chunk_15992 s93
  have s91 : leavesOK ctxLitU 170956250000 0 ((leaves.drop 31982).take 18) 171068750000 0 = true :=
    take_step (n := 2) (t := 18) (b := 31984) rfl rfl ArealUCore.ArealUK.chunk_15991 s92
  have s90 : leavesOK ctxLitU 170943750000 0 ((leaves.drop 31980).take 20) 171068750000 0 = true :=
    take_step (n := 2) (t := 20) (b := 31982) rfl rfl ArealUCore.ArealUK.chunk_15990 s91
  have s89 : leavesOK ctxLitU 170931250000 0 ((leaves.drop 31978).take 22) 171068750000 0 = true :=
    take_step (n := 2) (t := 22) (b := 31980) rfl rfl ArealUCore.ArealUK.chunk_15989 s90
  have s88 : leavesOK ctxLitU 170912500000 0 ((leaves.drop 31976).take 24) 171068750000 0 = true :=
    take_step (n := 2) (t := 24) (b := 31978) rfl rfl ArealUCore.ArealUK.chunk_15988 s89
  have s87 : leavesOK ctxLitU 341787500000 1 ((leaves.drop 31974).take 26) 171068750000 0 = true :=
    take_step (n := 2) (t := 26) (b := 31976) rfl rfl ArealUCore.ArealUK.chunk_15987 s88
  have s86 : leavesOK ctxLitU 341762500000 1 ((leaves.drop 31972).take 28) 171068750000 0 = true :=
    take_step (n := 2) (t := 28) (b := 31974) rfl rfl ArealUCore.ArealUK.chunk_15986 s87
  have s85 : leavesOK ctxLitU 170868750000 0 ((leaves.drop 31970).take 30) 171068750000 0 = true :=
    take_step (n := 2) (t := 30) (b := 31972) rfl rfl ArealUCore.ArealUK.chunk_15985 s86
  have s84 : leavesOK ctxLitU 170856250000 0 ((leaves.drop 31968).take 32) 171068750000 0 = true :=
    take_step (n := 2) (t := 32) (b := 31970) rfl rfl ArealUCore.ArealUK.chunk_15984 s85
  have s83 : leavesOK ctxLitU 170837500000 0 ((leaves.drop 31966).take 34) 171068750000 0 = true :=
    take_step (n := 2) (t := 34) (b := 31968) rfl rfl ArealUCore.ArealUK.chunk_15983 s84
  have s82 : leavesOK ctxLitU 170818750000 0 ((leaves.drop 31964).take 36) 171068750000 0 = true :=
    take_step (n := 2) (t := 36) (b := 31966) rfl rfl ArealUCore.ArealUK.chunk_15982 s83
  have s81 : leavesOK ctxLitU 170806250000 0 ((leaves.drop 31962).take 38) 171068750000 0 = true :=
    take_step (n := 2) (t := 38) (b := 31964) rfl rfl ArealUCore.ArealUK.chunk_15981 s82
  have s80 : leavesOK ctxLitU 170793750000 0 ((leaves.drop 31960).take 40) 171068750000 0 = true :=
    take_step (n := 2) (t := 40) (b := 31962) rfl rfl ArealUCore.ArealUK.chunk_15980 s81
  have s79 : leavesOK ctxLitU 170781250000 0 ((leaves.drop 31958).take 42) 171068750000 0 = true :=
    take_step (n := 2) (t := 42) (b := 31960) rfl rfl ArealUCore.ArealUK.chunk_15979 s80
  have s78 : leavesOK ctxLitU 170768750000 0 ((leaves.drop 31956).take 44) 171068750000 0 = true :=
    take_step (n := 2) (t := 44) (b := 31958) rfl rfl ArealUCore.ArealUK.chunk_15978 s79
  have s77 : leavesOK ctxLitU 170756250000 0 ((leaves.drop 31954).take 46) 171068750000 0 = true :=
    take_step (n := 2) (t := 46) (b := 31956) rfl rfl ArealUCore.ArealUK.chunk_15977 s78
  have s76 : leavesOK ctxLitU 170743750000 0 ((leaves.drop 31952).take 48) 171068750000 0 = true :=
    take_step (n := 2) (t := 48) (b := 31954) rfl rfl ArealUCore.ArealUK.chunk_15976 s77
  have s75 : leavesOK ctxLitU 170731250000 0 ((leaves.drop 31950).take 50) 171068750000 0 = true :=
    take_step (n := 2) (t := 50) (b := 31952) rfl rfl ArealUCore.ArealUK.chunk_15975 s76
  have s74 : leavesOK ctxLitU 170712500000 0 ((leaves.drop 31948).take 52) 171068750000 0 = true :=
    take_step (n := 2) (t := 52) (b := 31950) rfl rfl ArealUCore.ArealUK.chunk_15974 s75
  have s73 : leavesOK ctxLitU 341375000000 1 ((leaves.drop 31946).take 54) 171068750000 0 = true :=
    take_step (n := 2) (t := 54) (b := 31948) rfl rfl ArealUCore.ArealUK.chunk_15973 s74
  have s72 : leavesOK ctxLitU 170662500000 0 ((leaves.drop 31944).take 56) 171068750000 0 = true :=
    take_step (n := 2) (t := 56) (b := 31946) rfl rfl ArealUCore.ArealUK.chunk_15972 s73
  have s71 : leavesOK ctxLitU 170643750000 0 ((leaves.drop 31942).take 58) 171068750000 0 = true :=
    take_step (n := 2) (t := 58) (b := 31944) rfl rfl ArealUCore.ArealUK.chunk_15971 s72
  have s70 : leavesOK ctxLitU 170631250000 0 ((leaves.drop 31940).take 60) 171068750000 0 = true :=
    take_step (n := 2) (t := 60) (b := 31942) rfl rfl ArealUCore.ArealUK.chunk_15970 s71
  have s69 : leavesOK ctxLitU 170612500000 0 ((leaves.drop 31938).take 62) 171068750000 0 = true :=
    take_step (n := 2) (t := 62) (b := 31940) rfl rfl ArealUCore.ArealUK.chunk_15969 s70
  have s68 : leavesOK ctxLitU 170587500000 0 ((leaves.drop 31936).take 64) 171068750000 0 = true :=
    take_step (n := 2) (t := 64) (b := 31938) rfl rfl ArealUCore.ArealUK.chunk_15968 s69
  have s67 : leavesOK ctxLitU 170568750000 0 ((leaves.drop 31934).take 66) 171068750000 0 = true :=
    take_step (n := 2) (t := 66) (b := 31936) rfl rfl ArealUCore.ArealUK.chunk_15967 s68
  have s66 : leavesOK ctxLitU 170556250000 0 ((leaves.drop 31932).take 68) 171068750000 0 = true :=
    take_step (n := 2) (t := 68) (b := 31934) rfl rfl ArealUCore.ArealUK.chunk_15966 s67
  have s65 : leavesOK ctxLitU 170543750000 0 ((leaves.drop 31930).take 70) 171068750000 0 = true :=
    take_step (n := 2) (t := 70) (b := 31932) rfl rfl ArealUCore.ArealUK.chunk_15965 s66
  have s64 : leavesOK ctxLitU 170531250000 0 ((leaves.drop 31928).take 72) 171068750000 0 = true :=
    take_step (n := 2) (t := 72) (b := 31930) rfl rfl ArealUCore.ArealUK.chunk_15964 s65
  have s63 : leavesOK ctxLitU 170512500000 0 ((leaves.drop 31926).take 74) 171068750000 0 = true :=
    take_step (n := 2) (t := 74) (b := 31928) rfl rfl ArealUCore.ArealUK.chunk_15963 s64
  have s62 : leavesOK ctxLitU 170487500000 0 ((leaves.drop 31924).take 76) 171068750000 0 = true :=
    take_step (n := 2) (t := 76) (b := 31926) rfl rfl ArealUCore.ArealUK.chunk_15962 s63
  have s61 : leavesOK ctxLitU 170468750000 0 ((leaves.drop 31922).take 78) 171068750000 0 = true :=
    take_step (n := 2) (t := 78) (b := 31924) rfl rfl ArealUCore.ArealUK.chunk_15961 s62
  have s60 : leavesOK ctxLitU 170456250000 0 ((leaves.drop 31920).take 80) 171068750000 0 = true :=
    take_step (n := 2) (t := 80) (b := 31922) rfl rfl ArealUCore.ArealUK.chunk_15960 s61
  have s59 : leavesOK ctxLitU 170443750000 0 ((leaves.drop 31918).take 82) 171068750000 0 = true :=
    take_step (n := 2) (t := 82) (b := 31920) rfl rfl ArealUCore.ArealUK.chunk_15959 s60
  have s58 : leavesOK ctxLitU 170431250000 0 ((leaves.drop 31916).take 84) 171068750000 0 = true :=
    take_step (n := 2) (t := 84) (b := 31918) rfl rfl ArealUCore.ArealUK.chunk_15958 s59
  have s57 : leavesOK ctxLitU 170412500000 0 ((leaves.drop 31914).take 86) 171068750000 0 = true :=
    take_step (n := 2) (t := 86) (b := 31916) rfl rfl ArealUCore.ArealUK.chunk_15957 s58
  have s56 : leavesOK ctxLitU 170393750000 0 ((leaves.drop 31912).take 88) 171068750000 0 = true :=
    take_step (n := 2) (t := 88) (b := 31914) rfl rfl ArealUCore.ArealUK.chunk_15956 s57
  have s55 : leavesOK ctxLitU 170381250000 0 ((leaves.drop 31910).take 90) 171068750000 0 = true :=
    take_step (n := 2) (t := 90) (b := 31912) rfl rfl ArealUCore.ArealUK.chunk_15955 s56
  have s54 : leavesOK ctxLitU 170368750000 0 ((leaves.drop 31908).take 92) 171068750000 0 = true :=
    take_step (n := 2) (t := 92) (b := 31910) rfl rfl ArealUCore.ArealUK.chunk_15954 s55
  have s53 : leavesOK ctxLitU 170356250000 0 ((leaves.drop 31906).take 94) 171068750000 0 = true :=
    take_step (n := 2) (t := 94) (b := 31908) rfl rfl ArealUCore.ArealUK.chunk_15953 s54
  have s52 : leavesOK ctxLitU 170343750000 0 ((leaves.drop 31904).take 96) 171068750000 0 = true :=
    take_step (n := 2) (t := 96) (b := 31906) rfl rfl ArealUCore.ArealUK.chunk_15952 s53
  have s51 : leavesOK ctxLitU 170331250000 0 ((leaves.drop 31902).take 98) 171068750000 0 = true :=
    take_step (n := 2) (t := 98) (b := 31904) rfl rfl ArealUCore.ArealUK.chunk_15951 s52
  have s50 : leavesOK ctxLitU 170318750000 0 ((leaves.drop 31900).take 100) 171068750000 0 = true :=
    take_step (n := 2) (t := 100) (b := 31902) rfl rfl ArealUCore.ArealUK.chunk_15950 s51
  have s49 : leavesOK ctxLitU 170306250000 0 ((leaves.drop 31898).take 102) 171068750000 0 = true :=
    take_step (n := 2) (t := 102) (b := 31900) rfl rfl ArealUCore.ArealUK.chunk_15949 s50
  have s48 : leavesOK ctxLitU 170287500000 0 ((leaves.drop 31896).take 104) 171068750000 0 = true :=
    take_step (n := 2) (t := 104) (b := 31898) rfl rfl ArealUCore.ArealUK.chunk_15948 s49
  have s47 : leavesOK ctxLitU 170268750000 0 ((leaves.drop 31894).take 106) 171068750000 0 = true :=
    take_step (n := 2) (t := 106) (b := 31896) rfl rfl ArealUCore.ArealUK.chunk_15947 s48
  have s46 : leavesOK ctxLitU 170256250000 0 ((leaves.drop 31892).take 108) 171068750000 0 = true :=
    take_step (n := 2) (t := 108) (b := 31894) rfl rfl ArealUCore.ArealUK.chunk_15946 s47
  have s45 : leavesOK ctxLitU 170243750000 0 ((leaves.drop 31890).take 110) 171068750000 0 = true :=
    take_step (n := 2) (t := 110) (b := 31892) rfl rfl ArealUCore.ArealUK.chunk_15945 s46
  have s44 : leavesOK ctxLitU 170231250000 0 ((leaves.drop 31888).take 112) 171068750000 0 = true :=
    take_step (n := 2) (t := 112) (b := 31890) rfl rfl ArealUCore.ArealUK.chunk_15944 s45
  have s43 : leavesOK ctxLitU 170218750000 0 ((leaves.drop 31886).take 114) 171068750000 0 = true :=
    take_step (n := 2) (t := 114) (b := 31888) rfl rfl ArealUCore.ArealUK.chunk_15943 s44
  have s42 : leavesOK ctxLitU 170206250000 0 ((leaves.drop 31884).take 116) 171068750000 0 = true :=
    take_step (n := 2) (t := 116) (b := 31886) rfl rfl ArealUCore.ArealUK.chunk_15942 s43
  have s41 : leavesOK ctxLitU 170193750000 0 ((leaves.drop 31882).take 118) 171068750000 0 = true :=
    take_step (n := 2) (t := 118) (b := 31884) rfl rfl ArealUCore.ArealUK.chunk_15941 s42
  have s40 : leavesOK ctxLitU 170181250000 0 ((leaves.drop 31880).take 120) 171068750000 0 = true :=
    take_step (n := 2) (t := 120) (b := 31882) rfl rfl ArealUCore.ArealUK.chunk_15940 s41
  have s39 : leavesOK ctxLitU 170162500000 0 ((leaves.drop 31878).take 122) 171068750000 0 = true :=
    take_step (n := 2) (t := 122) (b := 31880) rfl rfl ArealUCore.ArealUK.chunk_15939 s40
  have s38 : leavesOK ctxLitU 170143750000 0 ((leaves.drop 31876).take 124) 171068750000 0 = true :=
    take_step (n := 2) (t := 124) (b := 31878) rfl rfl ArealUCore.ArealUK.chunk_15938 s39
  have s37 : leavesOK ctxLitU 170131250000 0 ((leaves.drop 31874).take 126) 171068750000 0 = true :=
    take_step (n := 2) (t := 126) (b := 31876) rfl rfl ArealUCore.ArealUK.chunk_15937 s38
  have s36 : leavesOK ctxLitU 340237500000 1 ((leaves.drop 31872).take 128) 171068750000 0 = true :=
    take_step (n := 2) (t := 128) (b := 31874) rfl rfl ArealUCore.ArealUK.chunk_15936 s37
  have s35 : leavesOK ctxLitU 340212500000 1 ((leaves.drop 31870).take 130) 171068750000 0 = true :=
    take_step (n := 2) (t := 130) (b := 31872) rfl rfl ArealUCore.ArealUK.chunk_15935 s36
  have s34 : leavesOK ctxLitU 170087500000 0 ((leaves.drop 31868).take 132) 171068750000 0 = true :=
    take_step (n := 2) (t := 132) (b := 31870) rfl rfl ArealUCore.ArealUK.chunk_15934 s35
  have s33 : leavesOK ctxLitU 170068750000 0 ((leaves.drop 31866).take 134) 171068750000 0 = true :=
    take_step (n := 2) (t := 134) (b := 31868) rfl rfl ArealUCore.ArealUK.chunk_15933 s34
  have s32 : leavesOK ctxLitU 170056250000 0 ((leaves.drop 31864).take 136) 171068750000 0 = true :=
    take_step (n := 2) (t := 136) (b := 31866) rfl rfl ArealUCore.ArealUK.chunk_15932 s33
  have s31 : leavesOK ctxLitU 170043750000 0 ((leaves.drop 31862).take 138) 171068750000 0 = true :=
    take_step (n := 2) (t := 138) (b := 31864) rfl rfl ArealUCore.ArealUK.chunk_15931 s32
  have s30 : leavesOK ctxLitU 170031250000 0 ((leaves.drop 31860).take 140) 171068750000 0 = true :=
    take_step (n := 2) (t := 140) (b := 31862) rfl rfl ArealUCore.ArealUK.chunk_15930 s31
  have s29 : leavesOK ctxLitU 170018750000 0 ((leaves.drop 31858).take 142) 171068750000 0 = true :=
    take_step (n := 2) (t := 142) (b := 31860) rfl rfl ArealUCore.ArealUK.chunk_15929 s30
  have s28 : leavesOK ctxLitU 170006250000 0 ((leaves.drop 31856).take 144) 171068750000 0 = true :=
    take_step (n := 2) (t := 144) (b := 31858) rfl rfl ArealUCore.ArealUK.chunk_15928 s29
  have s27 : leavesOK ctxLitU 169993750000 0 ((leaves.drop 31854).take 146) 171068750000 0 = true :=
    take_step (n := 2) (t := 146) (b := 31856) rfl rfl ArealUCore.ArealUK.chunk_15927 s28
  have s26 : leavesOK ctxLitU 169981250000 0 ((leaves.drop 31852).take 148) 171068750000 0 = true :=
    take_step (n := 2) (t := 148) (b := 31854) rfl rfl ArealUCore.ArealUK.chunk_15926 s27
  have s25 : leavesOK ctxLitU 169968750000 0 ((leaves.drop 31850).take 150) 171068750000 0 = true :=
    take_step (n := 2) (t := 150) (b := 31852) rfl rfl ArealUCore.ArealUK.chunk_15925 s26
  have s24 : leavesOK ctxLitU 169956250000 0 ((leaves.drop 31848).take 152) 171068750000 0 = true :=
    take_step (n := 2) (t := 152) (b := 31850) rfl rfl ArealUCore.ArealUK.chunk_15924 s25
  have s23 : leavesOK ctxLitU 169943750000 0 ((leaves.drop 31846).take 154) 171068750000 0 = true :=
    take_step (n := 2) (t := 154) (b := 31848) rfl rfl ArealUCore.ArealUK.chunk_15923 s24
  have s22 : leavesOK ctxLitU 169931250000 0 ((leaves.drop 31844).take 156) 171068750000 0 = true :=
    take_step (n := 2) (t := 156) (b := 31846) rfl rfl ArealUCore.ArealUK.chunk_15922 s23
  have s21 : leavesOK ctxLitU 169918750000 0 ((leaves.drop 31842).take 158) 171068750000 0 = true :=
    take_step (n := 2) (t := 158) (b := 31844) rfl rfl ArealUCore.ArealUK.chunk_15921 s22
  have s20 : leavesOK ctxLitU 169906250000 0 ((leaves.drop 31840).take 160) 171068750000 0 = true :=
    take_step (n := 2) (t := 160) (b := 31842) rfl rfl ArealUCore.ArealUK.chunk_15920 s21
  have s19 : leavesOK ctxLitU 169893750000 0 ((leaves.drop 31838).take 162) 171068750000 0 = true :=
    take_step (n := 2) (t := 162) (b := 31840) rfl rfl ArealUCore.ArealUK.chunk_15919 s20
  have s18 : leavesOK ctxLitU 169881250000 0 ((leaves.drop 31836).take 164) 171068750000 0 = true :=
    take_step (n := 2) (t := 164) (b := 31838) rfl rfl ArealUCore.ArealUK.chunk_15918 s19
  have s17 : leavesOK ctxLitU 169868750000 0 ((leaves.drop 31834).take 166) 171068750000 0 = true :=
    take_step (n := 2) (t := 166) (b := 31836) rfl rfl ArealUCore.ArealUK.chunk_15917 s18
  have s16 : leavesOK ctxLitU 169856250000 0 ((leaves.drop 31832).take 168) 171068750000 0 = true :=
    take_step (n := 2) (t := 168) (b := 31834) rfl rfl ArealUCore.ArealUK.chunk_15916 s17
  have s15 : leavesOK ctxLitU 169837500000 0 ((leaves.drop 31830).take 170) 171068750000 0 = true :=
    take_step (n := 2) (t := 170) (b := 31832) rfl rfl ArealUCore.ArealUK.chunk_15915 s16
  have s14 : leavesOK ctxLitU 169818750000 0 ((leaves.drop 31828).take 172) 171068750000 0 = true :=
    take_step (n := 2) (t := 172) (b := 31830) rfl rfl ArealUCore.ArealUK.chunk_15914 s15
  have s13 : leavesOK ctxLitU 169806250000 0 ((leaves.drop 31826).take 174) 171068750000 0 = true :=
    take_step (n := 2) (t := 174) (b := 31828) rfl rfl ArealUCore.ArealUK.chunk_15913 s14
  have s12 : leavesOK ctxLitU 169793750000 0 ((leaves.drop 31824).take 176) 171068750000 0 = true :=
    take_step (n := 2) (t := 176) (b := 31826) rfl rfl ArealUCore.ArealUK.chunk_15912 s13
  have s11 : leavesOK ctxLitU 169781250000 0 ((leaves.drop 31822).take 178) 171068750000 0 = true :=
    take_step (n := 2) (t := 178) (b := 31824) rfl rfl ArealUCore.ArealUK.chunk_15911 s12
  have s10 : leavesOK ctxLitU 169768750000 0 ((leaves.drop 31820).take 180) 171068750000 0 = true :=
    take_step (n := 2) (t := 180) (b := 31822) rfl rfl ArealUCore.ArealUK.chunk_15910 s11
  have s9 : leavesOK ctxLitU 169756250000 0 ((leaves.drop 31818).take 182) 171068750000 0 = true :=
    take_step (n := 2) (t := 182) (b := 31820) rfl rfl ArealUCore.ArealUK.chunk_15909 s10
  have s8 : leavesOK ctxLitU 169743750000 0 ((leaves.drop 31816).take 184) 171068750000 0 = true :=
    take_step (n := 2) (t := 184) (b := 31818) rfl rfl ArealUCore.ArealUK.chunk_15908 s9
  have s7 : leavesOK ctxLitU 169731250000 0 ((leaves.drop 31814).take 186) 171068750000 0 = true :=
    take_step (n := 2) (t := 186) (b := 31816) rfl rfl ArealUCore.ArealUK.chunk_15907 s8
  have s6 : leavesOK ctxLitU 169712500000 0 ((leaves.drop 31812).take 188) 171068750000 0 = true :=
    take_step (n := 2) (t := 188) (b := 31814) rfl rfl ArealUCore.ArealUK.chunk_15906 s7
  have s5 : leavesOK ctxLitU 339387500000 1 ((leaves.drop 31810).take 190) 171068750000 0 = true :=
    take_step (n := 2) (t := 190) (b := 31812) rfl rfl ArealUCore.ArealUK.chunk_15905 s6
  have s4 : leavesOK ctxLitU 169675000000 0 ((leaves.drop 31808).take 192) 171068750000 0 = true :=
    take_step (n := 2) (t := 192) (b := 31810) rfl rfl ArealUCore.ArealUK.chunk_15904 s5
  have s3 : leavesOK ctxLitU 169662500000 0 ((leaves.drop 31806).take 194) 171068750000 0 = true :=
    take_step (n := 2) (t := 194) (b := 31808) rfl rfl ArealUCore.ArealUK.chunk_15903 s4
  have s2 : leavesOK ctxLitU 169650000000 0 ((leaves.drop 31804).take 196) 171068750000 0 = true :=
    take_step (n := 2) (t := 196) (b := 31806) rfl rfl ArealUCore.ArealUK.chunk_15902 s3
  have s1 : leavesOK ctxLitU 169637500000 0 ((leaves.drop 31802).take 198) 171068750000 0 = true :=
    take_step (n := 2) (t := 198) (b := 31804) rfl rfl ArealUCore.ArealUK.chunk_15901 s2
  have s0 : leavesOK ctxLitU 169625000000 0 ((leaves.drop 31800).take 200) 171068750000 0 = true :=
    take_step (n := 2) (t := 200) (b := 31802) rfl rfl ArealUCore.ArealUK.chunk_15900 s1
  exact s0

end Areal.UCert

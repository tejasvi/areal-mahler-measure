import ArealUK.Chunk0900
import ArealUK.Chunk0901
import ArealUK.Chunk0902
import ArealUK.Chunk0903
import ArealUK.Chunk0904
import ArealUK.Chunk0905
import ArealUK.Chunk0906
import ArealUK.Chunk0907
import ArealUK.Chunk0908
import ArealUK.Chunk0909
import ArealUK.Chunk0910
import ArealUK.Chunk0911
import ArealUK.Chunk0912
import ArealUK.Chunk0913
import ArealUK.Chunk0914
import ArealUK.Chunk0915
import ArealUK.Chunk0916
import ArealUK.Chunk0917
import ArealUK.Chunk0918
import ArealUK.Chunk0919
import ArealUK.Chunk0920
import ArealUK.Chunk0921
import ArealUK.Chunk0922
import ArealUK.Chunk0923
import ArealUK.Chunk0924
import ArealUK.Chunk0925
import ArealUK.Chunk0926
import ArealUK.Chunk0927
import ArealUK.Chunk0928
import ArealUK.Chunk0929
import ArealUK.Chunk0930
import ArealUK.Chunk0931
import ArealUK.Chunk0932
import ArealUK.Chunk0933
import ArealUK.Chunk0934
import ArealUK.Chunk0935
import ArealUK.Chunk0936
import ArealUK.Chunk0937
import ArealUK.Chunk0938
import ArealUK.Chunk0939
import ArealUK.Chunk0940
import ArealUK.Chunk0941
import ArealUK.Chunk0942
import ArealUK.Chunk0943
import ArealUK.Chunk0944
import ArealUK.Chunk0945
import ArealUK.Chunk0946
import ArealUK.Chunk0947
import ArealUK.Chunk0948
import ArealUK.Chunk0949
import ArealUK.Chunk0950
import ArealUK.Chunk0951
import ArealUK.Chunk0952
import ArealUK.Chunk0953
import ArealUK.Chunk0954
import ArealUK.Chunk0955
import ArealUK.Chunk0956
import ArealUK.Chunk0957
import ArealUK.Chunk0958
import ArealUK.Chunk0959
import ArealUK.Chunk0960
import ArealUK.Chunk0961
import ArealUK.Chunk0962
import ArealUK.Chunk0963
import ArealUK.Chunk0964
import ArealUK.Chunk0965
import ArealUK.Chunk0966
import ArealUK.Chunk0967
import ArealUK.Chunk0968
import ArealUK.Chunk0969
import ArealUK.Chunk0970
import ArealUK.Chunk0971
import ArealUK.Chunk0972
import ArealUK.Chunk0973
import ArealUK.Chunk0974
import ArealUK.Chunk0975
import ArealUK.Chunk0976
import ArealUK.Chunk0977
import ArealUK.Chunk0978
import ArealUK.Chunk0979
import ArealUK.Chunk0980
import ArealUK.Chunk0981
import ArealUK.Chunk0982
import ArealUK.Chunk0983
import ArealUK.Chunk0984
import ArealUK.Chunk0985
import ArealUK.Chunk0986
import ArealUK.Chunk0987
import ArealUK.Chunk0988
import ArealUK.Chunk0989
import ArealUK.Chunk0990
import ArealUK.Chunk0991
import ArealUK.Chunk0992
import ArealUK.Chunk0993
import ArealUK.Chunk0994
import ArealUK.Chunk0995
import ArealUK.Chunk0996
import ArealUK.Chunk0997
import ArealUK.Chunk0998
import ArealUK.Chunk0999
import Areal.UCert.LeavesKGen

/-! Group 9 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_09 : leavesOK ctxLitU 148466045080990 15 ((leaves.drop 1800).take 200) 37706250000 3 = true := by
  have s99 := ArealUCore.ArealUK.chunk_0999
  have s98 : leavesOK ctxLitU 37681250000 3 ((leaves.drop 1996).take 4) 37706250000 3 = true :=
    take_step (n := 2) (t := 4) (b := 1998) rfl rfl ArealUCore.ArealUK.chunk_0998 s99
  have s97 : leavesOK ctxLitU 37668750000 3 ((leaves.drop 1994).take 6) 37706250000 3 = true :=
    take_step (n := 2) (t := 6) (b := 1996) rfl rfl ArealUCore.ArealUK.chunk_0997 s98
  have s96 : leavesOK ctxLitU 37656250000 3 ((leaves.drop 1992).take 8) 37706250000 3 = true :=
    take_step (n := 2) (t := 8) (b := 1994) rfl rfl ArealUCore.ArealUK.chunk_0996 s97
  have s95 : leavesOK ctxLitU 37643750000 3 ((leaves.drop 1990).take 10) 37706250000 3 = true :=
    take_step (n := 2) (t := 10) (b := 1992) rfl rfl ArealUCore.ArealUK.chunk_0995 s96
  have s94 : leavesOK ctxLitU 37631250000 3 ((leaves.drop 1988).take 12) 37706250000 3 = true :=
    take_step (n := 2) (t := 12) (b := 1990) rfl rfl ArealUCore.ArealUK.chunk_0994 s95
  have s93 : leavesOK ctxLitU 18806250000 2 ((leaves.drop 1986).take 14) 37706250000 3 = true :=
    take_step (n := 2) (t := 14) (b := 1988) rfl rfl ArealUCore.ArealUK.chunk_0993 s94
  have s92 : leavesOK ctxLitU 37587500000 3 ((leaves.drop 1984).take 16) 37706250000 3 = true :=
    take_step (n := 2) (t := 16) (b := 1986) rfl rfl ArealUCore.ArealUK.chunk_0992 s93
  have s91 : leavesOK ctxLitU 75137500000 4 ((leaves.drop 1982).take 18) 37706250000 3 = true :=
    take_step (n := 2) (t := 18) (b := 1984) rfl rfl ArealUCore.ArealUK.chunk_0991 s92
  have s90 : leavesOK ctxLitU 75112500000 4 ((leaves.drop 1980).take 20) 37706250000 3 = true :=
    take_step (n := 2) (t := 20) (b := 1982) rfl rfl ArealUCore.ArealUK.chunk_0990 s91
  have s89 : leavesOK ctxLitU 75087500000 4 ((leaves.drop 1978).take 22) 37706250000 3 = true :=
    take_step (n := 2) (t := 22) (b := 1980) rfl rfl ArealUCore.ArealUK.chunk_0989 s90
  have s88 : leavesOK ctxLitU 75062500000 4 ((leaves.drop 1976).take 24) 37706250000 3 = true :=
    take_step (n := 2) (t := 24) (b := 1978) rfl rfl ArealUCore.ArealUK.chunk_0988 s89
  have s87 : leavesOK ctxLitU 75037500000 4 ((leaves.drop 1974).take 26) 37706250000 3 = true :=
    take_step (n := 2) (t := 26) (b := 1976) rfl rfl ArealUCore.ArealUK.chunk_0987 s88
  have s86 : leavesOK ctxLitU 37500000000 3 ((leaves.drop 1972).take 28) 37706250000 3 = true :=
    take_step (n := 2) (t := 28) (b := 1974) rfl rfl ArealUCore.ArealUK.chunk_0986 s87
  have s85 : leavesOK ctxLitU 38377629943848 13 ((leaves.drop 1970).take 30) 37706250000 3 = true :=
    take_step (n := 2) (t := 30) (b := 1972) rfl rfl ArealUCore.ArealUK.chunk_0985 s86
  have s84 : leavesOK ctxLitU 153470504803447 15 ((leaves.drop 1968).take 32) 37706250000 3 = true :=
    take_step (n := 2) (t := 32) (b := 1970) rfl rfl ArealUCore.ArealUK.chunk_0984 s85
  have s83 : leavesOK ctxLitU 153390474859605 15 ((leaves.drop 1966).take 34) 37706250000 3 = true :=
    take_step (n := 2) (t := 34) (b := 1968) rfl rfl ArealUCore.ArealUK.chunk_0983 s84
  have s82 : leavesOK ctxLitU 306700919775368 16 ((leaves.drop 1964).take 36) 37706250000 3 = true :=
    take_step (n := 2) (t := 36) (b := 1966) rfl rfl ArealUCore.ArealUK.chunk_0982 s83
  have s81 : leavesOK ctxLitU 306620889831526 16 ((leaves.drop 1962).take 38) 37706250000 3 = true :=
    take_step (n := 2) (t := 38) (b := 1964) rfl rfl ArealUCore.ArealUK.chunk_0981 s82
  have s80 : leavesOK ctxLitU 306540859887684 16 ((leaves.drop 1960).take 40) 37706250000 3 = true :=
    take_step (n := 2) (t := 40) (b := 1962) rfl rfl ArealUCore.ArealUK.chunk_0980 s81
  have s79 : leavesOK ctxLitU 306460829943842 16 ((leaves.drop 1958).take 42) 37706250000 3 = true :=
    take_step (n := 2) (t := 42) (b := 1960) rfl rfl ArealUCore.ArealUK.chunk_0979 s80
  have s78 : leavesOK ctxLitU 306380800000000 16 ((leaves.drop 1956).take 44) 37706250000 3 = true :=
    take_step (n := 2) (t := 44) (b := 1958) rfl rfl ArealUCore.ArealUK.chunk_0978 s79
  have s77 : leavesOK ctxLitU 74775000000 4 ((leaves.drop 1954).take 46) 37706250000 3 = true :=
    take_step (n := 2) (t := 46) (b := 1956) rfl rfl ArealUCore.ArealUK.chunk_0977 s78
  have s76 : leavesOK ctxLitU 74750000000 4 ((leaves.drop 1952).take 48) 37706250000 3 = true :=
    take_step (n := 2) (t := 48) (b := 1954) rfl rfl ArealUCore.ArealUK.chunk_0976 s77
  have s75 : leavesOK ctxLitU 74725000000 4 ((leaves.drop 1950).take 50) 37706250000 3 = true :=
    take_step (n := 2) (t := 50) (b := 1952) rfl rfl ArealUCore.ArealUK.chunk_0975 s76
  have s74 : leavesOK ctxLitU 74700000000 4 ((leaves.drop 1948).take 52) 37706250000 3 = true :=
    take_step (n := 2) (t := 52) (b := 1950) rfl rfl ArealUCore.ArealUK.chunk_0974 s75
  have s73 : leavesOK ctxLitU 74675000000 4 ((leaves.drop 1946).take 54) 37706250000 3 = true :=
    take_step (n := 2) (t := 54) (b := 1948) rfl rfl ArealUCore.ArealUK.chunk_0973 s74
  have s72 : leavesOK ctxLitU 74650000000 4 ((leaves.drop 1944).take 56) 37706250000 3 = true :=
    take_step (n := 2) (t := 56) (b := 1946) rfl rfl ArealUCore.ArealUK.chunk_0972 s73
  have s71 : leavesOK ctxLitU 37300000000 3 ((leaves.drop 1942).take 58) 37706250000 3 = true :=
    take_step (n := 2) (t := 58) (b := 1944) rfl rfl ArealUCore.ArealUK.chunk_0971 s72
  have s70 : leavesOK ctxLitU 74562500000 4 ((leaves.drop 1940).take 60) 37706250000 3 = true :=
    take_step (n := 2) (t := 60) (b := 1942) rfl rfl ArealUCore.ArealUK.chunk_0970 s71
  have s69 : leavesOK ctxLitU 74537500000 4 ((leaves.drop 1938).take 62) 37706250000 3 = true :=
    take_step (n := 2) (t := 62) (b := 1940) rfl rfl ArealUCore.ArealUK.chunk_0969 s70
  have s68 : leavesOK ctxLitU 74512500000 4 ((leaves.drop 1936).take 64) 37706250000 3 = true :=
    take_step (n := 2) (t := 64) (b := 1938) rfl rfl ArealUCore.ArealUK.chunk_0968 s69
  have s67 : leavesOK ctxLitU 74487500000 4 ((leaves.drop 1934).take 66) 37706250000 3 = true :=
    take_step (n := 2) (t := 66) (b := 1936) rfl rfl ArealUCore.ArealUK.chunk_0967 s68
  have s66 : leavesOK ctxLitU 37225000000 3 ((leaves.drop 1932).take 68) 37706250000 3 = true :=
    take_step (n := 2) (t := 68) (b := 1934) rfl rfl ArealUCore.ArealUK.chunk_0966 s67
  have s65 : leavesOK ctxLitU 37200000000 3 ((leaves.drop 1930).take 70) 37706250000 3 = true :=
    take_step (n := 2) (t := 70) (b := 1932) rfl rfl ArealUCore.ArealUK.chunk_0965 s66
  have s64 : leavesOK ctxLitU 18587500000 2 ((leaves.drop 1928).take 72) 37706250000 3 = true :=
    take_step (n := 2) (t := 72) (b := 1930) rfl rfl ArealUCore.ArealUK.chunk_0964 s65
  have s63 : leavesOK ctxLitU 18575000000 2 ((leaves.drop 1926).take 74) 37706250000 3 = true :=
    take_step (n := 2) (t := 74) (b := 1928) rfl rfl ArealUCore.ArealUK.chunk_0963 s64
  have s62 : leavesOK ctxLitU 37131250000 3 ((leaves.drop 1924).take 76) 37706250000 3 = true :=
    take_step (n := 2) (t := 76) (b := 1926) rfl rfl ArealUCore.ArealUK.chunk_0962 s63
  have s61 : leavesOK ctxLitU 74250000000 4 ((leaves.drop 1922).take 78) 37706250000 3 = true :=
    take_step (n := 2) (t := 78) (b := 1924) rfl rfl ArealUCore.ArealUK.chunk_0961 s62
  have s60 : leavesOK ctxLitU 37112500000 3 ((leaves.drop 1920).take 80) 37706250000 3 = true :=
    take_step (n := 2) (t := 80) (b := 1922) rfl rfl ArealUCore.ArealUK.chunk_0960 s61
  have s59 : leavesOK ctxLitU 37100000000 3 ((leaves.drop 1918).take 82) 37706250000 3 = true :=
    take_step (n := 2) (t := 82) (b := 1920) rfl rfl ArealUCore.ArealUK.chunk_0959 s60
  have s58 : leavesOK ctxLitU 18537500000 2 ((leaves.drop 1916).take 84) 37706250000 3 = true :=
    take_step (n := 2) (t := 84) (b := 1918) rfl rfl ArealUCore.ArealUK.chunk_0958 s59
  have s57 : leavesOK ctxLitU 18966322181515 12 ((leaves.drop 1914).take 86) 37706250000 3 = true :=
    take_step (n := 2) (t := 86) (b := 1916) rfl rfl ArealUCore.ArealUK.chunk_0957 s58
  have s56 : leavesOK ctxLitU 37910322181512 13 ((leaves.drop 1912).take 88) 37706250000 3 = true :=
    take_step (n := 2) (t := 88) (b := 1914) rfl rfl ArealUCore.ArealUK.chunk_0956 s57
  have s55 : leavesOK ctxLitU 36993750000 3 ((leaves.drop 1910).take 90) 37706250000 3 = true :=
    take_step (n := 2) (t := 90) (b := 1912) rfl rfl ArealUCore.ArealUK.chunk_0955 s56
  have s54 : leavesOK ctxLitU 36981250000 3 ((leaves.drop 1908).take 92) 37706250000 3 = true :=
    take_step (n := 2) (t := 92) (b := 1910) rfl rfl ArealUCore.ArealUK.chunk_0954 s55
  have s53 : leavesOK ctxLitU 73943750000 4 ((leaves.drop 1906).take 94) 37706250000 3 = true :=
    take_step (n := 2) (t := 94) (b := 1908) rfl rfl ArealUCore.ArealUK.chunk_0953 s54
  have s52 : leavesOK ctxLitU 36962500000 3 ((leaves.drop 1904).take 96) 37706250000 3 = true :=
    take_step (n := 2) (t := 96) (b := 1906) rfl rfl ArealUCore.ArealUK.chunk_0952 s53
  have s51 : leavesOK ctxLitU 18468750000 2 ((leaves.drop 1902).take 98) 37706250000 3 = true :=
    take_step (n := 2) (t := 98) (b := 1904) rfl rfl ArealUCore.ArealUK.chunk_0951 s52
  have s50 : leavesOK ctxLitU 18456250000 2 ((leaves.drop 1900).take 100) 37706250000 3 = true :=
    take_step (n := 2) (t := 100) (b := 1902) rfl rfl ArealUCore.ArealUK.chunk_0950 s51
  have s49 : leavesOK ctxLitU 36893750000 3 ((leaves.drop 1898).take 102) 37706250000 3 = true :=
    take_step (n := 2) (t := 102) (b := 1900) rfl rfl ArealUCore.ArealUK.chunk_0949 s50
  have s48 : leavesOK ctxLitU 36881250000 3 ((leaves.drop 1896).take 104) 37706250000 3 = true :=
    take_step (n := 2) (t := 104) (b := 1898) rfl rfl ArealUCore.ArealUK.chunk_0948 s49
  have s47 : leavesOK ctxLitU 73750000000 4 ((leaves.drop 1894).take 106) 37706250000 3 = true :=
    take_step (n := 2) (t := 106) (b := 1896) rfl rfl ArealUCore.ArealUK.chunk_0947 s48
  have s46 : leavesOK ctxLitU 36862500000 3 ((leaves.drop 1892).take 108) 37706250000 3 = true :=
    take_step (n := 2) (t := 108) (b := 1894) rfl rfl ArealUCore.ArealUK.chunk_0946 s47
  have s45 : leavesOK ctxLitU 36850000000 3 ((leaves.drop 1890).take 110) 37706250000 3 = true :=
    take_step (n := 2) (t := 110) (b := 1892) rfl rfl ArealUCore.ArealUK.chunk_0945 s46
  have s44 : leavesOK ctxLitU 36837500000 3 ((leaves.drop 1888).take 112) 37706250000 3 = true :=
    take_step (n := 2) (t := 112) (b := 1890) rfl rfl ArealUCore.ArealUK.chunk_0944 s45
  have s43 : leavesOK ctxLitU 36825000000 3 ((leaves.drop 1886).take 114) 37706250000 3 = true :=
    take_step (n := 2) (t := 114) (b := 1888) rfl rfl ArealUCore.ArealUK.chunk_0943 s44
  have s42 : leavesOK ctxLitU 36812500000 3 ((leaves.drop 1884).take 116) 37706250000 3 = true :=
    take_step (n := 2) (t := 116) (b := 1886) rfl rfl ArealUCore.ArealUK.chunk_0942 s43
  have s41 : leavesOK ctxLitU 73612500000 4 ((leaves.drop 1882).take 118) 37706250000 3 = true :=
    take_step (n := 2) (t := 118) (b := 1884) rfl rfl ArealUCore.ArealUK.chunk_0941 s42
  have s40 : leavesOK ctxLitU 73600000000 4 ((leaves.drop 1880).take 120) 37706250000 3 = true :=
    take_step (n := 2) (t := 120) (b := 1882) rfl rfl ArealUCore.ArealUK.chunk_0940 s41
  have s39 : leavesOK ctxLitU 36787500000 3 ((leaves.drop 1878).take 122) 37706250000 3 = true :=
    take_step (n := 2) (t := 122) (b := 1880) rfl rfl ArealUCore.ArealUK.chunk_0939 s40
  have s38 : leavesOK ctxLitU 36775000000 3 ((leaves.drop 1876).take 124) 37706250000 3 = true :=
    take_step (n := 2) (t := 124) (b := 1878) rfl rfl ArealUCore.ArealUK.chunk_0938 s39
  have s37 : leavesOK ctxLitU 36762500000 3 ((leaves.drop 1874).take 126) 37706250000 3 = true :=
    take_step (n := 2) (t := 126) (b := 1876) rfl rfl ArealUCore.ArealUK.chunk_0937 s38
  have s36 : leavesOK ctxLitU 36750000000 3 ((leaves.drop 1872).take 128) 37706250000 3 = true :=
    take_step (n := 2) (t := 128) (b := 1874) rfl rfl ArealUCore.ArealUK.chunk_0936 s37
  have s35 : leavesOK ctxLitU 36737500000 3 ((leaves.drop 1870).take 130) 37706250000 3 = true :=
    take_step (n := 2) (t := 130) (b := 1872) rfl rfl ArealUCore.ArealUK.chunk_0935 s36
  have s34 : leavesOK ctxLitU 36725000000 3 ((leaves.drop 1868).take 132) 37706250000 3 = true :=
    take_step (n := 2) (t := 132) (b := 1870) rfl rfl ArealUCore.ArealUK.chunk_0934 s35
  have s33 : leavesOK ctxLitU 73437500000 4 ((leaves.drop 1866).take 134) 37706250000 3 = true :=
    take_step (n := 2) (t := 134) (b := 1868) rfl rfl ArealUCore.ArealUK.chunk_0933 s34
  have s32 : leavesOK ctxLitU 36706250000 3 ((leaves.drop 1864).take 136) 37706250000 3 = true :=
    take_step (n := 2) (t := 136) (b := 1866) rfl rfl ArealUCore.ArealUK.chunk_0932 s33
  have s31 : leavesOK ctxLitU 73400000000 4 ((leaves.drop 1862).take 138) 37706250000 3 = true :=
    take_step (n := 2) (t := 138) (b := 1864) rfl rfl ArealUCore.ArealUK.chunk_0931 s32
  have s30 : leavesOK ctxLitU 36687500000 3 ((leaves.drop 1860).take 140) 37706250000 3 = true :=
    take_step (n := 2) (t := 140) (b := 1862) rfl rfl ArealUCore.ArealUK.chunk_0930 s31
  have s29 : leavesOK ctxLitU 18331250000 2 ((leaves.drop 1858).take 142) 37706250000 3 = true :=
    take_step (n := 2) (t := 142) (b := 1860) rfl rfl ArealUCore.ArealUK.chunk_0929 s30
  have s28 : leavesOK ctxLitU 18318750000 2 ((leaves.drop 1856).take 144) 37706250000 3 = true :=
    take_step (n := 2) (t := 144) (b := 1858) rfl rfl ArealUCore.ArealUK.chunk_0928 s29
  have s27 : leavesOK ctxLitU 73256250000 4 ((leaves.drop 1854).take 146) 37706250000 3 = true :=
    take_step (n := 2) (t := 146) (b := 1856) rfl rfl ArealUCore.ArealUK.chunk_0927 s28
  have s26 : leavesOK ctxLitU 146500000000 5 ((leaves.drop 1852).take 148) 37706250000 3 = true :=
    take_step (n := 2) (t := 148) (b := 1854) rfl rfl ArealUCore.ArealUK.chunk_0926 s27
  have s25 : leavesOK ctxLitU 36612500000 3 ((leaves.drop 1850).take 150) 37706250000 3 = true :=
    take_step (n := 2) (t := 150) (b := 1852) rfl rfl ArealUCore.ArealUK.chunk_0925 s26
  have s24 : leavesOK ctxLitU 36600000000 3 ((leaves.drop 1848).take 152) 37706250000 3 = true :=
    take_step (n := 2) (t := 152) (b := 1850) rfl rfl ArealUCore.ArealUK.chunk_0924 s25
  have s23 : leavesOK ctxLitU 18724780389636 12 ((leaves.drop 1846).take 154) 37706250000 3 = true :=
    take_step (n := 2) (t := 154) (b := 1848) rfl rfl ArealUCore.ArealUK.chunk_0923 s24
  have s22 : leavesOK ctxLitU 36543750000 3 ((leaves.drop 1844).take 156) 37706250000 3 = true :=
    take_step (n := 2) (t := 156) (b := 1846) rfl rfl ArealUCore.ArealUK.chunk_0922 s23
  have s21 : leavesOK ctxLitU 36531250000 3 ((leaves.drop 1842).take 158) 37706250000 3 = true :=
    take_step (n := 2) (t := 158) (b := 1844) rfl rfl ArealUCore.ArealUK.chunk_0921 s22
  have s20 : leavesOK ctxLitU 146093750000 5 ((leaves.drop 1840).take 160) 37706250000 3 = true :=
    take_step (n := 2) (t := 160) (b := 1842) rfl rfl ArealUCore.ArealUK.chunk_0920 s21
  have s19 : leavesOK ctxLitU 73037500000 4 ((leaves.drop 1838).take 162) 37706250000 3 = true :=
    take_step (n := 2) (t := 162) (b := 1840) rfl rfl ArealUCore.ArealUK.chunk_0919 s20
  have s18 : leavesOK ctxLitU 18250000000 2 ((leaves.drop 1836).take 164) 37706250000 3 = true :=
    take_step (n := 2) (t := 164) (b := 1838) rfl rfl ArealUCore.ArealUK.chunk_0918 s19
  have s17 : leavesOK ctxLitU 18231250000 2 ((leaves.drop 1834).take 166) 37706250000 3 = true :=
    take_step (n := 2) (t := 166) (b := 1836) rfl rfl ArealUCore.ArealUK.chunk_0917 s18
  have s16 : leavesOK ctxLitU 72893750000 4 ((leaves.drop 1832).take 168) 37706250000 3 = true :=
    take_step (n := 2) (t := 168) (b := 1834) rfl rfl ArealUCore.ArealUK.chunk_0916 s17
  have s15 : leavesOK ctxLitU 36437500000 3 ((leaves.drop 1830).take 170) 37706250000 3 = true :=
    take_step (n := 2) (t := 170) (b := 1832) rfl rfl ArealUCore.ArealUK.chunk_0915 s16
  have s14 : leavesOK ctxLitU 72856250000 4 ((leaves.drop 1828).take 172) 37706250000 3 = true :=
    take_step (n := 2) (t := 172) (b := 1830) rfl rfl ArealUCore.ArealUK.chunk_0914 s15
  have s13 : leavesOK ctxLitU 36418750000 3 ((leaves.drop 1826).take 174) 37706250000 3 = true :=
    take_step (n := 2) (t := 174) (b := 1828) rfl rfl ArealUCore.ArealUK.chunk_0913 s14
  have s12 : leavesOK ctxLitU 36406250000 3 ((leaves.drop 1824).take 176) 37706250000 3 = true :=
    take_step (n := 2) (t := 176) (b := 1826) rfl rfl ArealUCore.ArealUK.chunk_0912 s13
  have s11 : leavesOK ctxLitU 36387500000 3 ((leaves.drop 1822).take 178) 37706250000 3 = true :=
    take_step (n := 2) (t := 178) (b := 1824) rfl rfl ArealUCore.ArealUK.chunk_0911 s12
  have s10 : leavesOK ctxLitU 72737500000 4 ((leaves.drop 1820).take 180) 37706250000 3 = true :=
    take_step (n := 2) (t := 180) (b := 1822) rfl rfl ArealUCore.ArealUK.chunk_0910 s11
  have s9 : leavesOK ctxLitU 72712500000 4 ((leaves.drop 1818).take 182) 37706250000 3 = true :=
    take_step (n := 2) (t := 182) (b := 1820) rfl rfl ArealUCore.ArealUK.chunk_0909 s10
  have s8 : leavesOK ctxLitU 72687500000 4 ((leaves.drop 1816).take 184) 37706250000 3 = true :=
    take_step (n := 2) (t := 184) (b := 1818) rfl rfl ArealUCore.ArealUK.chunk_0908 s9
  have s7 : leavesOK ctxLitU 72662500000 4 ((leaves.drop 1814).take 186) 37706250000 3 = true :=
    take_step (n := 2) (t := 186) (b := 1816) rfl rfl ArealUCore.ArealUK.chunk_0907 s8
  have s6 : leavesOK ctxLitU 72637500000 4 ((leaves.drop 1812).take 188) 37706250000 3 = true :=
    take_step (n := 2) (t := 188) (b := 1814) rfl rfl ArealUCore.ArealUK.chunk_0906 s7
  have s5 : leavesOK ctxLitU 72612500000 4 ((leaves.drop 1810).take 190) 37706250000 3 = true :=
    take_step (n := 2) (t := 190) (b := 1812) rfl rfl ArealUCore.ArealUK.chunk_0905 s6
  have s4 : leavesOK ctxLitU 297325849016198 16 ((leaves.drop 1808).take 192) 37706250000 3 = true :=
    take_step (n := 2) (t := 192) (b := 1810) rfl rfl ArealUCore.ArealUK.chunk_0904 s5
  have s3 : leavesOK ctxLitU 297238347048594 16 ((leaves.drop 1806).take 194) 37706250000 3 = true :=
    take_step (n := 2) (t := 194) (b := 1808) rfl rfl ArealUCore.ArealUK.chunk_0903 s4
  have s2 : leavesOK ctxLitU 297150845080990 16 ((leaves.drop 1804).take 196) 37706250000 3 = true :=
    take_step (n := 2) (t := 196) (b := 1806) rfl rfl ArealUCore.ArealUK.chunk_0902 s3
  have s1 : leavesOK ctxLitU 297063343113386 16 ((leaves.drop 1802).take 198) 37706250000 3 = true :=
    take_step (n := 2) (t := 198) (b := 1804) rfl rfl ArealUCore.ArealUK.chunk_0901 s2
  have s0 : leavesOK ctxLitU 148466045080990 15 ((leaves.drop 1800).take 200) 37706250000 3 = true :=
    take_step (n := 2) (t := 200) (b := 1802) rfl rfl ArealUCore.ArealUK.chunk_0900 s1
  exact s0

end Areal.UCert

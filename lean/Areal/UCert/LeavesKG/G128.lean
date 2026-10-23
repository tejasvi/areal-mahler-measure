import ArealUK.Chunk12800
import ArealUK.Chunk12801
import ArealUK.Chunk12802
import ArealUK.Chunk12803
import ArealUK.Chunk12804
import ArealUK.Chunk12805
import ArealUK.Chunk12806
import ArealUK.Chunk12807
import ArealUK.Chunk12808
import ArealUK.Chunk12809
import ArealUK.Chunk12810
import ArealUK.Chunk12811
import ArealUK.Chunk12812
import ArealUK.Chunk12813
import ArealUK.Chunk12814
import ArealUK.Chunk12815
import ArealUK.Chunk12816
import ArealUK.Chunk12817
import ArealUK.Chunk12818
import ArealUK.Chunk12819
import ArealUK.Chunk12820
import ArealUK.Chunk12821
import ArealUK.Chunk12822
import ArealUK.Chunk12823
import ArealUK.Chunk12824
import ArealUK.Chunk12825
import ArealUK.Chunk12826
import ArealUK.Chunk12827
import ArealUK.Chunk12828
import ArealUK.Chunk12829
import ArealUK.Chunk12830
import ArealUK.Chunk12831
import ArealUK.Chunk12832
import ArealUK.Chunk12833
import ArealUK.Chunk12834
import ArealUK.Chunk12835
import ArealUK.Chunk12836
import ArealUK.Chunk12837
import ArealUK.Chunk12838
import ArealUK.Chunk12839
import ArealUK.Chunk12840
import ArealUK.Chunk12841
import ArealUK.Chunk12842
import ArealUK.Chunk12843
import ArealUK.Chunk12844
import ArealUK.Chunk12845
import ArealUK.Chunk12846
import ArealUK.Chunk12847
import ArealUK.Chunk12848
import ArealUK.Chunk12849
import ArealUK.Chunk12850
import ArealUK.Chunk12851
import ArealUK.Chunk12852
import ArealUK.Chunk12853
import ArealUK.Chunk12854
import ArealUK.Chunk12855
import ArealUK.Chunk12856
import ArealUK.Chunk12857
import ArealUK.Chunk12858
import ArealUK.Chunk12859
import ArealUK.Chunk12860
import ArealUK.Chunk12861
import ArealUK.Chunk12862
import ArealUK.Chunk12863
import ArealUK.Chunk12864
import ArealUK.Chunk12865
import ArealUK.Chunk12866
import ArealUK.Chunk12867
import ArealUK.Chunk12868
import ArealUK.Chunk12869
import ArealUK.Chunk12870
import ArealUK.Chunk12871
import ArealUK.Chunk12872
import ArealUK.Chunk12873
import ArealUK.Chunk12874
import ArealUK.Chunk12875
import ArealUK.Chunk12876
import ArealUK.Chunk12877
import ArealUK.Chunk12878
import ArealUK.Chunk12879
import ArealUK.Chunk12880
import ArealUK.Chunk12881
import ArealUK.Chunk12882
import ArealUK.Chunk12883
import ArealUK.Chunk12884
import ArealUK.Chunk12885
import ArealUK.Chunk12886
import ArealUK.Chunk12887
import ArealUK.Chunk12888
import ArealUK.Chunk12889
import ArealUK.Chunk12890
import ArealUK.Chunk12891
import ArealUK.Chunk12892
import ArealUK.Chunk12893
import ArealUK.Chunk12894
import ArealUK.Chunk12895
import ArealUK.Chunk12896
import ArealUK.Chunk12897
import ArealUK.Chunk12898
import ArealUK.Chunk12899
import Areal.UCert.LeavesKGen

/-! Group 128 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_128 : leavesOK ctxLitU 259637500000 1 ((leaves.drop 25600).take 200) 523700000000 2 = true := by
  have s99 := ArealUCore.ArealUK.chunk_12899
  have s98 : leavesOK ctxLitU 523600000000 2 ((leaves.drop 25796).take 4) 523700000000 2 = true :=
    take_step (n := 2) (t := 4) (b := 25798) rfl rfl ArealUCore.ArealUK.chunk_12898 s99
  have s97 : leavesOK ctxLitU 523562500000 2 ((leaves.drop 25794).take 6) 523700000000 2 = true :=
    take_step (n := 2) (t := 6) (b := 25796) rfl rfl ArealUCore.ArealUK.chunk_12897 s98
  have s96 : leavesOK ctxLitU 523537500000 2 ((leaves.drop 25792).take 8) 523700000000 2 = true :=
    take_step (n := 2) (t := 8) (b := 25794) rfl rfl ArealUCore.ArealUK.chunk_12896 s97
  have s95 : leavesOK ctxLitU 261750000000 1 ((leaves.drop 25790).take 10) 523700000000 2 = true :=
    take_step (n := 2) (t := 10) (b := 25792) rfl rfl ArealUCore.ArealUK.chunk_12895 s96
  have s94 : leavesOK ctxLitU 261737500000 1 ((leaves.drop 25788).take 12) 523700000000 2 = true :=
    take_step (n := 2) (t := 12) (b := 25790) rfl rfl ArealUCore.ArealUK.chunk_12894 s95
  have s93 : leavesOK ctxLitU 261725000000 1 ((leaves.drop 25786).take 14) 523700000000 2 = true :=
    take_step (n := 2) (t := 14) (b := 25788) rfl rfl ArealUCore.ArealUK.chunk_12893 s94
  have s92 : leavesOK ctxLitU 130850000000 0 ((leaves.drop 25784).take 16) 523700000000 2 = true :=
    take_step (n := 2) (t := 16) (b := 25786) rfl rfl ArealUCore.ArealUK.chunk_12892 s93
  have s91 : leavesOK ctxLitU 130837500000 0 ((leaves.drop 25782).take 18) 523700000000 2 = true :=
    take_step (n := 2) (t := 18) (b := 25784) rfl rfl ArealUCore.ArealUK.chunk_12891 s92
  have s90 : leavesOK ctxLitU 261656250000 1 ((leaves.drop 25780).take 20) 523700000000 2 = true :=
    take_step (n := 2) (t := 20) (b := 25782) rfl rfl ArealUCore.ArealUK.chunk_12890 s91
  have s89 : leavesOK ctxLitU 261637500000 1 ((leaves.drop 25778).take 22) 523700000000 2 = true :=
    take_step (n := 2) (t := 22) (b := 25780) rfl rfl ArealUCore.ArealUK.chunk_12889 s90
  have s88 : leavesOK ctxLitU 261612500000 1 ((leaves.drop 25776).take 24) 523700000000 2 = true :=
    take_step (n := 2) (t := 24) (b := 25778) rfl rfl ArealUCore.ArealUK.chunk_12888 s89
  have s87 : leavesOK ctxLitU 261587500000 1 ((leaves.drop 25774).take 26) 523700000000 2 = true :=
    take_step (n := 2) (t := 26) (b := 25776) rfl rfl ArealUCore.ArealUK.chunk_12887 s88
  have s86 : leavesOK ctxLitU 261562500000 1 ((leaves.drop 25772).take 28) 523700000000 2 = true :=
    take_step (n := 2) (t := 28) (b := 25774) rfl rfl ArealUCore.ArealUK.chunk_12886 s87
  have s85 : leavesOK ctxLitU 261543750000 1 ((leaves.drop 25770).take 30) 523700000000 2 = true :=
    take_step (n := 2) (t := 30) (b := 25772) rfl rfl ArealUCore.ArealUK.chunk_12885 s86
  have s84 : leavesOK ctxLitU 261531250000 1 ((leaves.drop 25768).take 32) 523700000000 2 = true :=
    take_step (n := 2) (t := 32) (b := 25770) rfl rfl ArealUCore.ArealUK.chunk_12884 s85
  have s83 : leavesOK ctxLitU 130756250000 0 ((leaves.drop 25766).take 34) 523700000000 2 = true :=
    take_step (n := 2) (t := 34) (b := 25768) rfl rfl ArealUCore.ArealUK.chunk_12883 s84
  have s82 : leavesOK ctxLitU 261487500000 1 ((leaves.drop 25764).take 36) 523700000000 2 = true :=
    take_step (n := 2) (t := 36) (b := 25766) rfl rfl ArealUCore.ArealUK.chunk_12882 s83
  have s81 : leavesOK ctxLitU 261462500000 1 ((leaves.drop 25762).take 38) 523700000000 2 = true :=
    take_step (n := 2) (t := 38) (b := 25764) rfl rfl ArealUCore.ArealUK.chunk_12881 s82
  have s80 : leavesOK ctxLitU 522875000000 2 ((leaves.drop 25760).take 40) 523700000000 2 = true :=
    take_step (n := 2) (t := 40) (b := 25762) rfl rfl ArealUCore.ArealUK.chunk_12880 s81
  have s79 : leavesOK ctxLitU 522825000000 2 ((leaves.drop 25758).take 42) 523700000000 2 = true :=
    take_step (n := 2) (t := 42) (b := 25760) rfl rfl ArealUCore.ArealUK.chunk_12879 s80
  have s78 : leavesOK ctxLitU 522775000000 2 ((leaves.drop 25756).take 44) 523700000000 2 = true :=
    take_step (n := 2) (t := 44) (b := 25758) rfl rfl ArealUCore.ArealUK.chunk_12878 s79
  have s77 : leavesOK ctxLitU 522725000000 2 ((leaves.drop 25754).take 46) 523700000000 2 = true :=
    take_step (n := 2) (t := 46) (b := 25756) rfl rfl ArealUCore.ArealUK.chunk_12877 s78
  have s76 : leavesOK ctxLitU 261337500000 1 ((leaves.drop 25752).take 48) 523700000000 2 = true :=
    take_step (n := 2) (t := 48) (b := 25754) rfl rfl ArealUCore.ArealUK.chunk_12876 s77
  have s75 : leavesOK ctxLitU 261312500000 1 ((leaves.drop 25750).take 50) 523700000000 2 = true :=
    take_step (n := 2) (t := 50) (b := 25752) rfl rfl ArealUCore.ArealUK.chunk_12875 s76
  have s74 : leavesOK ctxLitU 130643750000 0 ((leaves.drop 25748).take 52) 523700000000 2 = true :=
    take_step (n := 2) (t := 52) (b := 25750) rfl rfl ArealUCore.ArealUK.chunk_12874 s75
  have s73 : leavesOK ctxLitU 261268750000 1 ((leaves.drop 25746).take 54) 523700000000 2 = true :=
    take_step (n := 2) (t := 54) (b := 25748) rfl rfl ArealUCore.ArealUK.chunk_12873 s74
  have s72 : leavesOK ctxLitU 522518750000 2 ((leaves.drop 25744).take 56) 523700000000 2 = true :=
    take_step (n := 2) (t := 56) (b := 25746) rfl rfl ArealUCore.ArealUK.chunk_12872 s73
  have s71 : leavesOK ctxLitU 261250000000 1 ((leaves.drop 25742).take 58) 523700000000 2 = true :=
    take_step (n := 2) (t := 58) (b := 25744) rfl rfl ArealUCore.ArealUK.chunk_12871 s72
  have s70 : leavesOK ctxLitU 261225000000 1 ((leaves.drop 25740).take 60) 523700000000 2 = true :=
    take_step (n := 2) (t := 60) (b := 25742) rfl rfl ArealUCore.ArealUK.chunk_12870 s71
  have s69 : leavesOK ctxLitU 261200000000 1 ((leaves.drop 25738).take 62) 523700000000 2 = true :=
    take_step (n := 2) (t := 62) (b := 25740) rfl rfl ArealUCore.ArealUK.chunk_12869 s70
  have s68 : leavesOK ctxLitU 261175000000 1 ((leaves.drop 25736).take 64) 523700000000 2 = true :=
    take_step (n := 2) (t := 64) (b := 25738) rfl rfl ArealUCore.ArealUK.chunk_12868 s69
  have s67 : leavesOK ctxLitU 261150000000 1 ((leaves.drop 25734).take 66) 523700000000 2 = true :=
    take_step (n := 2) (t := 66) (b := 25736) rfl rfl ArealUCore.ArealUK.chunk_12867 s68
  have s66 : leavesOK ctxLitU 130562500000 0 ((leaves.drop 25732).take 68) 523700000000 2 = true :=
    take_step (n := 2) (t := 68) (b := 25734) rfl rfl ArealUCore.ArealUK.chunk_12866 s67
  have s65 : leavesOK ctxLitU 130550000000 0 ((leaves.drop 25730).take 70) 523700000000 2 = true :=
    take_step (n := 2) (t := 70) (b := 25732) rfl rfl ArealUCore.ArealUK.chunk_12865 s66
  have s64 : leavesOK ctxLitU 130537500000 0 ((leaves.drop 25728).take 72) 523700000000 2 = true :=
    take_step (n := 2) (t := 72) (b := 25730) rfl rfl ArealUCore.ArealUK.chunk_12864 s65
  have s63 : leavesOK ctxLitU 130525000000 0 ((leaves.drop 25726).take 74) 523700000000 2 = true :=
    take_step (n := 2) (t := 74) (b := 25728) rfl rfl ArealUCore.ArealUK.chunk_12863 s64
  have s62 : leavesOK ctxLitU 261025000000 1 ((leaves.drop 25724).take 76) 523700000000 2 = true :=
    take_step (n := 2) (t := 76) (b := 25726) rfl rfl ArealUCore.ArealUK.chunk_12862 s63
  have s61 : leavesOK ctxLitU 261000000000 1 ((leaves.drop 25722).take 78) 523700000000 2 = true :=
    take_step (n := 2) (t := 78) (b := 25724) rfl rfl ArealUCore.ArealUK.chunk_12861 s62
  have s60 : leavesOK ctxLitU 521950000000 2 ((leaves.drop 25720).take 80) 523700000000 2 = true :=
    take_step (n := 2) (t := 80) (b := 25722) rfl rfl ArealUCore.ArealUK.chunk_12860 s61
  have s59 : leavesOK ctxLitU 521900000000 2 ((leaves.drop 25718).take 82) 523700000000 2 = true :=
    take_step (n := 2) (t := 82) (b := 25720) rfl rfl ArealUCore.ArealUK.chunk_12859 s60
  have s58 : leavesOK ctxLitU 521850000000 2 ((leaves.drop 25716).take 84) 523700000000 2 = true :=
    take_step (n := 2) (t := 84) (b := 25718) rfl rfl ArealUCore.ArealUK.chunk_12858 s59
  have s57 : leavesOK ctxLitU 521800000000 2 ((leaves.drop 25714).take 86) 523700000000 2 = true :=
    take_step (n := 2) (t := 86) (b := 25716) rfl rfl ArealUCore.ArealUK.chunk_12857 s58
  have s56 : leavesOK ctxLitU 521750000000 2 ((leaves.drop 25712).take 88) 523700000000 2 = true :=
    take_step (n := 2) (t := 88) (b := 25714) rfl rfl ArealUCore.ArealUK.chunk_12856 s57
  have s55 : leavesOK ctxLitU 521700000000 2 ((leaves.drop 25710).take 90) 523700000000 2 = true :=
    take_step (n := 2) (t := 90) (b := 25712) rfl rfl ArealUCore.ArealUK.chunk_12855 s56
  have s54 : leavesOK ctxLitU 521650000000 2 ((leaves.drop 25708).take 92) 523700000000 2 = true :=
    take_step (n := 2) (t := 92) (b := 25710) rfl rfl ArealUCore.ArealUK.chunk_12854 s55
  have s53 : leavesOK ctxLitU 521600000000 2 ((leaves.drop 25706).take 94) 523700000000 2 = true :=
    take_step (n := 2) (t := 94) (b := 25708) rfl rfl ArealUCore.ArealUK.chunk_12853 s54
  have s52 : leavesOK ctxLitU 260775000000 1 ((leaves.drop 25704).take 96) 523700000000 2 = true :=
    take_step (n := 2) (t := 96) (b := 25706) rfl rfl ArealUCore.ArealUK.chunk_12852 s53
  have s51 : leavesOK ctxLitU 260750000000 1 ((leaves.drop 25702).take 98) 523700000000 2 = true :=
    take_step (n := 2) (t := 98) (b := 25704) rfl rfl ArealUCore.ArealUK.chunk_12851 s52
  have s50 : leavesOK ctxLitU 260737500000 1 ((leaves.drop 25700).take 100) 523700000000 2 = true :=
    take_step (n := 2) (t := 100) (b := 25702) rfl rfl ArealUCore.ArealUK.chunk_12850 s51
  have s49 : leavesOK ctxLitU 260725000000 1 ((leaves.drop 25698).take 102) 523700000000 2 = true :=
    take_step (n := 2) (t := 102) (b := 25700) rfl rfl ArealUCore.ArealUK.chunk_12849 s50
  have s48 : leavesOK ctxLitU 130350000000 0 ((leaves.drop 25696).take 104) 523700000000 2 = true :=
    take_step (n := 2) (t := 104) (b := 25698) rfl rfl ArealUCore.ArealUK.chunk_12848 s49
  have s47 : leavesOK ctxLitU 130337500000 0 ((leaves.drop 25694).take 106) 523700000000 2 = true :=
    take_step (n := 2) (t := 106) (b := 25696) rfl rfl ArealUCore.ArealUK.chunk_12847 s48
  have s46 : leavesOK ctxLitU 260662500000 1 ((leaves.drop 25692).take 108) 523700000000 2 = true :=
    take_step (n := 2) (t := 108) (b := 25694) rfl rfl ArealUCore.ArealUK.chunk_12846 s47
  have s45 : leavesOK ctxLitU 260650000000 1 ((leaves.drop 25690).take 110) 523700000000 2 = true :=
    take_step (n := 2) (t := 110) (b := 25692) rfl rfl ArealUCore.ArealUK.chunk_12845 s46
  have s44 : leavesOK ctxLitU 521262500000 2 ((leaves.drop 25688).take 112) 523700000000 2 = true :=
    take_step (n := 2) (t := 112) (b := 25690) rfl rfl ArealUCore.ArealUK.chunk_12844 s45
  have s43 : leavesOK ctxLitU 521237500000 2 ((leaves.drop 25686).take 114) 523700000000 2 = true :=
    take_step (n := 2) (t := 114) (b := 25688) rfl rfl ArealUCore.ArealUK.chunk_12843 s44
  have s42 : leavesOK ctxLitU 260600000000 1 ((leaves.drop 25684).take 116) 523700000000 2 = true :=
    take_step (n := 2) (t := 116) (b := 25686) rfl rfl ArealUCore.ArealUK.chunk_12842 s43
  have s41 : leavesOK ctxLitU 260575000000 1 ((leaves.drop 25682).take 118) 523700000000 2 = true :=
    take_step (n := 2) (t := 118) (b := 25684) rfl rfl ArealUCore.ArealUK.chunk_12841 s42
  have s40 : leavesOK ctxLitU 260550000000 1 ((leaves.drop 25680).take 120) 523700000000 2 = true :=
    take_step (n := 2) (t := 120) (b := 25682) rfl rfl ArealUCore.ArealUK.chunk_12840 s41
  have s39 : leavesOK ctxLitU 130262500000 0 ((leaves.drop 25678).take 122) 523700000000 2 = true :=
    take_step (n := 2) (t := 122) (b := 25680) rfl rfl ArealUCore.ArealUK.chunk_12839 s40
  have s38 : leavesOK ctxLitU 130250000000 0 ((leaves.drop 25676).take 124) 523700000000 2 = true :=
    take_step (n := 2) (t := 124) (b := 25678) rfl rfl ArealUCore.ArealUK.chunk_12838 s39
  have s37 : leavesOK ctxLitU 130237500000 0 ((leaves.drop 25674).take 126) 523700000000 2 = true :=
    take_step (n := 2) (t := 126) (b := 25676) rfl rfl ArealUCore.ArealUK.chunk_12837 s38
  have s36 : leavesOK ctxLitU 260456250000 1 ((leaves.drop 25672).take 128) 523700000000 2 = true :=
    take_step (n := 2) (t := 128) (b := 25674) rfl rfl ArealUCore.ArealUK.chunk_12836 s37
  have s35 : leavesOK ctxLitU 260437500000 1 ((leaves.drop 25670).take 130) 523700000000 2 = true :=
    take_step (n := 2) (t := 130) (b := 25672) rfl rfl ArealUCore.ArealUK.chunk_12835 s36
  have s34 : leavesOK ctxLitU 260412500000 1 ((leaves.drop 25668).take 132) 523700000000 2 = true :=
    take_step (n := 2) (t := 132) (b := 25670) rfl rfl ArealUCore.ArealUK.chunk_12834 s35
  have s33 : leavesOK ctxLitU 260387500000 1 ((leaves.drop 25666).take 134) 523700000000 2 = true :=
    take_step (n := 2) (t := 134) (b := 25668) rfl rfl ArealUCore.ArealUK.chunk_12833 s34
  have s32 : leavesOK ctxLitU 260362500000 1 ((leaves.drop 25664).take 136) 523700000000 2 = true :=
    take_step (n := 2) (t := 136) (b := 25666) rfl rfl ArealUCore.ArealUK.chunk_12832 s33
  have s31 : leavesOK ctxLitU 130168750000 0 ((leaves.drop 25662).take 138) 523700000000 2 = true :=
    take_step (n := 2) (t := 138) (b := 25664) rfl rfl ArealUCore.ArealUK.chunk_12831 s32
  have s30 : leavesOK ctxLitU 130156250000 0 ((leaves.drop 25660).take 140) 523700000000 2 = true :=
    take_step (n := 2) (t := 140) (b := 25662) rfl rfl ArealUCore.ArealUK.chunk_12830 s31
  have s29 : leavesOK ctxLitU 130143750000 0 ((leaves.drop 25658).take 142) 523700000000 2 = true :=
    take_step (n := 2) (t := 142) (b := 25660) rfl rfl ArealUCore.ArealUK.chunk_12829 s30
  have s28 : leavesOK ctxLitU 260268750000 1 ((leaves.drop 25656).take 144) 523700000000 2 = true :=
    take_step (n := 2) (t := 144) (b := 25658) rfl rfl ArealUCore.ArealUK.chunk_12828 s29
  have s27 : leavesOK ctxLitU 260256250000 1 ((leaves.drop 25654).take 146) 523700000000 2 = true :=
    take_step (n := 2) (t := 146) (b := 25656) rfl rfl ArealUCore.ArealUK.chunk_12827 s28
  have s26 : leavesOK ctxLitU 260237500000 1 ((leaves.drop 25652).take 148) 523700000000 2 = true :=
    take_step (n := 2) (t := 148) (b := 25654) rfl rfl ArealUCore.ArealUK.chunk_12826 s27
  have s25 : leavesOK ctxLitU 260212500000 1 ((leaves.drop 25650).take 150) 523700000000 2 = true :=
    take_step (n := 2) (t := 150) (b := 25652) rfl rfl ArealUCore.ArealUK.chunk_12825 s26
  have s24 : leavesOK ctxLitU 260187500000 1 ((leaves.drop 25648).take 152) 523700000000 2 = true :=
    take_step (n := 2) (t := 152) (b := 25650) rfl rfl ArealUCore.ArealUK.chunk_12824 s25
  have s23 : leavesOK ctxLitU 520350000000 2 ((leaves.drop 25646).take 154) 523700000000 2 = true :=
    take_step (n := 2) (t := 154) (b := 25648) rfl rfl ArealUCore.ArealUK.chunk_12823 s24
  have s22 : leavesOK ctxLitU 260150000000 1 ((leaves.drop 25644).take 156) 523700000000 2 = true :=
    take_step (n := 2) (t := 156) (b := 25646) rfl rfl ArealUCore.ArealUK.chunk_12822 s23
  have s21 : leavesOK ctxLitU 130062500000 0 ((leaves.drop 25642).take 158) 523700000000 2 = true :=
    take_step (n := 2) (t := 158) (b := 25644) rfl rfl ArealUCore.ArealUK.chunk_12821 s22
  have s20 : leavesOK ctxLitU 130050000000 0 ((leaves.drop 25640).take 160) 523700000000 2 = true :=
    take_step (n := 2) (t := 160) (b := 25642) rfl rfl ArealUCore.ArealUK.chunk_12820 s21
  have s19 : leavesOK ctxLitU 130037500000 0 ((leaves.drop 25638).take 162) 523700000000 2 = true :=
    take_step (n := 2) (t := 162) (b := 25640) rfl rfl ArealUCore.ArealUK.chunk_12819 s20
  have s18 : leavesOK ctxLitU 260062500000 1 ((leaves.drop 25636).take 164) 523700000000 2 = true :=
    take_step (n := 2) (t := 164) (b := 25638) rfl rfl ArealUCore.ArealUK.chunk_12818 s19
  have s17 : leavesOK ctxLitU 260050000000 1 ((leaves.drop 25634).take 166) 523700000000 2 = true :=
    take_step (n := 2) (t := 166) (b := 25636) rfl rfl ArealUCore.ArealUK.chunk_12817 s18
  have s16 : leavesOK ctxLitU 260025000000 1 ((leaves.drop 25632).take 168) 523700000000 2 = true :=
    take_step (n := 2) (t := 168) (b := 25634) rfl rfl ArealUCore.ArealUK.chunk_12816 s17
  have s15 : leavesOK ctxLitU 260000000000 1 ((leaves.drop 25630).take 170) 523700000000 2 = true :=
    take_step (n := 2) (t := 170) (b := 25632) rfl rfl ArealUCore.ArealUK.chunk_12815 s16
  have s14 : leavesOK ctxLitU 259975000000 1 ((leaves.drop 25628).take 172) 523700000000 2 = true :=
    take_step (n := 2) (t := 172) (b := 25630) rfl rfl ArealUCore.ArealUK.chunk_12814 s15
  have s13 : leavesOK ctxLitU 259950000000 1 ((leaves.drop 25626).take 174) 523700000000 2 = true :=
    take_step (n := 2) (t := 174) (b := 25628) rfl rfl ArealUCore.ArealUK.chunk_12813 s14
  have s12 : leavesOK ctxLitU 129962500000 0 ((leaves.drop 25624).take 176) 523700000000 2 = true :=
    take_step (n := 2) (t := 176) (b := 25626) rfl rfl ArealUCore.ArealUK.chunk_12812 s13
  have s11 : leavesOK ctxLitU 129950000000 0 ((leaves.drop 25622).take 178) 523700000000 2 = true :=
    take_step (n := 2) (t := 178) (b := 25624) rfl rfl ArealUCore.ArealUK.chunk_12811 s12
  have s10 : leavesOK ctxLitU 129937500000 0 ((leaves.drop 25620).take 180) 523700000000 2 = true :=
    take_step (n := 2) (t := 180) (b := 25622) rfl rfl ArealUCore.ArealUK.chunk_12810 s11
  have s9 : leavesOK ctxLitU 129925000000 0 ((leaves.drop 25618).take 182) 523700000000 2 = true :=
    take_step (n := 2) (t := 182) (b := 25620) rfl rfl ArealUCore.ArealUK.chunk_12809 s10
  have s8 : leavesOK ctxLitU 259825000000 1 ((leaves.drop 25616).take 184) 523700000000 2 = true :=
    take_step (n := 2) (t := 184) (b := 25618) rfl rfl ArealUCore.ArealUK.chunk_12808 s9
  have s7 : leavesOK ctxLitU 259800000000 1 ((leaves.drop 25614).take 186) 523700000000 2 = true :=
    take_step (n := 2) (t := 186) (b := 25616) rfl rfl ArealUCore.ArealUK.chunk_12807 s8
  have s6 : leavesOK ctxLitU 259775000000 1 ((leaves.drop 25612).take 188) 523700000000 2 = true :=
    take_step (n := 2) (t := 188) (b := 25614) rfl rfl ArealUCore.ArealUK.chunk_12806 s7
  have s5 : leavesOK ctxLitU 259750000000 1 ((leaves.drop 25610).take 190) 523700000000 2 = true :=
    take_step (n := 2) (t := 190) (b := 25612) rfl rfl ArealUCore.ArealUK.chunk_12805 s6
  have s4 : leavesOK ctxLitU 129862500000 0 ((leaves.drop 25608).take 192) 523700000000 2 = true :=
    take_step (n := 2) (t := 192) (b := 25610) rfl rfl ArealUCore.ArealUK.chunk_12804 s5
  have s3 : leavesOK ctxLitU 129850000000 0 ((leaves.drop 25606).take 194) 523700000000 2 = true :=
    take_step (n := 2) (t := 194) (b := 25608) rfl rfl ArealUCore.ArealUK.chunk_12803 s4
  have s2 : leavesOK ctxLitU 129837500000 0 ((leaves.drop 25604).take 196) 523700000000 2 = true :=
    take_step (n := 2) (t := 196) (b := 25606) rfl rfl ArealUCore.ArealUK.chunk_12802 s3
  have s1 : leavesOK ctxLitU 259656250000 1 ((leaves.drop 25602).take 198) 523700000000 2 = true :=
    take_step (n := 2) (t := 198) (b := 25604) rfl rfl ArealUCore.ArealUK.chunk_12801 s2
  have s0 : leavesOK ctxLitU 259637500000 1 ((leaves.drop 25600).take 200) 523700000000 2 = true :=
    take_step (n := 2) (t := 200) (b := 25602) rfl rfl ArealUCore.ArealUK.chunk_12800 s1
  exact s0

end Areal.UCert

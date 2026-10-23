import ArealUK.Chunk10800
import ArealUK.Chunk10801
import ArealUK.Chunk10802
import ArealUK.Chunk10803
import ArealUK.Chunk10804
import ArealUK.Chunk10805
import ArealUK.Chunk10806
import ArealUK.Chunk10807
import ArealUK.Chunk10808
import ArealUK.Chunk10809
import ArealUK.Chunk10810
import ArealUK.Chunk10811
import ArealUK.Chunk10812
import ArealUK.Chunk10813
import ArealUK.Chunk10814
import ArealUK.Chunk10815
import ArealUK.Chunk10816
import ArealUK.Chunk10817
import ArealUK.Chunk10818
import ArealUK.Chunk10819
import ArealUK.Chunk10820
import ArealUK.Chunk10821
import ArealUK.Chunk10822
import ArealUK.Chunk10823
import ArealUK.Chunk10824
import ArealUK.Chunk10825
import ArealUK.Chunk10826
import ArealUK.Chunk10827
import ArealUK.Chunk10828
import ArealUK.Chunk10829
import ArealUK.Chunk10830
import ArealUK.Chunk10831
import ArealUK.Chunk10832
import ArealUK.Chunk10833
import ArealUK.Chunk10834
import ArealUK.Chunk10835
import ArealUK.Chunk10836
import ArealUK.Chunk10837
import ArealUK.Chunk10838
import ArealUK.Chunk10839
import ArealUK.Chunk10840
import ArealUK.Chunk10841
import ArealUK.Chunk10842
import ArealUK.Chunk10843
import ArealUK.Chunk10844
import ArealUK.Chunk10845
import ArealUK.Chunk10846
import ArealUK.Chunk10847
import ArealUK.Chunk10848
import ArealUK.Chunk10849
import ArealUK.Chunk10850
import ArealUK.Chunk10851
import ArealUK.Chunk10852
import ArealUK.Chunk10853
import ArealUK.Chunk10854
import ArealUK.Chunk10855
import ArealUK.Chunk10856
import ArealUK.Chunk10857
import ArealUK.Chunk10858
import ArealUK.Chunk10859
import ArealUK.Chunk10860
import ArealUK.Chunk10861
import ArealUK.Chunk10862
import ArealUK.Chunk10863
import ArealUK.Chunk10864
import ArealUK.Chunk10865
import ArealUK.Chunk10866
import ArealUK.Chunk10867
import ArealUK.Chunk10868
import ArealUK.Chunk10869
import ArealUK.Chunk10870
import ArealUK.Chunk10871
import ArealUK.Chunk10872
import ArealUK.Chunk10873
import ArealUK.Chunk10874
import ArealUK.Chunk10875
import ArealUK.Chunk10876
import ArealUK.Chunk10877
import ArealUK.Chunk10878
import ArealUK.Chunk10879
import ArealUK.Chunk10880
import ArealUK.Chunk10881
import ArealUK.Chunk10882
import ArealUK.Chunk10883
import ArealUK.Chunk10884
import ArealUK.Chunk10885
import ArealUK.Chunk10886
import ArealUK.Chunk10887
import ArealUK.Chunk10888
import ArealUK.Chunk10889
import ArealUK.Chunk10890
import ArealUK.Chunk10891
import ArealUK.Chunk10892
import ArealUK.Chunk10893
import ArealUK.Chunk10894
import ArealUK.Chunk10895
import ArealUK.Chunk10896
import ArealUK.Chunk10897
import ArealUK.Chunk10898
import ArealUK.Chunk10899
import Areal.UCert.LeavesKGen

/-! Group 108 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_108 : leavesOK ctxLitU 397150000000 2 ((leaves.drop 21600).take 200) 412979200000000 12 = true := by
  have s99 := ArealUCore.ArealUK.chunk_10899
  have s98 : leavesOK ctxLitU 100725000000 0 ((leaves.drop 21796).take 4) 412979200000000 12 = true :=
    take_step (n := 2) (t := 4) (b := 21798) rfl rfl ArealUCore.ArealUK.chunk_10898 s99
  have s97 : leavesOK ctxLitU 100675000000 0 ((leaves.drop 21794).take 6) 412979200000000 12 = true :=
    take_step (n := 2) (t := 6) (b := 21796) rfl rfl ArealUCore.ArealUK.chunk_10897 s98
  have s96 : leavesOK ctxLitU 100625000000 0 ((leaves.drop 21792).take 8) 412979200000000 12 = true :=
    take_step (n := 2) (t := 8) (b := 21794) rfl rfl ArealUCore.ArealUK.chunk_10896 s97
  have s95 : leavesOK ctxLitU 100575000000 0 ((leaves.drop 21790).take 10) 412979200000000 12 = true :=
    take_step (n := 2) (t := 10) (b := 21792) rfl rfl ArealUCore.ArealUK.chunk_10895 s96
  have s94 : leavesOK ctxLitU 100525000000 0 ((leaves.drop 21788).take 12) 412979200000000 12 = true :=
    take_step (n := 2) (t := 12) (b := 21790) rfl rfl ArealUCore.ArealUK.chunk_10894 s95
  have s93 : leavesOK ctxLitU 100475000000 0 ((leaves.drop 21786).take 14) 412979200000000 12 = true :=
    take_step (n := 2) (t := 14) (b := 21788) rfl rfl ArealUCore.ArealUK.chunk_10893 s94
  have s92 : leavesOK ctxLitU 100425000000 0 ((leaves.drop 21784).take 16) 412979200000000 12 = true :=
    take_step (n := 2) (t := 16) (b := 21786) rfl rfl ArealUCore.ArealUK.chunk_10892 s93
  have s91 : leavesOK ctxLitU 100400000000 0 ((leaves.drop 21782).take 18) 412979200000000 12 = true :=
    take_step (n := 2) (t := 18) (b := 21784) rfl rfl ArealUCore.ArealUK.chunk_10891 s92
  have s90 : leavesOK ctxLitU 100387500000 0 ((leaves.drop 21780).take 20) 412979200000000 12 = true :=
    take_step (n := 2) (t := 20) (b := 21782) rfl rfl ArealUCore.ArealUK.chunk_10890 s91
  have s89 : leavesOK ctxLitU 100375000000 0 ((leaves.drop 21778).take 22) 412979200000000 12 = true :=
    take_step (n := 2) (t := 22) (b := 21780) rfl rfl ArealUCore.ArealUK.chunk_10889 s90
  have s88 : leavesOK ctxLitU 100362500000 0 ((leaves.drop 21776).take 24) 412979200000000 12 = true :=
    take_step (n := 2) (t := 24) (b := 21778) rfl rfl ArealUCore.ArealUK.chunk_10888 s89
  have s87 : leavesOK ctxLitU 100350000000 0 ((leaves.drop 21774).take 26) 412979200000000 12 = true :=
    take_step (n := 2) (t := 26) (b := 21776) rfl rfl ArealUCore.ArealUK.chunk_10887 s88
  have s86 : leavesOK ctxLitU 200681250000 1 ((leaves.drop 21772).take 28) 412979200000000 12 = true :=
    take_step (n := 2) (t := 28) (b := 21774) rfl rfl ArealUCore.ArealUK.chunk_10886 s87
  have s85 : leavesOK ctxLitU 401343750000 2 ((leaves.drop 21770).take 30) 412979200000000 12 = true :=
    take_step (n := 2) (t := 30) (b := 21772) rfl rfl ArealUCore.ArealUK.chunk_10885 s86
  have s84 : leavesOK ctxLitU 200662500000 1 ((leaves.drop 21768).take 32) 412979200000000 12 = true :=
    take_step (n := 2) (t := 32) (b := 21770) rfl rfl ArealUCore.ArealUK.chunk_10884 s85
  have s83 : leavesOK ctxLitU 100318750000 0 ((leaves.drop 21766).take 34) 412979200000000 12 = true :=
    take_step (n := 2) (t := 34) (b := 21768) rfl rfl ArealUCore.ArealUK.chunk_10883 s84
  have s82 : leavesOK ctxLitU 100306250000 0 ((leaves.drop 21764).take 36) 412979200000000 12 = true :=
    take_step (n := 2) (t := 36) (b := 21766) rfl rfl ArealUCore.ArealUK.chunk_10882 s83
  have s81 : leavesOK ctxLitU 200587500000 1 ((leaves.drop 21762).take 38) 412979200000000 12 = true :=
    take_step (n := 2) (t := 38) (b := 21764) rfl rfl ArealUCore.ArealUK.chunk_10881 s82
  have s80 : leavesOK ctxLitU 401137500000 2 ((leaves.drop 21760).take 40) 412979200000000 12 = true :=
    take_step (n := 2) (t := 40) (b := 21762) rfl rfl ArealUCore.ArealUK.chunk_10880 s81
  have s79 : leavesOK ctxLitU 200550000000 1 ((leaves.drop 21758).take 42) 412979200000000 12 = true :=
    take_step (n := 2) (t := 42) (b := 21760) rfl rfl ArealUCore.ArealUK.chunk_10879 s80
  have s78 : leavesOK ctxLitU 401050000000 2 ((leaves.drop 21756).take 44) 412979200000000 12 = true :=
    take_step (n := 2) (t := 44) (b := 21758) rfl rfl ArealUCore.ArealUK.chunk_10878 s79
  have s77 : leavesOK ctxLitU 401000000000 2 ((leaves.drop 21754).take 46) 412979200000000 12 = true :=
    take_step (n := 2) (t := 46) (b := 21756) rfl rfl ArealUCore.ArealUK.chunk_10877 s78
  have s76 : leavesOK ctxLitU 400950000000 2 ((leaves.drop 21752).take 48) 412979200000000 12 = true :=
    take_step (n := 2) (t := 48) (b := 21754) rfl rfl ArealUCore.ArealUK.chunk_10876 s77
  have s75 : leavesOK ctxLitU 400900000000 2 ((leaves.drop 21750).take 50) 412979200000000 12 = true :=
    take_step (n := 2) (t := 50) (b := 21752) rfl rfl ArealUCore.ArealUK.chunk_10875 s76
  have s74 : leavesOK ctxLitU 400850000000 2 ((leaves.drop 21748).take 52) 412979200000000 12 = true :=
    take_step (n := 2) (t := 52) (b := 21750) rfl rfl ArealUCore.ArealUK.chunk_10874 s75
  have s73 : leavesOK ctxLitU 400800000000 2 ((leaves.drop 21746).take 54) 412979200000000 12 = true :=
    take_step (n := 2) (t := 54) (b := 21748) rfl rfl ArealUCore.ArealUK.chunk_10873 s74
  have s72 : leavesOK ctxLitU 400750000000 2 ((leaves.drop 21744).take 56) 412979200000000 12 = true :=
    take_step (n := 2) (t := 56) (b := 21746) rfl rfl ArealUCore.ArealUK.chunk_10872 s73
  have s71 : leavesOK ctxLitU 400700000000 2 ((leaves.drop 21742).take 58) 412979200000000 12 = true :=
    take_step (n := 2) (t := 58) (b := 21744) rfl rfl ArealUCore.ArealUK.chunk_10871 s72
  have s70 : leavesOK ctxLitU 400650000000 2 ((leaves.drop 21740).take 60) 412979200000000 12 = true :=
    take_step (n := 2) (t := 60) (b := 21742) rfl rfl ArealUCore.ArealUK.chunk_10870 s71
  have s69 : leavesOK ctxLitU 400600000000 2 ((leaves.drop 21738).take 62) 412979200000000 12 = true :=
    take_step (n := 2) (t := 62) (b := 21740) rfl rfl ArealUCore.ArealUK.chunk_10869 s70
  have s68 : leavesOK ctxLitU 400550000000 2 ((leaves.drop 21736).take 64) 412979200000000 12 = true :=
    take_step (n := 2) (t := 64) (b := 21738) rfl rfl ArealUCore.ArealUK.chunk_10868 s69
  have s67 : leavesOK ctxLitU 400500000000 2 ((leaves.drop 21734).take 66) 412979200000000 12 = true :=
    take_step (n := 2) (t := 66) (b := 21736) rfl rfl ArealUCore.ArealUK.chunk_10867 s68
  have s66 : leavesOK ctxLitU 400450000000 2 ((leaves.drop 21732).take 68) 412979200000000 12 = true :=
    take_step (n := 2) (t := 68) (b := 21734) rfl rfl ArealUCore.ArealUK.chunk_10866 s67
  have s65 : leavesOK ctxLitU 400400000000 2 ((leaves.drop 21730).take 70) 412979200000000 12 = true :=
    take_step (n := 2) (t := 70) (b := 21732) rfl rfl ArealUCore.ArealUK.chunk_10865 s66
  have s64 : leavesOK ctxLitU 400350000000 2 ((leaves.drop 21728).take 72) 412979200000000 12 = true :=
    take_step (n := 2) (t := 72) (b := 21730) rfl rfl ArealUCore.ArealUK.chunk_10864 s65
  have s63 : leavesOK ctxLitU 400300000000 2 ((leaves.drop 21726).take 74) 412979200000000 12 = true :=
    take_step (n := 2) (t := 74) (b := 21728) rfl rfl ArealUCore.ArealUK.chunk_10863 s64
  have s62 : leavesOK ctxLitU 400250000000 2 ((leaves.drop 21724).take 76) 412979200000000 12 = true :=
    take_step (n := 2) (t := 76) (b := 21726) rfl rfl ArealUCore.ArealUK.chunk_10862 s63
  have s61 : leavesOK ctxLitU 400200000000 2 ((leaves.drop 21722).take 78) 412979200000000 12 = true :=
    take_step (n := 2) (t := 78) (b := 21724) rfl rfl ArealUCore.ArealUK.chunk_10861 s62
  have s60 : leavesOK ctxLitU 400150000000 2 ((leaves.drop 21720).take 80) 412979200000000 12 = true :=
    take_step (n := 2) (t := 80) (b := 21722) rfl rfl ArealUCore.ArealUK.chunk_10860 s61
  have s59 : leavesOK ctxLitU 400100000000 2 ((leaves.drop 21718).take 82) 412979200000000 12 = true :=
    take_step (n := 2) (t := 82) (b := 21720) rfl rfl ArealUCore.ArealUK.chunk_10859 s60
  have s58 : leavesOK ctxLitU 400050000000 2 ((leaves.drop 21716).take 84) 412979200000000 12 = true :=
    take_step (n := 2) (t := 84) (b := 21718) rfl rfl ArealUCore.ArealUK.chunk_10858 s59
  have s57 : leavesOK ctxLitU 400000000000 2 ((leaves.drop 21714).take 86) 412979200000000 12 = true :=
    take_step (n := 2) (t := 86) (b := 21716) rfl rfl ArealUCore.ArealUK.chunk_10857 s58
  have s56 : leavesOK ctxLitU 399950000000 2 ((leaves.drop 21712).take 88) 412979200000000 12 = true :=
    take_step (n := 2) (t := 88) (b := 21714) rfl rfl ArealUCore.ArealUK.chunk_10856 s57
  have s55 : leavesOK ctxLitU 399900000000 2 ((leaves.drop 21710).take 90) 412979200000000 12 = true :=
    take_step (n := 2) (t := 90) (b := 21712) rfl rfl ArealUCore.ArealUK.chunk_10855 s56
  have s54 : leavesOK ctxLitU 399850000000 2 ((leaves.drop 21708).take 92) 412979200000000 12 = true :=
    take_step (n := 2) (t := 92) (b := 21710) rfl rfl ArealUCore.ArealUK.chunk_10854 s55
  have s53 : leavesOK ctxLitU 399800000000 2 ((leaves.drop 21706).take 94) 412979200000000 12 = true :=
    take_step (n := 2) (t := 94) (b := 21708) rfl rfl ArealUCore.ArealUK.chunk_10853 s54
  have s52 : leavesOK ctxLitU 399750000000 2 ((leaves.drop 21704).take 96) 412979200000000 12 = true :=
    take_step (n := 2) (t := 96) (b := 21706) rfl rfl ArealUCore.ArealUK.chunk_10852 s53
  have s51 : leavesOK ctxLitU 399700000000 2 ((leaves.drop 21702).take 98) 412979200000000 12 = true :=
    take_step (n := 2) (t := 98) (b := 21704) rfl rfl ArealUCore.ArealUK.chunk_10851 s52
  have s50 : leavesOK ctxLitU 399650000000 2 ((leaves.drop 21700).take 100) 412979200000000 12 = true :=
    take_step (n := 2) (t := 100) (b := 21702) rfl rfl ArealUCore.ArealUK.chunk_10850 s51
  have s49 : leavesOK ctxLitU 399600000000 2 ((leaves.drop 21698).take 102) 412979200000000 12 = true :=
    take_step (n := 2) (t := 102) (b := 21700) rfl rfl ArealUCore.ArealUK.chunk_10849 s50
  have s48 : leavesOK ctxLitU 399550000000 2 ((leaves.drop 21696).take 104) 412979200000000 12 = true :=
    take_step (n := 2) (t := 104) (b := 21698) rfl rfl ArealUCore.ArealUK.chunk_10848 s49
  have s47 : leavesOK ctxLitU 399500000000 2 ((leaves.drop 21694).take 106) 412979200000000 12 = true :=
    take_step (n := 2) (t := 106) (b := 21696) rfl rfl ArealUCore.ArealUK.chunk_10847 s48
  have s46 : leavesOK ctxLitU 399450000000 2 ((leaves.drop 21692).take 108) 412979200000000 12 = true :=
    take_step (n := 2) (t := 108) (b := 21694) rfl rfl ArealUCore.ArealUK.chunk_10846 s47
  have s45 : leavesOK ctxLitU 399400000000 2 ((leaves.drop 21690).take 110) 412979200000000 12 = true :=
    take_step (n := 2) (t := 110) (b := 21692) rfl rfl ArealUCore.ArealUK.chunk_10845 s46
  have s44 : leavesOK ctxLitU 399350000000 2 ((leaves.drop 21688).take 112) 412979200000000 12 = true :=
    take_step (n := 2) (t := 112) (b := 21690) rfl rfl ArealUCore.ArealUK.chunk_10844 s45
  have s43 : leavesOK ctxLitU 399300000000 2 ((leaves.drop 21686).take 114) 412979200000000 12 = true :=
    take_step (n := 2) (t := 114) (b := 21688) rfl rfl ArealUCore.ArealUK.chunk_10843 s44
  have s42 : leavesOK ctxLitU 399250000000 2 ((leaves.drop 21684).take 116) 412979200000000 12 = true :=
    take_step (n := 2) (t := 116) (b := 21686) rfl rfl ArealUCore.ArealUK.chunk_10842 s43
  have s41 : leavesOK ctxLitU 399200000000 2 ((leaves.drop 21682).take 118) 412979200000000 12 = true :=
    take_step (n := 2) (t := 118) (b := 21684) rfl rfl ArealUCore.ArealUK.chunk_10841 s42
  have s40 : leavesOK ctxLitU 399150000000 2 ((leaves.drop 21680).take 120) 412979200000000 12 = true :=
    take_step (n := 2) (t := 120) (b := 21682) rfl rfl ArealUCore.ArealUK.chunk_10840 s41
  have s39 : leavesOK ctxLitU 399100000000 2 ((leaves.drop 21678).take 122) 412979200000000 12 = true :=
    take_step (n := 2) (t := 122) (b := 21680) rfl rfl ArealUCore.ArealUK.chunk_10839 s40
  have s38 : leavesOK ctxLitU 399050000000 2 ((leaves.drop 21676).take 124) 412979200000000 12 = true :=
    take_step (n := 2) (t := 124) (b := 21678) rfl rfl ArealUCore.ArealUK.chunk_10838 s39
  have s37 : leavesOK ctxLitU 399000000000 2 ((leaves.drop 21674).take 126) 412979200000000 12 = true :=
    take_step (n := 2) (t := 126) (b := 21676) rfl rfl ArealUCore.ArealUK.chunk_10837 s38
  have s36 : leavesOK ctxLitU 398950000000 2 ((leaves.drop 21672).take 128) 412979200000000 12 = true :=
    take_step (n := 2) (t := 128) (b := 21674) rfl rfl ArealUCore.ArealUK.chunk_10836 s37
  have s35 : leavesOK ctxLitU 398900000000 2 ((leaves.drop 21670).take 130) 412979200000000 12 = true :=
    take_step (n := 2) (t := 130) (b := 21672) rfl rfl ArealUCore.ArealUK.chunk_10835 s36
  have s34 : leavesOK ctxLitU 398850000000 2 ((leaves.drop 21668).take 132) 412979200000000 12 = true :=
    take_step (n := 2) (t := 132) (b := 21670) rfl rfl ArealUCore.ArealUK.chunk_10834 s35
  have s33 : leavesOK ctxLitU 398800000000 2 ((leaves.drop 21666).take 134) 412979200000000 12 = true :=
    take_step (n := 2) (t := 134) (b := 21668) rfl rfl ArealUCore.ArealUK.chunk_10833 s34
  have s32 : leavesOK ctxLitU 398750000000 2 ((leaves.drop 21664).take 136) 412979200000000 12 = true :=
    take_step (n := 2) (t := 136) (b := 21666) rfl rfl ArealUCore.ArealUK.chunk_10832 s33
  have s31 : leavesOK ctxLitU 398700000000 2 ((leaves.drop 21662).take 138) 412979200000000 12 = true :=
    take_step (n := 2) (t := 138) (b := 21664) rfl rfl ArealUCore.ArealUK.chunk_10831 s32
  have s30 : leavesOK ctxLitU 398650000000 2 ((leaves.drop 21660).take 140) 412979200000000 12 = true :=
    take_step (n := 2) (t := 140) (b := 21662) rfl rfl ArealUCore.ArealUK.chunk_10830 s31
  have s29 : leavesOK ctxLitU 398600000000 2 ((leaves.drop 21658).take 142) 412979200000000 12 = true :=
    take_step (n := 2) (t := 142) (b := 21660) rfl rfl ArealUCore.ArealUK.chunk_10829 s30
  have s28 : leavesOK ctxLitU 398550000000 2 ((leaves.drop 21656).take 144) 412979200000000 12 = true :=
    take_step (n := 2) (t := 144) (b := 21658) rfl rfl ArealUCore.ArealUK.chunk_10828 s29
  have s27 : leavesOK ctxLitU 398500000000 2 ((leaves.drop 21654).take 146) 412979200000000 12 = true :=
    take_step (n := 2) (t := 146) (b := 21656) rfl rfl ArealUCore.ArealUK.chunk_10827 s28
  have s26 : leavesOK ctxLitU 398450000000 2 ((leaves.drop 21652).take 148) 412979200000000 12 = true :=
    take_step (n := 2) (t := 148) (b := 21654) rfl rfl ArealUCore.ArealUK.chunk_10826 s27
  have s25 : leavesOK ctxLitU 398400000000 2 ((leaves.drop 21650).take 150) 412979200000000 12 = true :=
    take_step (n := 2) (t := 150) (b := 21652) rfl rfl ArealUCore.ArealUK.chunk_10825 s26
  have s24 : leavesOK ctxLitU 398350000000 2 ((leaves.drop 21648).take 152) 412979200000000 12 = true :=
    take_step (n := 2) (t := 152) (b := 21650) rfl rfl ArealUCore.ArealUK.chunk_10824 s25
  have s23 : leavesOK ctxLitU 398300000000 2 ((leaves.drop 21646).take 154) 412979200000000 12 = true :=
    take_step (n := 2) (t := 154) (b := 21648) rfl rfl ArealUCore.ArealUK.chunk_10823 s24
  have s22 : leavesOK ctxLitU 398250000000 2 ((leaves.drop 21644).take 156) 412979200000000 12 = true :=
    take_step (n := 2) (t := 156) (b := 21646) rfl rfl ArealUCore.ArealUK.chunk_10822 s23
  have s21 : leavesOK ctxLitU 398200000000 2 ((leaves.drop 21642).take 158) 412979200000000 12 = true :=
    take_step (n := 2) (t := 158) (b := 21644) rfl rfl ArealUCore.ArealUK.chunk_10821 s22
  have s20 : leavesOK ctxLitU 398150000000 2 ((leaves.drop 21640).take 160) 412979200000000 12 = true :=
    take_step (n := 2) (t := 160) (b := 21642) rfl rfl ArealUCore.ArealUK.chunk_10820 s21
  have s19 : leavesOK ctxLitU 398100000000 2 ((leaves.drop 21638).take 162) 412979200000000 12 = true :=
    take_step (n := 2) (t := 162) (b := 21640) rfl rfl ArealUCore.ArealUK.chunk_10819 s20
  have s18 : leavesOK ctxLitU 398050000000 2 ((leaves.drop 21636).take 164) 412979200000000 12 = true :=
    take_step (n := 2) (t := 164) (b := 21638) rfl rfl ArealUCore.ArealUK.chunk_10818 s19
  have s17 : leavesOK ctxLitU 398000000000 2 ((leaves.drop 21634).take 166) 412979200000000 12 = true :=
    take_step (n := 2) (t := 166) (b := 21636) rfl rfl ArealUCore.ArealUK.chunk_10817 s18
  have s16 : leavesOK ctxLitU 397950000000 2 ((leaves.drop 21632).take 168) 412979200000000 12 = true :=
    take_step (n := 2) (t := 168) (b := 21634) rfl rfl ArealUCore.ArealUK.chunk_10816 s17
  have s15 : leavesOK ctxLitU 397900000000 2 ((leaves.drop 21630).take 170) 412979200000000 12 = true :=
    take_step (n := 2) (t := 170) (b := 21632) rfl rfl ArealUCore.ArealUK.chunk_10815 s16
  have s14 : leavesOK ctxLitU 397850000000 2 ((leaves.drop 21628).take 172) 412979200000000 12 = true :=
    take_step (n := 2) (t := 172) (b := 21630) rfl rfl ArealUCore.ArealUK.chunk_10814 s15
  have s13 : leavesOK ctxLitU 397800000000 2 ((leaves.drop 21626).take 174) 412979200000000 12 = true :=
    take_step (n := 2) (t := 174) (b := 21628) rfl rfl ArealUCore.ArealUK.chunk_10813 s14
  have s12 : leavesOK ctxLitU 397750000000 2 ((leaves.drop 21624).take 176) 412979200000000 12 = true :=
    take_step (n := 2) (t := 176) (b := 21626) rfl rfl ArealUCore.ArealUK.chunk_10812 s13
  have s11 : leavesOK ctxLitU 397700000000 2 ((leaves.drop 21622).take 178) 412979200000000 12 = true :=
    take_step (n := 2) (t := 178) (b := 21624) rfl rfl ArealUCore.ArealUK.chunk_10811 s12
  have s10 : leavesOK ctxLitU 397650000000 2 ((leaves.drop 21620).take 180) 412979200000000 12 = true :=
    take_step (n := 2) (t := 180) (b := 21622) rfl rfl ArealUCore.ArealUK.chunk_10810 s11
  have s9 : leavesOK ctxLitU 397600000000 2 ((leaves.drop 21618).take 182) 412979200000000 12 = true :=
    take_step (n := 2) (t := 182) (b := 21620) rfl rfl ArealUCore.ArealUK.chunk_10809 s10
  have s8 : leavesOK ctxLitU 397550000000 2 ((leaves.drop 21616).take 184) 412979200000000 12 = true :=
    take_step (n := 2) (t := 184) (b := 21618) rfl rfl ArealUCore.ArealUK.chunk_10808 s9
  have s7 : leavesOK ctxLitU 397500000000 2 ((leaves.drop 21614).take 186) 412979200000000 12 = true :=
    take_step (n := 2) (t := 186) (b := 21616) rfl rfl ArealUCore.ArealUK.chunk_10807 s8
  have s6 : leavesOK ctxLitU 397450000000 2 ((leaves.drop 21612).take 188) 412979200000000 12 = true :=
    take_step (n := 2) (t := 188) (b := 21614) rfl rfl ArealUCore.ArealUK.chunk_10806 s7
  have s5 : leavesOK ctxLitU 397400000000 2 ((leaves.drop 21610).take 190) 412979200000000 12 = true :=
    take_step (n := 2) (t := 190) (b := 21612) rfl rfl ArealUCore.ArealUK.chunk_10805 s6
  have s4 : leavesOK ctxLitU 397350000000 2 ((leaves.drop 21608).take 192) 412979200000000 12 = true :=
    take_step (n := 2) (t := 192) (b := 21610) rfl rfl ArealUCore.ArealUK.chunk_10804 s5
  have s3 : leavesOK ctxLitU 397300000000 2 ((leaves.drop 21606).take 194) 412979200000000 12 = true :=
    take_step (n := 2) (t := 194) (b := 21608) rfl rfl ArealUCore.ArealUK.chunk_10803 s4
  have s2 : leavesOK ctxLitU 397250000000 2 ((leaves.drop 21604).take 196) 412979200000000 12 = true :=
    take_step (n := 2) (t := 196) (b := 21606) rfl rfl ArealUCore.ArealUK.chunk_10802 s3
  have s1 : leavesOK ctxLitU 397200000000 2 ((leaves.drop 21602).take 198) 412979200000000 12 = true :=
    take_step (n := 2) (t := 198) (b := 21604) rfl rfl ArealUCore.ArealUK.chunk_10801 s2
  have s0 : leavesOK ctxLitU 397150000000 2 ((leaves.drop 21600).take 200) 412979200000000 12 = true :=
    take_step (n := 2) (t := 200) (b := 21602) rfl rfl ArealUCore.ArealUK.chunk_10800 s1
  exact s0

end Areal.UCert

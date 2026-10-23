import ArealUK.Chunk10700
import ArealUK.Chunk10701
import ArealUK.Chunk10702
import ArealUK.Chunk10703
import ArealUK.Chunk10704
import ArealUK.Chunk10705
import ArealUK.Chunk10706
import ArealUK.Chunk10707
import ArealUK.Chunk10708
import ArealUK.Chunk10709
import ArealUK.Chunk10710
import ArealUK.Chunk10711
import ArealUK.Chunk10712
import ArealUK.Chunk10713
import ArealUK.Chunk10714
import ArealUK.Chunk10715
import ArealUK.Chunk10716
import ArealUK.Chunk10717
import ArealUK.Chunk10718
import ArealUK.Chunk10719
import ArealUK.Chunk10720
import ArealUK.Chunk10721
import ArealUK.Chunk10722
import ArealUK.Chunk10723
import ArealUK.Chunk10724
import ArealUK.Chunk10725
import ArealUK.Chunk10726
import ArealUK.Chunk10727
import ArealUK.Chunk10728
import ArealUK.Chunk10729
import ArealUK.Chunk10730
import ArealUK.Chunk10731
import ArealUK.Chunk10732
import ArealUK.Chunk10733
import ArealUK.Chunk10734
import ArealUK.Chunk10735
import ArealUK.Chunk10736
import ArealUK.Chunk10737
import ArealUK.Chunk10738
import ArealUK.Chunk10739
import ArealUK.Chunk10740
import ArealUK.Chunk10741
import ArealUK.Chunk10742
import ArealUK.Chunk10743
import ArealUK.Chunk10744
import ArealUK.Chunk10745
import ArealUK.Chunk10746
import ArealUK.Chunk10747
import ArealUK.Chunk10748
import ArealUK.Chunk10749
import ArealUK.Chunk10750
import ArealUK.Chunk10751
import ArealUK.Chunk10752
import ArealUK.Chunk10753
import ArealUK.Chunk10754
import ArealUK.Chunk10755
import ArealUK.Chunk10756
import ArealUK.Chunk10757
import ArealUK.Chunk10758
import ArealUK.Chunk10759
import ArealUK.Chunk10760
import ArealUK.Chunk10761
import ArealUK.Chunk10762
import ArealUK.Chunk10763
import ArealUK.Chunk10764
import ArealUK.Chunk10765
import ArealUK.Chunk10766
import ArealUK.Chunk10767
import ArealUK.Chunk10768
import ArealUK.Chunk10769
import ArealUK.Chunk10770
import ArealUK.Chunk10771
import ArealUK.Chunk10772
import ArealUK.Chunk10773
import ArealUK.Chunk10774
import ArealUK.Chunk10775
import ArealUK.Chunk10776
import ArealUK.Chunk10777
import ArealUK.Chunk10778
import ArealUK.Chunk10779
import ArealUK.Chunk10780
import ArealUK.Chunk10781
import ArealUK.Chunk10782
import ArealUK.Chunk10783
import ArealUK.Chunk10784
import ArealUK.Chunk10785
import ArealUK.Chunk10786
import ArealUK.Chunk10787
import ArealUK.Chunk10788
import ArealUK.Chunk10789
import ArealUK.Chunk10790
import ArealUK.Chunk10791
import ArealUK.Chunk10792
import ArealUK.Chunk10793
import ArealUK.Chunk10794
import ArealUK.Chunk10795
import ArealUK.Chunk10796
import ArealUK.Chunk10797
import ArealUK.Chunk10798
import ArealUK.Chunk10799
import Areal.UCert.LeavesKGen

/-! Group 107 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_107 : leavesOK ctxLitU 392150000000 2 ((leaves.drop 21400).take 200) 397150000000 2 = true := by
  have s99 := ArealUCore.ArealUK.chunk_10799
  have s98 : leavesOK ctxLitU 397050000000 2 ((leaves.drop 21596).take 4) 397150000000 2 = true :=
    take_step (n := 2) (t := 4) (b := 21598) rfl rfl ArealUCore.ArealUK.chunk_10798 s99
  have s97 : leavesOK ctxLitU 397000000000 2 ((leaves.drop 21594).take 6) 397150000000 2 = true :=
    take_step (n := 2) (t := 6) (b := 21596) rfl rfl ArealUCore.ArealUK.chunk_10797 s98
  have s96 : leavesOK ctxLitU 396950000000 2 ((leaves.drop 21592).take 8) 397150000000 2 = true :=
    take_step (n := 2) (t := 8) (b := 21594) rfl rfl ArealUCore.ArealUK.chunk_10796 s97
  have s95 : leavesOK ctxLitU 396900000000 2 ((leaves.drop 21590).take 10) 397150000000 2 = true :=
    take_step (n := 2) (t := 10) (b := 21592) rfl rfl ArealUCore.ArealUK.chunk_10795 s96
  have s94 : leavesOK ctxLitU 396850000000 2 ((leaves.drop 21588).take 12) 397150000000 2 = true :=
    take_step (n := 2) (t := 12) (b := 21590) rfl rfl ArealUCore.ArealUK.chunk_10794 s95
  have s93 : leavesOK ctxLitU 396800000000 2 ((leaves.drop 21586).take 14) 397150000000 2 = true :=
    take_step (n := 2) (t := 14) (b := 21588) rfl rfl ArealUCore.ArealUK.chunk_10793 s94
  have s92 : leavesOK ctxLitU 396750000000 2 ((leaves.drop 21584).take 16) 397150000000 2 = true :=
    take_step (n := 2) (t := 16) (b := 21586) rfl rfl ArealUCore.ArealUK.chunk_10792 s93
  have s91 : leavesOK ctxLitU 396700000000 2 ((leaves.drop 21582).take 18) 397150000000 2 = true :=
    take_step (n := 2) (t := 18) (b := 21584) rfl rfl ArealUCore.ArealUK.chunk_10791 s92
  have s90 : leavesOK ctxLitU 396650000000 2 ((leaves.drop 21580).take 20) 397150000000 2 = true :=
    take_step (n := 2) (t := 20) (b := 21582) rfl rfl ArealUCore.ArealUK.chunk_10790 s91
  have s89 : leavesOK ctxLitU 396600000000 2 ((leaves.drop 21578).take 22) 397150000000 2 = true :=
    take_step (n := 2) (t := 22) (b := 21580) rfl rfl ArealUCore.ArealUK.chunk_10789 s90
  have s88 : leavesOK ctxLitU 396550000000 2 ((leaves.drop 21576).take 24) 397150000000 2 = true :=
    take_step (n := 2) (t := 24) (b := 21578) rfl rfl ArealUCore.ArealUK.chunk_10788 s89
  have s87 : leavesOK ctxLitU 396500000000 2 ((leaves.drop 21574).take 26) 397150000000 2 = true :=
    take_step (n := 2) (t := 26) (b := 21576) rfl rfl ArealUCore.ArealUK.chunk_10787 s88
  have s86 : leavesOK ctxLitU 396450000000 2 ((leaves.drop 21572).take 28) 397150000000 2 = true :=
    take_step (n := 2) (t := 28) (b := 21574) rfl rfl ArealUCore.ArealUK.chunk_10786 s87
  have s85 : leavesOK ctxLitU 396400000000 2 ((leaves.drop 21570).take 30) 397150000000 2 = true :=
    take_step (n := 2) (t := 30) (b := 21572) rfl rfl ArealUCore.ArealUK.chunk_10785 s86
  have s84 : leavesOK ctxLitU 396350000000 2 ((leaves.drop 21568).take 32) 397150000000 2 = true :=
    take_step (n := 2) (t := 32) (b := 21570) rfl rfl ArealUCore.ArealUK.chunk_10784 s85
  have s83 : leavesOK ctxLitU 396300000000 2 ((leaves.drop 21566).take 34) 397150000000 2 = true :=
    take_step (n := 2) (t := 34) (b := 21568) rfl rfl ArealUCore.ArealUK.chunk_10783 s84
  have s82 : leavesOK ctxLitU 396250000000 2 ((leaves.drop 21564).take 36) 397150000000 2 = true :=
    take_step (n := 2) (t := 36) (b := 21566) rfl rfl ArealUCore.ArealUK.chunk_10782 s83
  have s81 : leavesOK ctxLitU 396200000000 2 ((leaves.drop 21562).take 38) 397150000000 2 = true :=
    take_step (n := 2) (t := 38) (b := 21564) rfl rfl ArealUCore.ArealUK.chunk_10781 s82
  have s80 : leavesOK ctxLitU 396150000000 2 ((leaves.drop 21560).take 40) 397150000000 2 = true :=
    take_step (n := 2) (t := 40) (b := 21562) rfl rfl ArealUCore.ArealUK.chunk_10780 s81
  have s79 : leavesOK ctxLitU 396100000000 2 ((leaves.drop 21558).take 42) 397150000000 2 = true :=
    take_step (n := 2) (t := 42) (b := 21560) rfl rfl ArealUCore.ArealUK.chunk_10779 s80
  have s78 : leavesOK ctxLitU 396050000000 2 ((leaves.drop 21556).take 44) 397150000000 2 = true :=
    take_step (n := 2) (t := 44) (b := 21558) rfl rfl ArealUCore.ArealUK.chunk_10778 s79
  have s77 : leavesOK ctxLitU 396000000000 2 ((leaves.drop 21554).take 46) 397150000000 2 = true :=
    take_step (n := 2) (t := 46) (b := 21556) rfl rfl ArealUCore.ArealUK.chunk_10777 s78
  have s76 : leavesOK ctxLitU 395950000000 2 ((leaves.drop 21552).take 48) 397150000000 2 = true :=
    take_step (n := 2) (t := 48) (b := 21554) rfl rfl ArealUCore.ArealUK.chunk_10776 s77
  have s75 : leavesOK ctxLitU 395900000000 2 ((leaves.drop 21550).take 50) 397150000000 2 = true :=
    take_step (n := 2) (t := 50) (b := 21552) rfl rfl ArealUCore.ArealUK.chunk_10775 s76
  have s74 : leavesOK ctxLitU 395850000000 2 ((leaves.drop 21548).take 52) 397150000000 2 = true :=
    take_step (n := 2) (t := 52) (b := 21550) rfl rfl ArealUCore.ArealUK.chunk_10774 s75
  have s73 : leavesOK ctxLitU 395800000000 2 ((leaves.drop 21546).take 54) 397150000000 2 = true :=
    take_step (n := 2) (t := 54) (b := 21548) rfl rfl ArealUCore.ArealUK.chunk_10773 s74
  have s72 : leavesOK ctxLitU 395750000000 2 ((leaves.drop 21544).take 56) 397150000000 2 = true :=
    take_step (n := 2) (t := 56) (b := 21546) rfl rfl ArealUCore.ArealUK.chunk_10772 s73
  have s71 : leavesOK ctxLitU 395700000000 2 ((leaves.drop 21542).take 58) 397150000000 2 = true :=
    take_step (n := 2) (t := 58) (b := 21544) rfl rfl ArealUCore.ArealUK.chunk_10771 s72
  have s70 : leavesOK ctxLitU 395650000000 2 ((leaves.drop 21540).take 60) 397150000000 2 = true :=
    take_step (n := 2) (t := 60) (b := 21542) rfl rfl ArealUCore.ArealUK.chunk_10770 s71
  have s69 : leavesOK ctxLitU 395600000000 2 ((leaves.drop 21538).take 62) 397150000000 2 = true :=
    take_step (n := 2) (t := 62) (b := 21540) rfl rfl ArealUCore.ArealUK.chunk_10769 s70
  have s68 : leavesOK ctxLitU 395550000000 2 ((leaves.drop 21536).take 64) 397150000000 2 = true :=
    take_step (n := 2) (t := 64) (b := 21538) rfl rfl ArealUCore.ArealUK.chunk_10768 s69
  have s67 : leavesOK ctxLitU 395500000000 2 ((leaves.drop 21534).take 66) 397150000000 2 = true :=
    take_step (n := 2) (t := 66) (b := 21536) rfl rfl ArealUCore.ArealUK.chunk_10767 s68
  have s66 : leavesOK ctxLitU 395450000000 2 ((leaves.drop 21532).take 68) 397150000000 2 = true :=
    take_step (n := 2) (t := 68) (b := 21534) rfl rfl ArealUCore.ArealUK.chunk_10766 s67
  have s65 : leavesOK ctxLitU 395400000000 2 ((leaves.drop 21530).take 70) 397150000000 2 = true :=
    take_step (n := 2) (t := 70) (b := 21532) rfl rfl ArealUCore.ArealUK.chunk_10765 s66
  have s64 : leavesOK ctxLitU 395350000000 2 ((leaves.drop 21528).take 72) 397150000000 2 = true :=
    take_step (n := 2) (t := 72) (b := 21530) rfl rfl ArealUCore.ArealUK.chunk_10764 s65
  have s63 : leavesOK ctxLitU 395300000000 2 ((leaves.drop 21526).take 74) 397150000000 2 = true :=
    take_step (n := 2) (t := 74) (b := 21528) rfl rfl ArealUCore.ArealUK.chunk_10763 s64
  have s62 : leavesOK ctxLitU 395250000000 2 ((leaves.drop 21524).take 76) 397150000000 2 = true :=
    take_step (n := 2) (t := 76) (b := 21526) rfl rfl ArealUCore.ArealUK.chunk_10762 s63
  have s61 : leavesOK ctxLitU 395200000000 2 ((leaves.drop 21522).take 78) 397150000000 2 = true :=
    take_step (n := 2) (t := 78) (b := 21524) rfl rfl ArealUCore.ArealUK.chunk_10761 s62
  have s60 : leavesOK ctxLitU 395150000000 2 ((leaves.drop 21520).take 80) 397150000000 2 = true :=
    take_step (n := 2) (t := 80) (b := 21522) rfl rfl ArealUCore.ArealUK.chunk_10760 s61
  have s59 : leavesOK ctxLitU 395100000000 2 ((leaves.drop 21518).take 82) 397150000000 2 = true :=
    take_step (n := 2) (t := 82) (b := 21520) rfl rfl ArealUCore.ArealUK.chunk_10759 s60
  have s58 : leavesOK ctxLitU 395050000000 2 ((leaves.drop 21516).take 84) 397150000000 2 = true :=
    take_step (n := 2) (t := 84) (b := 21518) rfl rfl ArealUCore.ArealUK.chunk_10758 s59
  have s57 : leavesOK ctxLitU 395000000000 2 ((leaves.drop 21514).take 86) 397150000000 2 = true :=
    take_step (n := 2) (t := 86) (b := 21516) rfl rfl ArealUCore.ArealUK.chunk_10757 s58
  have s56 : leavesOK ctxLitU 394950000000 2 ((leaves.drop 21512).take 88) 397150000000 2 = true :=
    take_step (n := 2) (t := 88) (b := 21514) rfl rfl ArealUCore.ArealUK.chunk_10756 s57
  have s55 : leavesOK ctxLitU 394900000000 2 ((leaves.drop 21510).take 90) 397150000000 2 = true :=
    take_step (n := 2) (t := 90) (b := 21512) rfl rfl ArealUCore.ArealUK.chunk_10755 s56
  have s54 : leavesOK ctxLitU 394850000000 2 ((leaves.drop 21508).take 92) 397150000000 2 = true :=
    take_step (n := 2) (t := 92) (b := 21510) rfl rfl ArealUCore.ArealUK.chunk_10754 s55
  have s53 : leavesOK ctxLitU 394800000000 2 ((leaves.drop 21506).take 94) 397150000000 2 = true :=
    take_step (n := 2) (t := 94) (b := 21508) rfl rfl ArealUCore.ArealUK.chunk_10753 s54
  have s52 : leavesOK ctxLitU 394750000000 2 ((leaves.drop 21504).take 96) 397150000000 2 = true :=
    take_step (n := 2) (t := 96) (b := 21506) rfl rfl ArealUCore.ArealUK.chunk_10752 s53
  have s51 : leavesOK ctxLitU 394700000000 2 ((leaves.drop 21502).take 98) 397150000000 2 = true :=
    take_step (n := 2) (t := 98) (b := 21504) rfl rfl ArealUCore.ArealUK.chunk_10751 s52
  have s50 : leavesOK ctxLitU 394650000000 2 ((leaves.drop 21500).take 100) 397150000000 2 = true :=
    take_step (n := 2) (t := 100) (b := 21502) rfl rfl ArealUCore.ArealUK.chunk_10750 s51
  have s49 : leavesOK ctxLitU 394600000000 2 ((leaves.drop 21498).take 102) 397150000000 2 = true :=
    take_step (n := 2) (t := 102) (b := 21500) rfl rfl ArealUCore.ArealUK.chunk_10749 s50
  have s48 : leavesOK ctxLitU 394550000000 2 ((leaves.drop 21496).take 104) 397150000000 2 = true :=
    take_step (n := 2) (t := 104) (b := 21498) rfl rfl ArealUCore.ArealUK.chunk_10748 s49
  have s47 : leavesOK ctxLitU 394500000000 2 ((leaves.drop 21494).take 106) 397150000000 2 = true :=
    take_step (n := 2) (t := 106) (b := 21496) rfl rfl ArealUCore.ArealUK.chunk_10747 s48
  have s46 : leavesOK ctxLitU 394450000000 2 ((leaves.drop 21492).take 108) 397150000000 2 = true :=
    take_step (n := 2) (t := 108) (b := 21494) rfl rfl ArealUCore.ArealUK.chunk_10746 s47
  have s45 : leavesOK ctxLitU 394400000000 2 ((leaves.drop 21490).take 110) 397150000000 2 = true :=
    take_step (n := 2) (t := 110) (b := 21492) rfl rfl ArealUCore.ArealUK.chunk_10745 s46
  have s44 : leavesOK ctxLitU 394350000000 2 ((leaves.drop 21488).take 112) 397150000000 2 = true :=
    take_step (n := 2) (t := 112) (b := 21490) rfl rfl ArealUCore.ArealUK.chunk_10744 s45
  have s43 : leavesOK ctxLitU 394300000000 2 ((leaves.drop 21486).take 114) 397150000000 2 = true :=
    take_step (n := 2) (t := 114) (b := 21488) rfl rfl ArealUCore.ArealUK.chunk_10743 s44
  have s42 : leavesOK ctxLitU 394250000000 2 ((leaves.drop 21484).take 116) 397150000000 2 = true :=
    take_step (n := 2) (t := 116) (b := 21486) rfl rfl ArealUCore.ArealUK.chunk_10742 s43
  have s41 : leavesOK ctxLitU 394200000000 2 ((leaves.drop 21482).take 118) 397150000000 2 = true :=
    take_step (n := 2) (t := 118) (b := 21484) rfl rfl ArealUCore.ArealUK.chunk_10741 s42
  have s40 : leavesOK ctxLitU 394150000000 2 ((leaves.drop 21480).take 120) 397150000000 2 = true :=
    take_step (n := 2) (t := 120) (b := 21482) rfl rfl ArealUCore.ArealUK.chunk_10740 s41
  have s39 : leavesOK ctxLitU 394100000000 2 ((leaves.drop 21478).take 122) 397150000000 2 = true :=
    take_step (n := 2) (t := 122) (b := 21480) rfl rfl ArealUCore.ArealUK.chunk_10739 s40
  have s38 : leavesOK ctxLitU 394050000000 2 ((leaves.drop 21476).take 124) 397150000000 2 = true :=
    take_step (n := 2) (t := 124) (b := 21478) rfl rfl ArealUCore.ArealUK.chunk_10738 s39
  have s37 : leavesOK ctxLitU 394000000000 2 ((leaves.drop 21474).take 126) 397150000000 2 = true :=
    take_step (n := 2) (t := 126) (b := 21476) rfl rfl ArealUCore.ArealUK.chunk_10737 s38
  have s36 : leavesOK ctxLitU 393950000000 2 ((leaves.drop 21472).take 128) 397150000000 2 = true :=
    take_step (n := 2) (t := 128) (b := 21474) rfl rfl ArealUCore.ArealUK.chunk_10736 s37
  have s35 : leavesOK ctxLitU 393900000000 2 ((leaves.drop 21470).take 130) 397150000000 2 = true :=
    take_step (n := 2) (t := 130) (b := 21472) rfl rfl ArealUCore.ArealUK.chunk_10735 s36
  have s34 : leavesOK ctxLitU 393850000000 2 ((leaves.drop 21468).take 132) 397150000000 2 = true :=
    take_step (n := 2) (t := 132) (b := 21470) rfl rfl ArealUCore.ArealUK.chunk_10734 s35
  have s33 : leavesOK ctxLitU 393800000000 2 ((leaves.drop 21466).take 134) 397150000000 2 = true :=
    take_step (n := 2) (t := 134) (b := 21468) rfl rfl ArealUCore.ArealUK.chunk_10733 s34
  have s32 : leavesOK ctxLitU 393750000000 2 ((leaves.drop 21464).take 136) 397150000000 2 = true :=
    take_step (n := 2) (t := 136) (b := 21466) rfl rfl ArealUCore.ArealUK.chunk_10732 s33
  have s31 : leavesOK ctxLitU 393700000000 2 ((leaves.drop 21462).take 138) 397150000000 2 = true :=
    take_step (n := 2) (t := 138) (b := 21464) rfl rfl ArealUCore.ArealUK.chunk_10731 s32
  have s30 : leavesOK ctxLitU 393650000000 2 ((leaves.drop 21460).take 140) 397150000000 2 = true :=
    take_step (n := 2) (t := 140) (b := 21462) rfl rfl ArealUCore.ArealUK.chunk_10730 s31
  have s29 : leavesOK ctxLitU 393600000000 2 ((leaves.drop 21458).take 142) 397150000000 2 = true :=
    take_step (n := 2) (t := 142) (b := 21460) rfl rfl ArealUCore.ArealUK.chunk_10729 s30
  have s28 : leavesOK ctxLitU 393550000000 2 ((leaves.drop 21456).take 144) 397150000000 2 = true :=
    take_step (n := 2) (t := 144) (b := 21458) rfl rfl ArealUCore.ArealUK.chunk_10728 s29
  have s27 : leavesOK ctxLitU 393500000000 2 ((leaves.drop 21454).take 146) 397150000000 2 = true :=
    take_step (n := 2) (t := 146) (b := 21456) rfl rfl ArealUCore.ArealUK.chunk_10727 s28
  have s26 : leavesOK ctxLitU 393450000000 2 ((leaves.drop 21452).take 148) 397150000000 2 = true :=
    take_step (n := 2) (t := 148) (b := 21454) rfl rfl ArealUCore.ArealUK.chunk_10726 s27
  have s25 : leavesOK ctxLitU 393400000000 2 ((leaves.drop 21450).take 150) 397150000000 2 = true :=
    take_step (n := 2) (t := 150) (b := 21452) rfl rfl ArealUCore.ArealUK.chunk_10725 s26
  have s24 : leavesOK ctxLitU 393350000000 2 ((leaves.drop 21448).take 152) 397150000000 2 = true :=
    take_step (n := 2) (t := 152) (b := 21450) rfl rfl ArealUCore.ArealUK.chunk_10724 s25
  have s23 : leavesOK ctxLitU 393300000000 2 ((leaves.drop 21446).take 154) 397150000000 2 = true :=
    take_step (n := 2) (t := 154) (b := 21448) rfl rfl ArealUCore.ArealUK.chunk_10723 s24
  have s22 : leavesOK ctxLitU 393250000000 2 ((leaves.drop 21444).take 156) 397150000000 2 = true :=
    take_step (n := 2) (t := 156) (b := 21446) rfl rfl ArealUCore.ArealUK.chunk_10722 s23
  have s21 : leavesOK ctxLitU 393200000000 2 ((leaves.drop 21442).take 158) 397150000000 2 = true :=
    take_step (n := 2) (t := 158) (b := 21444) rfl rfl ArealUCore.ArealUK.chunk_10721 s22
  have s20 : leavesOK ctxLitU 393150000000 2 ((leaves.drop 21440).take 160) 397150000000 2 = true :=
    take_step (n := 2) (t := 160) (b := 21442) rfl rfl ArealUCore.ArealUK.chunk_10720 s21
  have s19 : leavesOK ctxLitU 393100000000 2 ((leaves.drop 21438).take 162) 397150000000 2 = true :=
    take_step (n := 2) (t := 162) (b := 21440) rfl rfl ArealUCore.ArealUK.chunk_10719 s20
  have s18 : leavesOK ctxLitU 393050000000 2 ((leaves.drop 21436).take 164) 397150000000 2 = true :=
    take_step (n := 2) (t := 164) (b := 21438) rfl rfl ArealUCore.ArealUK.chunk_10718 s19
  have s17 : leavesOK ctxLitU 393000000000 2 ((leaves.drop 21434).take 166) 397150000000 2 = true :=
    take_step (n := 2) (t := 166) (b := 21436) rfl rfl ArealUCore.ArealUK.chunk_10717 s18
  have s16 : leavesOK ctxLitU 392950000000 2 ((leaves.drop 21432).take 168) 397150000000 2 = true :=
    take_step (n := 2) (t := 168) (b := 21434) rfl rfl ArealUCore.ArealUK.chunk_10716 s17
  have s15 : leavesOK ctxLitU 392900000000 2 ((leaves.drop 21430).take 170) 397150000000 2 = true :=
    take_step (n := 2) (t := 170) (b := 21432) rfl rfl ArealUCore.ArealUK.chunk_10715 s16
  have s14 : leavesOK ctxLitU 392850000000 2 ((leaves.drop 21428).take 172) 397150000000 2 = true :=
    take_step (n := 2) (t := 172) (b := 21430) rfl rfl ArealUCore.ArealUK.chunk_10714 s15
  have s13 : leavesOK ctxLitU 392800000000 2 ((leaves.drop 21426).take 174) 397150000000 2 = true :=
    take_step (n := 2) (t := 174) (b := 21428) rfl rfl ArealUCore.ArealUK.chunk_10713 s14
  have s12 : leavesOK ctxLitU 392750000000 2 ((leaves.drop 21424).take 176) 397150000000 2 = true :=
    take_step (n := 2) (t := 176) (b := 21426) rfl rfl ArealUCore.ArealUK.chunk_10712 s13
  have s11 : leavesOK ctxLitU 392700000000 2 ((leaves.drop 21422).take 178) 397150000000 2 = true :=
    take_step (n := 2) (t := 178) (b := 21424) rfl rfl ArealUCore.ArealUK.chunk_10711 s12
  have s10 : leavesOK ctxLitU 392650000000 2 ((leaves.drop 21420).take 180) 397150000000 2 = true :=
    take_step (n := 2) (t := 180) (b := 21422) rfl rfl ArealUCore.ArealUK.chunk_10710 s11
  have s9 : leavesOK ctxLitU 392600000000 2 ((leaves.drop 21418).take 182) 397150000000 2 = true :=
    take_step (n := 2) (t := 182) (b := 21420) rfl rfl ArealUCore.ArealUK.chunk_10709 s10
  have s8 : leavesOK ctxLitU 392550000000 2 ((leaves.drop 21416).take 184) 397150000000 2 = true :=
    take_step (n := 2) (t := 184) (b := 21418) rfl rfl ArealUCore.ArealUK.chunk_10708 s9
  have s7 : leavesOK ctxLitU 392500000000 2 ((leaves.drop 21414).take 186) 397150000000 2 = true :=
    take_step (n := 2) (t := 186) (b := 21416) rfl rfl ArealUCore.ArealUK.chunk_10707 s8
  have s6 : leavesOK ctxLitU 392450000000 2 ((leaves.drop 21412).take 188) 397150000000 2 = true :=
    take_step (n := 2) (t := 188) (b := 21414) rfl rfl ArealUCore.ArealUK.chunk_10706 s7
  have s5 : leavesOK ctxLitU 392400000000 2 ((leaves.drop 21410).take 190) 397150000000 2 = true :=
    take_step (n := 2) (t := 190) (b := 21412) rfl rfl ArealUCore.ArealUK.chunk_10705 s6
  have s4 : leavesOK ctxLitU 392350000000 2 ((leaves.drop 21408).take 192) 397150000000 2 = true :=
    take_step (n := 2) (t := 192) (b := 21410) rfl rfl ArealUCore.ArealUK.chunk_10704 s5
  have s3 : leavesOK ctxLitU 392300000000 2 ((leaves.drop 21406).take 194) 397150000000 2 = true :=
    take_step (n := 2) (t := 194) (b := 21408) rfl rfl ArealUCore.ArealUK.chunk_10703 s4
  have s2 : leavesOK ctxLitU 392250000000 2 ((leaves.drop 21404).take 196) 397150000000 2 = true :=
    take_step (n := 2) (t := 196) (b := 21406) rfl rfl ArealUCore.ArealUK.chunk_10702 s3
  have s1 : leavesOK ctxLitU 392200000000 2 ((leaves.drop 21402).take 198) 397150000000 2 = true :=
    take_step (n := 2) (t := 198) (b := 21404) rfl rfl ArealUCore.ArealUK.chunk_10701 s2
  have s0 : leavesOK ctxLitU 392150000000 2 ((leaves.drop 21400).take 200) 397150000000 2 = true :=
    take_step (n := 2) (t := 200) (b := 21402) rfl rfl ArealUCore.ArealUK.chunk_10700 s1
  exact s0

end Areal.UCert

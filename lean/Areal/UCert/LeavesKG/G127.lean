import ArealUK.Chunk12700
import ArealUK.Chunk12701
import ArealUK.Chunk12702
import ArealUK.Chunk12703
import ArealUK.Chunk12704
import ArealUK.Chunk12705
import ArealUK.Chunk12706
import ArealUK.Chunk12707
import ArealUK.Chunk12708
import ArealUK.Chunk12709
import ArealUK.Chunk12710
import ArealUK.Chunk12711
import ArealUK.Chunk12712
import ArealUK.Chunk12713
import ArealUK.Chunk12714
import ArealUK.Chunk12715
import ArealUK.Chunk12716
import ArealUK.Chunk12717
import ArealUK.Chunk12718
import ArealUK.Chunk12719
import ArealUK.Chunk12720
import ArealUK.Chunk12721
import ArealUK.Chunk12722
import ArealUK.Chunk12723
import ArealUK.Chunk12724
import ArealUK.Chunk12725
import ArealUK.Chunk12726
import ArealUK.Chunk12727
import ArealUK.Chunk12728
import ArealUK.Chunk12729
import ArealUK.Chunk12730
import ArealUK.Chunk12731
import ArealUK.Chunk12732
import ArealUK.Chunk12733
import ArealUK.Chunk12734
import ArealUK.Chunk12735
import ArealUK.Chunk12736
import ArealUK.Chunk12737
import ArealUK.Chunk12738
import ArealUK.Chunk12739
import ArealUK.Chunk12740
import ArealUK.Chunk12741
import ArealUK.Chunk12742
import ArealUK.Chunk12743
import ArealUK.Chunk12744
import ArealUK.Chunk12745
import ArealUK.Chunk12746
import ArealUK.Chunk12747
import ArealUK.Chunk12748
import ArealUK.Chunk12749
import ArealUK.Chunk12750
import ArealUK.Chunk12751
import ArealUK.Chunk12752
import ArealUK.Chunk12753
import ArealUK.Chunk12754
import ArealUK.Chunk12755
import ArealUK.Chunk12756
import ArealUK.Chunk12757
import ArealUK.Chunk12758
import ArealUK.Chunk12759
import ArealUK.Chunk12760
import ArealUK.Chunk12761
import ArealUK.Chunk12762
import ArealUK.Chunk12763
import ArealUK.Chunk12764
import ArealUK.Chunk12765
import ArealUK.Chunk12766
import ArealUK.Chunk12767
import ArealUK.Chunk12768
import ArealUK.Chunk12769
import ArealUK.Chunk12770
import ArealUK.Chunk12771
import ArealUK.Chunk12772
import ArealUK.Chunk12773
import ArealUK.Chunk12774
import ArealUK.Chunk12775
import ArealUK.Chunk12776
import ArealUK.Chunk12777
import ArealUK.Chunk12778
import ArealUK.Chunk12779
import ArealUK.Chunk12780
import ArealUK.Chunk12781
import ArealUK.Chunk12782
import ArealUK.Chunk12783
import ArealUK.Chunk12784
import ArealUK.Chunk12785
import ArealUK.Chunk12786
import ArealUK.Chunk12787
import ArealUK.Chunk12788
import ArealUK.Chunk12789
import ArealUK.Chunk12790
import ArealUK.Chunk12791
import ArealUK.Chunk12792
import ArealUK.Chunk12793
import ArealUK.Chunk12794
import ArealUK.Chunk12795
import ArealUK.Chunk12796
import ArealUK.Chunk12797
import ArealUK.Chunk12798
import ArealUK.Chunk12799
import Areal.UCert.LeavesKGen

/-! Group 127 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_127 : leavesOK ctxLitU 514600000000 2 ((leaves.drop 25400).take 200) 259637500000 1 = true := by
  have s99 := ArealUCore.ArealUK.chunk_12799
  have s98 : leavesOK ctxLitU 259587500000 1 ((leaves.drop 25596).take 4) 259637500000 1 = true :=
    take_step (n := 2) (t := 4) (b := 25598) rfl rfl ArealUCore.ArealUK.chunk_12798 s99
  have s97 : leavesOK ctxLitU 259562500000 1 ((leaves.drop 25594).take 6) 259637500000 1 = true :=
    take_step (n := 2) (t := 6) (b := 25596) rfl rfl ArealUCore.ArealUK.chunk_12797 s98
  have s96 : leavesOK ctxLitU 259543750000 1 ((leaves.drop 25592).take 8) 259637500000 1 = true :=
    take_step (n := 2) (t := 8) (b := 25594) rfl rfl ArealUCore.ArealUK.chunk_12796 s97
  have s95 : leavesOK ctxLitU 259531250000 1 ((leaves.drop 25590).take 10) 259637500000 1 = true :=
    take_step (n := 2) (t := 10) (b := 25592) rfl rfl ArealUCore.ArealUK.chunk_12795 s96
  have s94 : leavesOK ctxLitU 129756250000 0 ((leaves.drop 25588).take 12) 259637500000 1 = true :=
    take_step (n := 2) (t := 12) (b := 25590) rfl rfl ArealUCore.ArealUK.chunk_12794 s95
  have s93 : leavesOK ctxLitU 129743750000 0 ((leaves.drop 25586).take 14) 259637500000 1 = true :=
    take_step (n := 2) (t := 14) (b := 25588) rfl rfl ArealUCore.ArealUK.chunk_12793 s94
  have s92 : leavesOK ctxLitU 259468750000 1 ((leaves.drop 25584).take 16) 259637500000 1 = true :=
    take_step (n := 2) (t := 16) (b := 25586) rfl rfl ArealUCore.ArealUK.chunk_12792 s93
  have s91 : leavesOK ctxLitU 259456250000 1 ((leaves.drop 25582).take 18) 259637500000 1 = true :=
    take_step (n := 2) (t := 18) (b := 25584) rfl rfl ArealUCore.ArealUK.chunk_12791 s92
  have s90 : leavesOK ctxLitU 259437500000 1 ((leaves.drop 25580).take 20) 259637500000 1 = true :=
    take_step (n := 2) (t := 20) (b := 25582) rfl rfl ArealUCore.ArealUK.chunk_12790 s91
  have s89 : leavesOK ctxLitU 518850000000 2 ((leaves.drop 25578).take 22) 259637500000 1 = true :=
    take_step (n := 2) (t := 22) (b := 25580) rfl rfl ArealUCore.ArealUK.chunk_12789 s90
  have s88 : leavesOK ctxLitU 518825000000 2 ((leaves.drop 25576).take 24) 259637500000 1 = true :=
    take_step (n := 2) (t := 24) (b := 25578) rfl rfl ArealUCore.ArealUK.chunk_12788 s89
  have s87 : leavesOK ctxLitU 518775000000 2 ((leaves.drop 25574).take 26) 259637500000 1 = true :=
    take_step (n := 2) (t := 26) (b := 25576) rfl rfl ArealUCore.ArealUK.chunk_12787 s88
  have s86 : leavesOK ctxLitU 518725000000 2 ((leaves.drop 25572).take 28) 259637500000 1 = true :=
    take_step (n := 2) (t := 28) (b := 25574) rfl rfl ArealUCore.ArealUK.chunk_12786 s87
  have s85 : leavesOK ctxLitU 518675000000 2 ((leaves.drop 25570).take 30) 259637500000 1 = true :=
    take_step (n := 2) (t := 30) (b := 25572) rfl rfl ArealUCore.ArealUK.chunk_12785 s86
  have s84 : leavesOK ctxLitU 518625000000 2 ((leaves.drop 25568).take 32) 259637500000 1 = true :=
    take_step (n := 2) (t := 32) (b := 25570) rfl rfl ArealUCore.ArealUK.chunk_12784 s85
  have s83 : leavesOK ctxLitU 518575000000 2 ((leaves.drop 25566).take 34) 259637500000 1 = true :=
    take_step (n := 2) (t := 34) (b := 25568) rfl rfl ArealUCore.ArealUK.chunk_12783 s84
  have s82 : leavesOK ctxLitU 518525000000 2 ((leaves.drop 25564).take 36) 259637500000 1 = true :=
    take_step (n := 2) (t := 36) (b := 25566) rfl rfl ArealUCore.ArealUK.chunk_12782 s83
  have s81 : leavesOK ctxLitU 518475000000 2 ((leaves.drop 25562).take 38) 259637500000 1 = true :=
    take_step (n := 2) (t := 38) (b := 25564) rfl rfl ArealUCore.ArealUK.chunk_12781 s82
  have s80 : leavesOK ctxLitU 518425000000 2 ((leaves.drop 25560).take 40) 259637500000 1 = true :=
    take_step (n := 2) (t := 40) (b := 25562) rfl rfl ArealUCore.ArealUK.chunk_12780 s81
  have s79 : leavesOK ctxLitU 518375000000 2 ((leaves.drop 25558).take 42) 259637500000 1 = true :=
    take_step (n := 2) (t := 42) (b := 25560) rfl rfl ArealUCore.ArealUK.chunk_12779 s80
  have s78 : leavesOK ctxLitU 518325000000 2 ((leaves.drop 25556).take 44) 259637500000 1 = true :=
    take_step (n := 2) (t := 44) (b := 25558) rfl rfl ArealUCore.ArealUK.chunk_12778 s79
  have s77 : leavesOK ctxLitU 518275000000 2 ((leaves.drop 25554).take 46) 259637500000 1 = true :=
    take_step (n := 2) (t := 46) (b := 25556) rfl rfl ArealUCore.ArealUK.chunk_12777 s78
  have s76 : leavesOK ctxLitU 518225000000 2 ((leaves.drop 25552).take 48) 259637500000 1 = true :=
    take_step (n := 2) (t := 48) (b := 25554) rfl rfl ArealUCore.ArealUK.chunk_12776 s77
  have s75 : leavesOK ctxLitU 518175000000 2 ((leaves.drop 25550).take 50) 259637500000 1 = true :=
    take_step (n := 2) (t := 50) (b := 25552) rfl rfl ArealUCore.ArealUK.chunk_12775 s76
  have s74 : leavesOK ctxLitU 518125000000 2 ((leaves.drop 25548).take 52) 259637500000 1 = true :=
    take_step (n := 2) (t := 52) (b := 25550) rfl rfl ArealUCore.ArealUK.chunk_12774 s75
  have s73 : leavesOK ctxLitU 518075000000 2 ((leaves.drop 25546).take 54) 259637500000 1 = true :=
    take_step (n := 2) (t := 54) (b := 25548) rfl rfl ArealUCore.ArealUK.chunk_12773 s74
  have s72 : leavesOK ctxLitU 518025000000 2 ((leaves.drop 25544).take 56) 259637500000 1 = true :=
    take_step (n := 2) (t := 56) (b := 25546) rfl rfl ArealUCore.ArealUK.chunk_12772 s73
  have s71 : leavesOK ctxLitU 517975000000 2 ((leaves.drop 25542).take 58) 259637500000 1 = true :=
    take_step (n := 2) (t := 58) (b := 25544) rfl rfl ArealUCore.ArealUK.chunk_12771 s72
  have s70 : leavesOK ctxLitU 517925000000 2 ((leaves.drop 25540).take 60) 259637500000 1 = true :=
    take_step (n := 2) (t := 60) (b := 25542) rfl rfl ArealUCore.ArealUK.chunk_12770 s71
  have s69 : leavesOK ctxLitU 517875000000 2 ((leaves.drop 25538).take 62) 259637500000 1 = true :=
    take_step (n := 2) (t := 62) (b := 25540) rfl rfl ArealUCore.ArealUK.chunk_12769 s70
  have s68 : leavesOK ctxLitU 517825000000 2 ((leaves.drop 25536).take 64) 259637500000 1 = true :=
    take_step (n := 2) (t := 64) (b := 25538) rfl rfl ArealUCore.ArealUK.chunk_12768 s69
  have s67 : leavesOK ctxLitU 517775000000 2 ((leaves.drop 25534).take 66) 259637500000 1 = true :=
    take_step (n := 2) (t := 66) (b := 25536) rfl rfl ArealUCore.ArealUK.chunk_12767 s68
  have s66 : leavesOK ctxLitU 517725000000 2 ((leaves.drop 25532).take 68) 259637500000 1 = true :=
    take_step (n := 2) (t := 68) (b := 25534) rfl rfl ArealUCore.ArealUK.chunk_12766 s67
  have s65 : leavesOK ctxLitU 517675000000 2 ((leaves.drop 25530).take 70) 259637500000 1 = true :=
    take_step (n := 2) (t := 70) (b := 25532) rfl rfl ArealUCore.ArealUK.chunk_12765 s66
  have s64 : leavesOK ctxLitU 517625000000 2 ((leaves.drop 25528).take 72) 259637500000 1 = true :=
    take_step (n := 2) (t := 72) (b := 25530) rfl rfl ArealUCore.ArealUK.chunk_12764 s65
  have s63 : leavesOK ctxLitU 258787500000 1 ((leaves.drop 25526).take 74) 259637500000 1 = true :=
    take_step (n := 2) (t := 74) (b := 25528) rfl rfl ArealUCore.ArealUK.chunk_12763 s64
  have s62 : leavesOK ctxLitU 258762500000 1 ((leaves.drop 25524).take 76) 259637500000 1 = true :=
    take_step (n := 2) (t := 76) (b := 25526) rfl rfl ArealUCore.ArealUK.chunk_12762 s63
  have s61 : leavesOK ctxLitU 258743750000 1 ((leaves.drop 25522).take 78) 259637500000 1 = true :=
    take_step (n := 2) (t := 78) (b := 25524) rfl rfl ArealUCore.ArealUK.chunk_12761 s62
  have s60 : leavesOK ctxLitU 517475000000 2 ((leaves.drop 25520).take 80) 259637500000 1 = true :=
    take_step (n := 2) (t := 80) (b := 25522) rfl rfl ArealUCore.ArealUK.chunk_12760 s61
  have s59 : leavesOK ctxLitU 258725000000 1 ((leaves.drop 25518).take 82) 259637500000 1 = true :=
    take_step (n := 2) (t := 82) (b := 25520) rfl rfl ArealUCore.ArealUK.chunk_12759 s60
  have s58 : leavesOK ctxLitU 129350000000 0 ((leaves.drop 25516).take 84) 259637500000 1 = true :=
    take_step (n := 2) (t := 84) (b := 25518) rfl rfl ArealUCore.ArealUK.chunk_12758 s59
  have s57 : leavesOK ctxLitU 129337500000 0 ((leaves.drop 25514).take 86) 259637500000 1 = true :=
    take_step (n := 2) (t := 86) (b := 25516) rfl rfl ArealUCore.ArealUK.chunk_12757 s58
  have s56 : leavesOK ctxLitU 129325000000 0 ((leaves.drop 25512).take 88) 259637500000 1 = true :=
    take_step (n := 2) (t := 88) (b := 25514) rfl rfl ArealUCore.ArealUK.chunk_12756 s57
  have s55 : leavesOK ctxLitU 258625000000 1 ((leaves.drop 25510).take 90) 259637500000 1 = true :=
    take_step (n := 2) (t := 90) (b := 25512) rfl rfl ArealUCore.ArealUK.chunk_12755 s56
  have s54 : leavesOK ctxLitU 258600000000 1 ((leaves.drop 25508).take 92) 259637500000 1 = true :=
    take_step (n := 2) (t := 92) (b := 25510) rfl rfl ArealUCore.ArealUK.chunk_12754 s55
  have s53 : leavesOK ctxLitU 517150000000 2 ((leaves.drop 25506).take 94) 259637500000 1 = true :=
    take_step (n := 2) (t := 94) (b := 25508) rfl rfl ArealUCore.ArealUK.chunk_12753 s54
  have s52 : leavesOK ctxLitU 517100000000 2 ((leaves.drop 25504).take 96) 259637500000 1 = true :=
    take_step (n := 2) (t := 96) (b := 25506) rfl rfl ArealUCore.ArealUK.chunk_12752 s53
  have s51 : leavesOK ctxLitU 517050000000 2 ((leaves.drop 25502).take 98) 259637500000 1 = true :=
    take_step (n := 2) (t := 98) (b := 25504) rfl rfl ArealUCore.ArealUK.chunk_12751 s52
  have s50 : leavesOK ctxLitU 517000000000 2 ((leaves.drop 25500).take 100) 259637500000 1 = true :=
    take_step (n := 2) (t := 100) (b := 25502) rfl rfl ArealUCore.ArealUK.chunk_12750 s51
  have s49 : leavesOK ctxLitU 516950000000 2 ((leaves.drop 25498).take 102) 259637500000 1 = true :=
    take_step (n := 2) (t := 102) (b := 25500) rfl rfl ArealUCore.ArealUK.chunk_12749 s50
  have s48 : leavesOK ctxLitU 516900000000 2 ((leaves.drop 25496).take 104) 259637500000 1 = true :=
    take_step (n := 2) (t := 104) (b := 25498) rfl rfl ArealUCore.ArealUK.chunk_12748 s49
  have s47 : leavesOK ctxLitU 516850000000 2 ((leaves.drop 25494).take 106) 259637500000 1 = true :=
    take_step (n := 2) (t := 106) (b := 25496) rfl rfl ArealUCore.ArealUK.chunk_12747 s48
  have s46 : leavesOK ctxLitU 516800000000 2 ((leaves.drop 25492).take 108) 259637500000 1 = true :=
    take_step (n := 2) (t := 108) (b := 25494) rfl rfl ArealUCore.ArealUK.chunk_12746 s47
  have s45 : leavesOK ctxLitU 516750000000 2 ((leaves.drop 25490).take 110) 259637500000 1 = true :=
    take_step (n := 2) (t := 110) (b := 25492) rfl rfl ArealUCore.ArealUK.chunk_12745 s46
  have s44 : leavesOK ctxLitU 516700000000 2 ((leaves.drop 25488).take 112) 259637500000 1 = true :=
    take_step (n := 2) (t := 112) (b := 25490) rfl rfl ArealUCore.ArealUK.chunk_12744 s45
  have s43 : leavesOK ctxLitU 516650000000 2 ((leaves.drop 25486).take 114) 259637500000 1 = true :=
    take_step (n := 2) (t := 114) (b := 25488) rfl rfl ArealUCore.ArealUK.chunk_12743 s44
  have s42 : leavesOK ctxLitU 516600000000 2 ((leaves.drop 25484).take 116) 259637500000 1 = true :=
    take_step (n := 2) (t := 116) (b := 25486) rfl rfl ArealUCore.ArealUK.chunk_12742 s43
  have s41 : leavesOK ctxLitU 516550000000 2 ((leaves.drop 25482).take 118) 259637500000 1 = true :=
    take_step (n := 2) (t := 118) (b := 25484) rfl rfl ArealUCore.ArealUK.chunk_12741 s42
  have s40 : leavesOK ctxLitU 516500000000 2 ((leaves.drop 25480).take 120) 259637500000 1 = true :=
    take_step (n := 2) (t := 120) (b := 25482) rfl rfl ArealUCore.ArealUK.chunk_12740 s41
  have s39 : leavesOK ctxLitU 516450000000 2 ((leaves.drop 25478).take 122) 259637500000 1 = true :=
    take_step (n := 2) (t := 122) (b := 25480) rfl rfl ArealUCore.ArealUK.chunk_12739 s40
  have s38 : leavesOK ctxLitU 516400000000 2 ((leaves.drop 25476).take 124) 259637500000 1 = true :=
    take_step (n := 2) (t := 124) (b := 25478) rfl rfl ArealUCore.ArealUK.chunk_12738 s39
  have s37 : leavesOK ctxLitU 258175000000 1 ((leaves.drop 25474).take 126) 259637500000 1 = true :=
    take_step (n := 2) (t := 126) (b := 25476) rfl rfl ArealUCore.ArealUK.chunk_12737 s38
  have s36 : leavesOK ctxLitU 258150000000 1 ((leaves.drop 25472).take 128) 259637500000 1 = true :=
    take_step (n := 2) (t := 128) (b := 25474) rfl rfl ArealUCore.ArealUK.chunk_12736 s37
  have s35 : leavesOK ctxLitU 258137500000 1 ((leaves.drop 25470).take 130) 259637500000 1 = true :=
    take_step (n := 2) (t := 130) (b := 25472) rfl rfl ArealUCore.ArealUK.chunk_12735 s36
  have s34 : leavesOK ctxLitU 258125000000 1 ((leaves.drop 25468).take 132) 259637500000 1 = true :=
    take_step (n := 2) (t := 132) (b := 25470) rfl rfl ArealUCore.ArealUK.chunk_12734 s35
  have s33 : leavesOK ctxLitU 129050000000 0 ((leaves.drop 25466).take 134) 259637500000 1 = true :=
    take_step (n := 2) (t := 134) (b := 25468) rfl rfl ArealUCore.ArealUK.chunk_12733 s34
  have s32 : leavesOK ctxLitU 129037500000 0 ((leaves.drop 25464).take 136) 259637500000 1 = true :=
    take_step (n := 2) (t := 136) (b := 25466) rfl rfl ArealUCore.ArealUK.chunk_12732 s33
  have s31 : leavesOK ctxLitU 258062500000 1 ((leaves.drop 25462).take 138) 259637500000 1 = true :=
    take_step (n := 2) (t := 138) (b := 25464) rfl rfl ArealUCore.ArealUK.chunk_12731 s32
  have s30 : leavesOK ctxLitU 258050000000 1 ((leaves.drop 25460).take 140) 259637500000 1 = true :=
    take_step (n := 2) (t := 140) (b := 25462) rfl rfl ArealUCore.ArealUK.chunk_12730 s31
  have s29 : leavesOK ctxLitU 258025000000 1 ((leaves.drop 25458).take 142) 259637500000 1 = true :=
    take_step (n := 2) (t := 142) (b := 25460) rfl rfl ArealUCore.ArealUK.chunk_12729 s30
  have s28 : leavesOK ctxLitU 258000000000 1 ((leaves.drop 25456).take 144) 259637500000 1 = true :=
    take_step (n := 2) (t := 144) (b := 25458) rfl rfl ArealUCore.ArealUK.chunk_12728 s29
  have s27 : leavesOK ctxLitU 515950000000 2 ((leaves.drop 25454).take 146) 259637500000 1 = true :=
    take_step (n := 2) (t := 146) (b := 25456) rfl rfl ArealUCore.ArealUK.chunk_12727 s28
  have s26 : leavesOK ctxLitU 515900000000 2 ((leaves.drop 25452).take 148) 259637500000 1 = true :=
    take_step (n := 2) (t := 148) (b := 25454) rfl rfl ArealUCore.ArealUK.chunk_12726 s27
  have s25 : leavesOK ctxLitU 515850000000 2 ((leaves.drop 25450).take 150) 259637500000 1 = true :=
    take_step (n := 2) (t := 150) (b := 25452) rfl rfl ArealUCore.ArealUK.chunk_12725 s26
  have s24 : leavesOK ctxLitU 515800000000 2 ((leaves.drop 25448).take 152) 259637500000 1 = true :=
    take_step (n := 2) (t := 152) (b := 25450) rfl rfl ArealUCore.ArealUK.chunk_12724 s25
  have s23 : leavesOK ctxLitU 515750000000 2 ((leaves.drop 25446).take 154) 259637500000 1 = true :=
    take_step (n := 2) (t := 154) (b := 25448) rfl rfl ArealUCore.ArealUK.chunk_12723 s24
  have s22 : leavesOK ctxLitU 515700000000 2 ((leaves.drop 25444).take 156) 259637500000 1 = true :=
    take_step (n := 2) (t := 156) (b := 25446) rfl rfl ArealUCore.ArealUK.chunk_12722 s23
  have s21 : leavesOK ctxLitU 515650000000 2 ((leaves.drop 25442).take 158) 259637500000 1 = true :=
    take_step (n := 2) (t := 158) (b := 25444) rfl rfl ArealUCore.ArealUK.chunk_12721 s22
  have s20 : leavesOK ctxLitU 515600000000 2 ((leaves.drop 25440).take 160) 259637500000 1 = true :=
    take_step (n := 2) (t := 160) (b := 25442) rfl rfl ArealUCore.ArealUK.chunk_12720 s21
  have s19 : leavesOK ctxLitU 515550000000 2 ((leaves.drop 25438).take 162) 259637500000 1 = true :=
    take_step (n := 2) (t := 162) (b := 25440) rfl rfl ArealUCore.ArealUK.chunk_12719 s20
  have s18 : leavesOK ctxLitU 515500000000 2 ((leaves.drop 25436).take 164) 259637500000 1 = true :=
    take_step (n := 2) (t := 164) (b := 25438) rfl rfl ArealUCore.ArealUK.chunk_12718 s19
  have s17 : leavesOK ctxLitU 515450000000 2 ((leaves.drop 25434).take 166) 259637500000 1 = true :=
    take_step (n := 2) (t := 166) (b := 25436) rfl rfl ArealUCore.ArealUK.chunk_12717 s18
  have s16 : leavesOK ctxLitU 515400000000 2 ((leaves.drop 25432).take 168) 259637500000 1 = true :=
    take_step (n := 2) (t := 168) (b := 25434) rfl rfl ArealUCore.ArealUK.chunk_12716 s17
  have s15 : leavesOK ctxLitU 515350000000 2 ((leaves.drop 25430).take 170) 259637500000 1 = true :=
    take_step (n := 2) (t := 170) (b := 25432) rfl rfl ArealUCore.ArealUK.chunk_12715 s16
  have s14 : leavesOK ctxLitU 515300000000 2 ((leaves.drop 25428).take 172) 259637500000 1 = true :=
    take_step (n := 2) (t := 172) (b := 25430) rfl rfl ArealUCore.ArealUK.chunk_12714 s15
  have s13 : leavesOK ctxLitU 515250000000 2 ((leaves.drop 25426).take 174) 259637500000 1 = true :=
    take_step (n := 2) (t := 174) (b := 25428) rfl rfl ArealUCore.ArealUK.chunk_12713 s14
  have s12 : leavesOK ctxLitU 515200000000 2 ((leaves.drop 25424).take 176) 259637500000 1 = true :=
    take_step (n := 2) (t := 176) (b := 25426) rfl rfl ArealUCore.ArealUK.chunk_12712 s13
  have s11 : leavesOK ctxLitU 515150000000 2 ((leaves.drop 25422).take 178) 259637500000 1 = true :=
    take_step (n := 2) (t := 178) (b := 25424) rfl rfl ArealUCore.ArealUK.chunk_12711 s12
  have s10 : leavesOK ctxLitU 515100000000 2 ((leaves.drop 25420).take 180) 259637500000 1 = true :=
    take_step (n := 2) (t := 180) (b := 25422) rfl rfl ArealUCore.ArealUK.chunk_12710 s11
  have s9 : leavesOK ctxLitU 515050000000 2 ((leaves.drop 25418).take 182) 259637500000 1 = true :=
    take_step (n := 2) (t := 182) (b := 25420) rfl rfl ArealUCore.ArealUK.chunk_12709 s10
  have s8 : leavesOK ctxLitU 515000000000 2 ((leaves.drop 25416).take 184) 259637500000 1 = true :=
    take_step (n := 2) (t := 184) (b := 25418) rfl rfl ArealUCore.ArealUK.chunk_12708 s9
  have s7 : leavesOK ctxLitU 514950000000 2 ((leaves.drop 25414).take 186) 259637500000 1 = true :=
    take_step (n := 2) (t := 186) (b := 25416) rfl rfl ArealUCore.ArealUK.chunk_12707 s8
  have s6 : leavesOK ctxLitU 514900000000 2 ((leaves.drop 25412).take 188) 259637500000 1 = true :=
    take_step (n := 2) (t := 188) (b := 25414) rfl rfl ArealUCore.ArealUK.chunk_12706 s7
  have s5 : leavesOK ctxLitU 514850000000 2 ((leaves.drop 25410).take 190) 259637500000 1 = true :=
    take_step (n := 2) (t := 190) (b := 25412) rfl rfl ArealUCore.ArealUK.chunk_12705 s6
  have s4 : leavesOK ctxLitU 514800000000 2 ((leaves.drop 25408).take 192) 259637500000 1 = true :=
    take_step (n := 2) (t := 192) (b := 25410) rfl rfl ArealUCore.ArealUK.chunk_12704 s5
  have s3 : leavesOK ctxLitU 514750000000 2 ((leaves.drop 25406).take 194) 259637500000 1 = true :=
    take_step (n := 2) (t := 194) (b := 25408) rfl rfl ArealUCore.ArealUK.chunk_12703 s4
  have s2 : leavesOK ctxLitU 514700000000 2 ((leaves.drop 25404).take 196) 259637500000 1 = true :=
    take_step (n := 2) (t := 196) (b := 25406) rfl rfl ArealUCore.ArealUK.chunk_12702 s3
  have s1 : leavesOK ctxLitU 514650000000 2 ((leaves.drop 25402).take 198) 259637500000 1 = true :=
    take_step (n := 2) (t := 198) (b := 25404) rfl rfl ArealUCore.ArealUK.chunk_12701 s2
  have s0 : leavesOK ctxLitU 514600000000 2 ((leaves.drop 25400).take 200) 259637500000 1 = true :=
    take_step (n := 2) (t := 200) (b := 25402) rfl rfl ArealUCore.ArealUK.chunk_12700 s1
  exact s0

end Areal.UCert

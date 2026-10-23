import ArealUK.Chunk6600
import ArealUK.Chunk6601
import ArealUK.Chunk6602
import ArealUK.Chunk6603
import ArealUK.Chunk6604
import ArealUK.Chunk6605
import ArealUK.Chunk6606
import ArealUK.Chunk6607
import ArealUK.Chunk6608
import ArealUK.Chunk6609
import ArealUK.Chunk6610
import ArealUK.Chunk6611
import ArealUK.Chunk6612
import ArealUK.Chunk6613
import ArealUK.Chunk6614
import ArealUK.Chunk6615
import ArealUK.Chunk6616
import ArealUK.Chunk6617
import ArealUK.Chunk6618
import ArealUK.Chunk6619
import ArealUK.Chunk6620
import ArealUK.Chunk6621
import ArealUK.Chunk6622
import ArealUK.Chunk6623
import ArealUK.Chunk6624
import ArealUK.Chunk6625
import ArealUK.Chunk6626
import ArealUK.Chunk6627
import ArealUK.Chunk6628
import ArealUK.Chunk6629
import ArealUK.Chunk6630
import ArealUK.Chunk6631
import ArealUK.Chunk6632
import ArealUK.Chunk6633
import ArealUK.Chunk6634
import ArealUK.Chunk6635
import ArealUK.Chunk6636
import ArealUK.Chunk6637
import ArealUK.Chunk6638
import ArealUK.Chunk6639
import ArealUK.Chunk6640
import ArealUK.Chunk6641
import ArealUK.Chunk6642
import ArealUK.Chunk6643
import ArealUK.Chunk6644
import ArealUK.Chunk6645
import ArealUK.Chunk6646
import ArealUK.Chunk6647
import ArealUK.Chunk6648
import ArealUK.Chunk6649
import ArealUK.Chunk6650
import ArealUK.Chunk6651
import ArealUK.Chunk6652
import ArealUK.Chunk6653
import ArealUK.Chunk6654
import ArealUK.Chunk6655
import ArealUK.Chunk6656
import ArealUK.Chunk6657
import ArealUK.Chunk6658
import ArealUK.Chunk6659
import ArealUK.Chunk6660
import ArealUK.Chunk6661
import ArealUK.Chunk6662
import ArealUK.Chunk6663
import ArealUK.Chunk6664
import ArealUK.Chunk6665
import ArealUK.Chunk6666
import ArealUK.Chunk6667
import ArealUK.Chunk6668
import ArealUK.Chunk6669
import ArealUK.Chunk6670
import ArealUK.Chunk6671
import ArealUK.Chunk6672
import ArealUK.Chunk6673
import ArealUK.Chunk6674
import ArealUK.Chunk6675
import ArealUK.Chunk6676
import ArealUK.Chunk6677
import ArealUK.Chunk6678
import ArealUK.Chunk6679
import ArealUK.Chunk6680
import ArealUK.Chunk6681
import ArealUK.Chunk6682
import ArealUK.Chunk6683
import ArealUK.Chunk6684
import ArealUK.Chunk6685
import ArealUK.Chunk6686
import ArealUK.Chunk6687
import ArealUK.Chunk6688
import ArealUK.Chunk6689
import ArealUK.Chunk6690
import ArealUK.Chunk6691
import ArealUK.Chunk6692
import ArealUK.Chunk6693
import ArealUK.Chunk6694
import ArealUK.Chunk6695
import ArealUK.Chunk6696
import ArealUK.Chunk6697
import ArealUK.Chunk6698
import ArealUK.Chunk6699
import Areal.UCert.LeavesKGen

/-! Group 66 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_66 : leavesOK ctxLitU 46425000000 0 ((leaves.drop 13200).take 200) 51250000000 0 = true := by
  have s99 := ArealUCore.ArealUK.chunk_6699
  have s98 : leavesOK ctxLitU 51150000000 0 ((leaves.drop 13396).take 4) 51250000000 0 = true :=
    take_step (n := 2) (t := 4) (b := 13398) rfl rfl ArealUCore.ArealUK.chunk_6698 s99
  have s97 : leavesOK ctxLitU 51100000000 0 ((leaves.drop 13394).take 6) 51250000000 0 = true :=
    take_step (n := 2) (t := 6) (b := 13396) rfl rfl ArealUCore.ArealUK.chunk_6697 s98
  have s96 : leavesOK ctxLitU 51050000000 0 ((leaves.drop 13392).take 8) 51250000000 0 = true :=
    take_step (n := 2) (t := 8) (b := 13394) rfl rfl ArealUCore.ArealUK.chunk_6696 s97
  have s95 : leavesOK ctxLitU 51000000000 0 ((leaves.drop 13390).take 10) 51250000000 0 = true :=
    take_step (n := 2) (t := 10) (b := 13392) rfl rfl ArealUCore.ArealUK.chunk_6695 s96
  have s94 : leavesOK ctxLitU 50950000000 0 ((leaves.drop 13388).take 12) 51250000000 0 = true :=
    take_step (n := 2) (t := 12) (b := 13390) rfl rfl ArealUCore.ArealUK.chunk_6694 s95
  have s93 : leavesOK ctxLitU 50900000000 0 ((leaves.drop 13386).take 14) 51250000000 0 = true :=
    take_step (n := 2) (t := 14) (b := 13388) rfl rfl ArealUCore.ArealUK.chunk_6693 s94
  have s92 : leavesOK ctxLitU 50850000000 0 ((leaves.drop 13384).take 16) 51250000000 0 = true :=
    take_step (n := 2) (t := 16) (b := 13386) rfl rfl ArealUCore.ArealUK.chunk_6692 s93
  have s91 : leavesOK ctxLitU 50800000000 0 ((leaves.drop 13382).take 18) 51250000000 0 = true :=
    take_step (n := 2) (t := 18) (b := 13384) rfl rfl ArealUCore.ArealUK.chunk_6691 s92
  have s90 : leavesOK ctxLitU 50750000000 0 ((leaves.drop 13380).take 20) 51250000000 0 = true :=
    take_step (n := 2) (t := 20) (b := 13382) rfl rfl ArealUCore.ArealUK.chunk_6690 s91
  have s89 : leavesOK ctxLitU 50700000000 0 ((leaves.drop 13378).take 22) 51250000000 0 = true :=
    take_step (n := 2) (t := 22) (b := 13380) rfl rfl ArealUCore.ArealUK.chunk_6689 s90
  have s88 : leavesOK ctxLitU 50650000000 0 ((leaves.drop 13376).take 24) 51250000000 0 = true :=
    take_step (n := 2) (t := 24) (b := 13378) rfl rfl ArealUCore.ArealUK.chunk_6688 s89
  have s87 : leavesOK ctxLitU 50600000000 0 ((leaves.drop 13374).take 26) 51250000000 0 = true :=
    take_step (n := 2) (t := 26) (b := 13376) rfl rfl ArealUCore.ArealUK.chunk_6687 s88
  have s86 : leavesOK ctxLitU 50550000000 0 ((leaves.drop 13372).take 28) 51250000000 0 = true :=
    take_step (n := 2) (t := 28) (b := 13374) rfl rfl ArealUCore.ArealUK.chunk_6686 s87
  have s85 : leavesOK ctxLitU 50500000000 0 ((leaves.drop 13370).take 30) 51250000000 0 = true :=
    take_step (n := 2) (t := 30) (b := 13372) rfl rfl ArealUCore.ArealUK.chunk_6685 s86
  have s84 : leavesOK ctxLitU 206803654226832 12 ((leaves.drop 13368).take 32) 51250000000 0 = true :=
    take_step (n := 2) (t := 32) (b := 13370) rfl rfl ArealUCore.ArealUK.chunk_6684 s85
  have s83 : leavesOK ctxLitU 50450000000 0 ((leaves.drop 13366).take 34) 51250000000 0 = true :=
    take_step (n := 2) (t := 34) (b := 13368) rfl rfl ArealUCore.ArealUK.chunk_6683 s84
  have s82 : leavesOK ctxLitU 50400000000 0 ((leaves.drop 13364).take 36) 51250000000 0 = true :=
    take_step (n := 2) (t := 36) (b := 13366) rfl rfl ArealUCore.ArealUK.chunk_6682 s83
  have s81 : leavesOK ctxLitU 50350000000 0 ((leaves.drop 13362).take 38) 51250000000 0 = true :=
    take_step (n := 2) (t := 38) (b := 13364) rfl rfl ArealUCore.ArealUK.chunk_6681 s82
  have s80 : leavesOK ctxLitU 50300000000 0 ((leaves.drop 13360).take 40) 51250000000 0 = true :=
    take_step (n := 2) (t := 40) (b := 13362) rfl rfl ArealUCore.ArealUK.chunk_6680 s81
  have s79 : leavesOK ctxLitU 50250000000 0 ((leaves.drop 13358).take 42) 51250000000 0 = true :=
    take_step (n := 2) (t := 42) (b := 13360) rfl rfl ArealUCore.ArealUK.chunk_6679 s80
  have s78 : leavesOK ctxLitU 50200000000 0 ((leaves.drop 13356).take 44) 51250000000 0 = true :=
    take_step (n := 2) (t := 44) (b := 13358) rfl rfl ArealUCore.ArealUK.chunk_6678 s79
  have s77 : leavesOK ctxLitU 50150000000 0 ((leaves.drop 13354).take 46) 51250000000 0 = true :=
    take_step (n := 2) (t := 46) (b := 13356) rfl rfl ArealUCore.ArealUK.chunk_6677 s78
  have s76 : leavesOK ctxLitU 50100000000 0 ((leaves.drop 13352).take 48) 51250000000 0 = true :=
    take_step (n := 2) (t := 48) (b := 13354) rfl rfl ArealUCore.ArealUK.chunk_6676 s77
  have s75 : leavesOK ctxLitU 50050000000 0 ((leaves.drop 13350).take 50) 51250000000 0 = true :=
    take_step (n := 2) (t := 50) (b := 13352) rfl rfl ArealUCore.ArealUK.chunk_6675 s76
  have s74 : leavesOK ctxLitU 50000000000 0 ((leaves.drop 13348).take 52) 51250000000 0 = true :=
    take_step (n := 2) (t := 52) (b := 13350) rfl rfl ArealUCore.ArealUK.chunk_6674 s75
  have s73 : leavesOK ctxLitU 49950000000 0 ((leaves.drop 13346).take 54) 51250000000 0 = true :=
    take_step (n := 2) (t := 54) (b := 13348) rfl rfl ArealUCore.ArealUK.chunk_6673 s74
  have s72 : leavesOK ctxLitU 49900000000 0 ((leaves.drop 13344).take 56) 51250000000 0 = true :=
    take_step (n := 2) (t := 56) (b := 13346) rfl rfl ArealUCore.ArealUK.chunk_6672 s73
  have s71 : leavesOK ctxLitU 49850000000 0 ((leaves.drop 13342).take 58) 51250000000 0 = true :=
    take_step (n := 2) (t := 58) (b := 13344) rfl rfl ArealUCore.ArealUK.chunk_6671 s72
  have s70 : leavesOK ctxLitU 49800000000 0 ((leaves.drop 13340).take 60) 51250000000 0 = true :=
    take_step (n := 2) (t := 60) (b := 13342) rfl rfl ArealUCore.ArealUK.chunk_6670 s71
  have s69 : leavesOK ctxLitU 49750000000 0 ((leaves.drop 13338).take 62) 51250000000 0 = true :=
    take_step (n := 2) (t := 62) (b := 13340) rfl rfl ArealUCore.ArealUK.chunk_6669 s70
  have s68 : leavesOK ctxLitU 49700000000 0 ((leaves.drop 13336).take 64) 51250000000 0 = true :=
    take_step (n := 2) (t := 64) (b := 13338) rfl rfl ArealUCore.ArealUK.chunk_6668 s69
  have s67 : leavesOK ctxLitU 49650000000 0 ((leaves.drop 13334).take 66) 51250000000 0 = true :=
    take_step (n := 2) (t := 66) (b := 13336) rfl rfl ArealUCore.ArealUK.chunk_6667 s68
  have s66 : leavesOK ctxLitU 49600000000 0 ((leaves.drop 13332).take 68) 51250000000 0 = true :=
    take_step (n := 2) (t := 68) (b := 13334) rfl rfl ArealUCore.ArealUK.chunk_6666 s67
  have s65 : leavesOK ctxLitU 49550000000 0 ((leaves.drop 13330).take 70) 51250000000 0 = true :=
    take_step (n := 2) (t := 70) (b := 13332) rfl rfl ArealUCore.ArealUK.chunk_6665 s66
  have s64 : leavesOK ctxLitU 49500000000 0 ((leaves.drop 13328).take 72) 51250000000 0 = true :=
    take_step (n := 2) (t := 72) (b := 13330) rfl rfl ArealUCore.ArealUK.chunk_6664 s65
  have s63 : leavesOK ctxLitU 49450000000 0 ((leaves.drop 13326).take 74) 51250000000 0 = true :=
    take_step (n := 2) (t := 74) (b := 13328) rfl rfl ArealUCore.ArealUK.chunk_6663 s64
  have s62 : leavesOK ctxLitU 49400000000 0 ((leaves.drop 13324).take 76) 51250000000 0 = true :=
    take_step (n := 2) (t := 76) (b := 13326) rfl rfl ArealUCore.ArealUK.chunk_6662 s63
  have s61 : leavesOK ctxLitU 49350000000 0 ((leaves.drop 13322).take 78) 51250000000 0 = true :=
    take_step (n := 2) (t := 78) (b := 13324) rfl rfl ArealUCore.ArealUK.chunk_6661 s62
  have s60 : leavesOK ctxLitU 49300000000 0 ((leaves.drop 13320).take 80) 51250000000 0 = true :=
    take_step (n := 2) (t := 80) (b := 13322) rfl rfl ArealUCore.ArealUK.chunk_6660 s61
  have s59 : leavesOK ctxLitU 49250000000 0 ((leaves.drop 13318).take 82) 51250000000 0 = true :=
    take_step (n := 2) (t := 82) (b := 13320) rfl rfl ArealUCore.ArealUK.chunk_6659 s60
  have s58 : leavesOK ctxLitU 49200000000 0 ((leaves.drop 13316).take 84) 51250000000 0 = true :=
    take_step (n := 2) (t := 84) (b := 13318) rfl rfl ArealUCore.ArealUK.chunk_6658 s59
  have s57 : leavesOK ctxLitU 49150000000 0 ((leaves.drop 13314).take 86) 51250000000 0 = true :=
    take_step (n := 2) (t := 86) (b := 13316) rfl rfl ArealUCore.ArealUK.chunk_6657 s58
  have s56 : leavesOK ctxLitU 49100000000 0 ((leaves.drop 13312).take 88) 51250000000 0 = true :=
    take_step (n := 2) (t := 88) (b := 13314) rfl rfl ArealUCore.ArealUK.chunk_6656 s57
  have s55 : leavesOK ctxLitU 49050000000 0 ((leaves.drop 13310).take 90) 51250000000 0 = true :=
    take_step (n := 2) (t := 90) (b := 13312) rfl rfl ArealUCore.ArealUK.chunk_6655 s56
  have s54 : leavesOK ctxLitU 49000000000 0 ((leaves.drop 13308).take 92) 51250000000 0 = true :=
    take_step (n := 2) (t := 92) (b := 13310) rfl rfl ArealUCore.ArealUK.chunk_6654 s55
  have s53 : leavesOK ctxLitU 48950000000 0 ((leaves.drop 13306).take 94) 51250000000 0 = true :=
    take_step (n := 2) (t := 94) (b := 13308) rfl rfl ArealUCore.ArealUK.chunk_6653 s54
  have s52 : leavesOK ctxLitU 48900000000 0 ((leaves.drop 13304).take 96) 51250000000 0 = true :=
    take_step (n := 2) (t := 96) (b := 13306) rfl rfl ArealUCore.ArealUK.chunk_6652 s53
  have s51 : leavesOK ctxLitU 48850000000 0 ((leaves.drop 13302).take 98) 51250000000 0 = true :=
    take_step (n := 2) (t := 98) (b := 13304) rfl rfl ArealUCore.ArealUK.chunk_6651 s52
  have s50 : leavesOK ctxLitU 48800000000 0 ((leaves.drop 13300).take 100) 51250000000 0 = true :=
    take_step (n := 2) (t := 100) (b := 13302) rfl rfl ArealUCore.ArealUK.chunk_6650 s51
  have s49 : leavesOK ctxLitU 48750000000 0 ((leaves.drop 13298).take 102) 51250000000 0 = true :=
    take_step (n := 2) (t := 102) (b := 13300) rfl rfl ArealUCore.ArealUK.chunk_6649 s50
  have s48 : leavesOK ctxLitU 48700000000 0 ((leaves.drop 13296).take 104) 51250000000 0 = true :=
    take_step (n := 2) (t := 104) (b := 13298) rfl rfl ArealUCore.ArealUK.chunk_6648 s49
  have s47 : leavesOK ctxLitU 48650000000 0 ((leaves.drop 13294).take 106) 51250000000 0 = true :=
    take_step (n := 2) (t := 106) (b := 13296) rfl rfl ArealUCore.ArealUK.chunk_6647 s48
  have s46 : leavesOK ctxLitU 48600000000 0 ((leaves.drop 13292).take 108) 51250000000 0 = true :=
    take_step (n := 2) (t := 108) (b := 13294) rfl rfl ArealUCore.ArealUK.chunk_6646 s47
  have s45 : leavesOK ctxLitU 48550000000 0 ((leaves.drop 13290).take 110) 51250000000 0 = true :=
    take_step (n := 2) (t := 110) (b := 13292) rfl rfl ArealUCore.ArealUK.chunk_6645 s46
  have s44 : leavesOK ctxLitU 48500000000 0 ((leaves.drop 13288).take 112) 51250000000 0 = true :=
    take_step (n := 2) (t := 112) (b := 13290) rfl rfl ArealUCore.ArealUK.chunk_6644 s45
  have s43 : leavesOK ctxLitU 48450000000 0 ((leaves.drop 13286).take 114) 51250000000 0 = true :=
    take_step (n := 2) (t := 114) (b := 13288) rfl rfl ArealUCore.ArealUK.chunk_6643 s44
  have s42 : leavesOK ctxLitU 48400000000 0 ((leaves.drop 13284).take 116) 51250000000 0 = true :=
    take_step (n := 2) (t := 116) (b := 13286) rfl rfl ArealUCore.ArealUK.chunk_6642 s43
  have s41 : leavesOK ctxLitU 48350000000 0 ((leaves.drop 13282).take 118) 51250000000 0 = true :=
    take_step (n := 2) (t := 118) (b := 13284) rfl rfl ArealUCore.ArealUK.chunk_6641 s42
  have s40 : leavesOK ctxLitU 48300000000 0 ((leaves.drop 13280).take 120) 51250000000 0 = true :=
    take_step (n := 2) (t := 120) (b := 13282) rfl rfl ArealUCore.ArealUK.chunk_6640 s41
  have s39 : leavesOK ctxLitU 48250000000 0 ((leaves.drop 13278).take 122) 51250000000 0 = true :=
    take_step (n := 2) (t := 122) (b := 13280) rfl rfl ArealUCore.ArealUK.chunk_6639 s40
  have s38 : leavesOK ctxLitU 48200000000 0 ((leaves.drop 13276).take 124) 51250000000 0 = true :=
    take_step (n := 2) (t := 124) (b := 13278) rfl rfl ArealUCore.ArealUK.chunk_6638 s39
  have s37 : leavesOK ctxLitU 48150000000 0 ((leaves.drop 13274).take 126) 51250000000 0 = true :=
    take_step (n := 2) (t := 126) (b := 13276) rfl rfl ArealUCore.ArealUK.chunk_6637 s38
  have s36 : leavesOK ctxLitU 48100000000 0 ((leaves.drop 13272).take 128) 51250000000 0 = true :=
    take_step (n := 2) (t := 128) (b := 13274) rfl rfl ArealUCore.ArealUK.chunk_6636 s37
  have s35 : leavesOK ctxLitU 48050000000 0 ((leaves.drop 13270).take 130) 51250000000 0 = true :=
    take_step (n := 2) (t := 130) (b := 13272) rfl rfl ArealUCore.ArealUK.chunk_6635 s36
  have s34 : leavesOK ctxLitU 48000000000 0 ((leaves.drop 13268).take 132) 51250000000 0 = true :=
    take_step (n := 2) (t := 132) (b := 13270) rfl rfl ArealUCore.ArealUK.chunk_6634 s35
  have s33 : leavesOK ctxLitU 47950000000 0 ((leaves.drop 13266).take 134) 51250000000 0 = true :=
    take_step (n := 2) (t := 134) (b := 13268) rfl rfl ArealUCore.ArealUK.chunk_6633 s34
  have s32 : leavesOK ctxLitU 47900000000 0 ((leaves.drop 13264).take 136) 51250000000 0 = true :=
    take_step (n := 2) (t := 136) (b := 13266) rfl rfl ArealUCore.ArealUK.chunk_6632 s33
  have s31 : leavesOK ctxLitU 47850000000 0 ((leaves.drop 13262).take 138) 51250000000 0 = true :=
    take_step (n := 2) (t := 138) (b := 13264) rfl rfl ArealUCore.ArealUK.chunk_6631 s32
  have s30 : leavesOK ctxLitU 47800000000 0 ((leaves.drop 13260).take 140) 51250000000 0 = true :=
    take_step (n := 2) (t := 140) (b := 13262) rfl rfl ArealUCore.ArealUK.chunk_6630 s31
  have s29 : leavesOK ctxLitU 47750000000 0 ((leaves.drop 13258).take 142) 51250000000 0 = true :=
    take_step (n := 2) (t := 142) (b := 13260) rfl rfl ArealUCore.ArealUK.chunk_6629 s30
  have s28 : leavesOK ctxLitU 47700000000 0 ((leaves.drop 13256).take 144) 51250000000 0 = true :=
    take_step (n := 2) (t := 144) (b := 13258) rfl rfl ArealUCore.ArealUK.chunk_6628 s29
  have s27 : leavesOK ctxLitU 47650000000 0 ((leaves.drop 13254).take 146) 51250000000 0 = true :=
    take_step (n := 2) (t := 146) (b := 13256) rfl rfl ArealUCore.ArealUK.chunk_6627 s28
  have s26 : leavesOK ctxLitU 47600000000 0 ((leaves.drop 13252).take 148) 51250000000 0 = true :=
    take_step (n := 2) (t := 148) (b := 13254) rfl rfl ArealUCore.ArealUK.chunk_6626 s27
  have s25 : leavesOK ctxLitU 47550000000 0 ((leaves.drop 13250).take 150) 51250000000 0 = true :=
    take_step (n := 2) (t := 150) (b := 13252) rfl rfl ArealUCore.ArealUK.chunk_6625 s26
  have s24 : leavesOK ctxLitU 47500000000 0 ((leaves.drop 13248).take 152) 51250000000 0 = true :=
    take_step (n := 2) (t := 152) (b := 13250) rfl rfl ArealUCore.ArealUK.chunk_6624 s25
  have s23 : leavesOK ctxLitU 47450000000 0 ((leaves.drop 13246).take 154) 51250000000 0 = true :=
    take_step (n := 2) (t := 154) (b := 13248) rfl rfl ArealUCore.ArealUK.chunk_6623 s24
  have s22 : leavesOK ctxLitU 47400000000 0 ((leaves.drop 13244).take 156) 51250000000 0 = true :=
    take_step (n := 2) (t := 156) (b := 13246) rfl rfl ArealUCore.ArealUK.chunk_6622 s23
  have s21 : leavesOK ctxLitU 47350000000 0 ((leaves.drop 13242).take 158) 51250000000 0 = true :=
    take_step (n := 2) (t := 158) (b := 13244) rfl rfl ArealUCore.ArealUK.chunk_6621 s22
  have s20 : leavesOK ctxLitU 47300000000 0 ((leaves.drop 13240).take 160) 51250000000 0 = true :=
    take_step (n := 2) (t := 160) (b := 13242) rfl rfl ArealUCore.ArealUK.chunk_6620 s21
  have s19 : leavesOK ctxLitU 47250000000 0 ((leaves.drop 13238).take 162) 51250000000 0 = true :=
    take_step (n := 2) (t := 162) (b := 13240) rfl rfl ArealUCore.ArealUK.chunk_6619 s20
  have s18 : leavesOK ctxLitU 47200000000 0 ((leaves.drop 13236).take 164) 51250000000 0 = true :=
    take_step (n := 2) (t := 164) (b := 13238) rfl rfl ArealUCore.ArealUK.chunk_6618 s19
  have s17 : leavesOK ctxLitU 47150000000 0 ((leaves.drop 13234).take 166) 51250000000 0 = true :=
    take_step (n := 2) (t := 166) (b := 13236) rfl rfl ArealUCore.ArealUK.chunk_6617 s18
  have s16 : leavesOK ctxLitU 47100000000 0 ((leaves.drop 13232).take 168) 51250000000 0 = true :=
    take_step (n := 2) (t := 168) (b := 13234) rfl rfl ArealUCore.ArealUK.chunk_6616 s17
  have s15 : leavesOK ctxLitU 47050000000 0 ((leaves.drop 13230).take 170) 51250000000 0 = true :=
    take_step (n := 2) (t := 170) (b := 13232) rfl rfl ArealUCore.ArealUK.chunk_6615 s16
  have s14 : leavesOK ctxLitU 47000000000 0 ((leaves.drop 13228).take 172) 51250000000 0 = true :=
    take_step (n := 2) (t := 172) (b := 13230) rfl rfl ArealUCore.ArealUK.chunk_6614 s15
  have s13 : leavesOK ctxLitU 46950000000 0 ((leaves.drop 13226).take 174) 51250000000 0 = true :=
    take_step (n := 2) (t := 174) (b := 13228) rfl rfl ArealUCore.ArealUK.chunk_6613 s14
  have s12 : leavesOK ctxLitU 46900000000 0 ((leaves.drop 13224).take 176) 51250000000 0 = true :=
    take_step (n := 2) (t := 176) (b := 13226) rfl rfl ArealUCore.ArealUK.chunk_6612 s13
  have s11 : leavesOK ctxLitU 46850000000 0 ((leaves.drop 13222).take 178) 51250000000 0 = true :=
    take_step (n := 2) (t := 178) (b := 13224) rfl rfl ArealUCore.ArealUK.chunk_6611 s12
  have s10 : leavesOK ctxLitU 46800000000 0 ((leaves.drop 13220).take 180) 51250000000 0 = true :=
    take_step (n := 2) (t := 180) (b := 13222) rfl rfl ArealUCore.ArealUK.chunk_6610 s11
  have s9 : leavesOK ctxLitU 46775000000 0 ((leaves.drop 13218).take 182) 51250000000 0 = true :=
    take_step (n := 2) (t := 182) (b := 13220) rfl rfl ArealUCore.ArealUK.chunk_6609 s10
  have s8 : leavesOK ctxLitU 46762500000 0 ((leaves.drop 13216).take 184) 51250000000 0 = true :=
    take_step (n := 2) (t := 184) (b := 13218) rfl rfl ArealUCore.ArealUK.chunk_6608 s9
  have s7 : leavesOK ctxLitU 46750000000 0 ((leaves.drop 13214).take 186) 51250000000 0 = true :=
    take_step (n := 2) (t := 186) (b := 13216) rfl rfl ArealUCore.ArealUK.chunk_6607 s8
  have s6 : leavesOK ctxLitU 46725000000 0 ((leaves.drop 13212).take 188) 51250000000 0 = true :=
    take_step (n := 2) (t := 188) (b := 13214) rfl rfl ArealUCore.ArealUK.chunk_6606 s7
  have s5 : leavesOK ctxLitU 46675000000 0 ((leaves.drop 13210).take 190) 51250000000 0 = true :=
    take_step (n := 2) (t := 190) (b := 13212) rfl rfl ArealUCore.ArealUK.chunk_6605 s6
  have s4 : leavesOK ctxLitU 46625000000 0 ((leaves.drop 13208).take 192) 51250000000 0 = true :=
    take_step (n := 2) (t := 192) (b := 13210) rfl rfl ArealUCore.ArealUK.chunk_6604 s5
  have s3 : leavesOK ctxLitU 46575000000 0 ((leaves.drop 13206).take 194) 51250000000 0 = true :=
    take_step (n := 2) (t := 194) (b := 13208) rfl rfl ArealUCore.ArealUK.chunk_6603 s4
  have s2 : leavesOK ctxLitU 46525000000 0 ((leaves.drop 13204).take 196) 51250000000 0 = true :=
    take_step (n := 2) (t := 196) (b := 13206) rfl rfl ArealUCore.ArealUK.chunk_6602 s3
  have s1 : leavesOK ctxLitU 46475000000 0 ((leaves.drop 13202).take 198) 51250000000 0 = true :=
    take_step (n := 2) (t := 198) (b := 13204) rfl rfl ArealUCore.ArealUK.chunk_6601 s2
  have s0 : leavesOK ctxLitU 46425000000 0 ((leaves.drop 13200).take 200) 51250000000 0 = true :=
    take_step (n := 2) (t := 200) (b := 13202) rfl rfl ArealUCore.ArealUK.chunk_6600 s1
  exact s0

end Areal.UCert

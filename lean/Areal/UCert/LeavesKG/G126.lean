import ArealUK.Chunk12600
import ArealUK.Chunk12601
import ArealUK.Chunk12602
import ArealUK.Chunk12603
import ArealUK.Chunk12604
import ArealUK.Chunk12605
import ArealUK.Chunk12606
import ArealUK.Chunk12607
import ArealUK.Chunk12608
import ArealUK.Chunk12609
import ArealUK.Chunk12610
import ArealUK.Chunk12611
import ArealUK.Chunk12612
import ArealUK.Chunk12613
import ArealUK.Chunk12614
import ArealUK.Chunk12615
import ArealUK.Chunk12616
import ArealUK.Chunk12617
import ArealUK.Chunk12618
import ArealUK.Chunk12619
import ArealUK.Chunk12620
import ArealUK.Chunk12621
import ArealUK.Chunk12622
import ArealUK.Chunk12623
import ArealUK.Chunk12624
import ArealUK.Chunk12625
import ArealUK.Chunk12626
import ArealUK.Chunk12627
import ArealUK.Chunk12628
import ArealUK.Chunk12629
import ArealUK.Chunk12630
import ArealUK.Chunk12631
import ArealUK.Chunk12632
import ArealUK.Chunk12633
import ArealUK.Chunk12634
import ArealUK.Chunk12635
import ArealUK.Chunk12636
import ArealUK.Chunk12637
import ArealUK.Chunk12638
import ArealUK.Chunk12639
import ArealUK.Chunk12640
import ArealUK.Chunk12641
import ArealUK.Chunk12642
import ArealUK.Chunk12643
import ArealUK.Chunk12644
import ArealUK.Chunk12645
import ArealUK.Chunk12646
import ArealUK.Chunk12647
import ArealUK.Chunk12648
import ArealUK.Chunk12649
import ArealUK.Chunk12650
import ArealUK.Chunk12651
import ArealUK.Chunk12652
import ArealUK.Chunk12653
import ArealUK.Chunk12654
import ArealUK.Chunk12655
import ArealUK.Chunk12656
import ArealUK.Chunk12657
import ArealUK.Chunk12658
import ArealUK.Chunk12659
import ArealUK.Chunk12660
import ArealUK.Chunk12661
import ArealUK.Chunk12662
import ArealUK.Chunk12663
import ArealUK.Chunk12664
import ArealUK.Chunk12665
import ArealUK.Chunk12666
import ArealUK.Chunk12667
import ArealUK.Chunk12668
import ArealUK.Chunk12669
import ArealUK.Chunk12670
import ArealUK.Chunk12671
import ArealUK.Chunk12672
import ArealUK.Chunk12673
import ArealUK.Chunk12674
import ArealUK.Chunk12675
import ArealUK.Chunk12676
import ArealUK.Chunk12677
import ArealUK.Chunk12678
import ArealUK.Chunk12679
import ArealUK.Chunk12680
import ArealUK.Chunk12681
import ArealUK.Chunk12682
import ArealUK.Chunk12683
import ArealUK.Chunk12684
import ArealUK.Chunk12685
import ArealUK.Chunk12686
import ArealUK.Chunk12687
import ArealUK.Chunk12688
import ArealUK.Chunk12689
import ArealUK.Chunk12690
import ArealUK.Chunk12691
import ArealUK.Chunk12692
import ArealUK.Chunk12693
import ArealUK.Chunk12694
import ArealUK.Chunk12695
import ArealUK.Chunk12696
import ArealUK.Chunk12697
import ArealUK.Chunk12698
import ArealUK.Chunk12699
import Areal.UCert.LeavesKGen

/-! Group 126 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_126 : leavesOK ctxLitU 510075000000 2 ((leaves.drop 25200).take 200) 514600000000 2 = true := by
  have s99 := ArealUCore.ArealUK.chunk_12699
  have s98 : leavesOK ctxLitU 514500000000 2 ((leaves.drop 25396).take 4) 514600000000 2 = true :=
    take_step (n := 2) (t := 4) (b := 25398) rfl rfl ArealUCore.ArealUK.chunk_12698 s99
  have s97 : leavesOK ctxLitU 514450000000 2 ((leaves.drop 25394).take 6) 514600000000 2 = true :=
    take_step (n := 2) (t := 6) (b := 25396) rfl rfl ArealUCore.ArealUK.chunk_12697 s98
  have s96 : leavesOK ctxLitU 514400000000 2 ((leaves.drop 25392).take 8) 514600000000 2 = true :=
    take_step (n := 2) (t := 8) (b := 25394) rfl rfl ArealUCore.ArealUK.chunk_12696 s97
  have s95 : leavesOK ctxLitU 514350000000 2 ((leaves.drop 25390).take 10) 514600000000 2 = true :=
    take_step (n := 2) (t := 10) (b := 25392) rfl rfl ArealUCore.ArealUK.chunk_12695 s96
  have s94 : leavesOK ctxLitU 514300000000 2 ((leaves.drop 25388).take 12) 514600000000 2 = true :=
    take_step (n := 2) (t := 12) (b := 25390) rfl rfl ArealUCore.ArealUK.chunk_12694 s95
  have s93 : leavesOK ctxLitU 514250000000 2 ((leaves.drop 25386).take 14) 514600000000 2 = true :=
    take_step (n := 2) (t := 14) (b := 25388) rfl rfl ArealUCore.ArealUK.chunk_12693 s94
  have s92 : leavesOK ctxLitU 514200000000 2 ((leaves.drop 25384).take 16) 514600000000 2 = true :=
    take_step (n := 2) (t := 16) (b := 25386) rfl rfl ArealUCore.ArealUK.chunk_12692 s93
  have s91 : leavesOK ctxLitU 514150000000 2 ((leaves.drop 25382).take 18) 514600000000 2 = true :=
    take_step (n := 2) (t := 18) (b := 25384) rfl rfl ArealUCore.ArealUK.chunk_12691 s92
  have s90 : leavesOK ctxLitU 514100000000 2 ((leaves.drop 25380).take 20) 514600000000 2 = true :=
    take_step (n := 2) (t := 20) (b := 25382) rfl rfl ArealUCore.ArealUK.chunk_12690 s91
  have s89 : leavesOK ctxLitU 514050000000 2 ((leaves.drop 25378).take 22) 514600000000 2 = true :=
    take_step (n := 2) (t := 22) (b := 25380) rfl rfl ArealUCore.ArealUK.chunk_12689 s90
  have s88 : leavesOK ctxLitU 514000000000 2 ((leaves.drop 25376).take 24) 514600000000 2 = true :=
    take_step (n := 2) (t := 24) (b := 25378) rfl rfl ArealUCore.ArealUK.chunk_12688 s89
  have s87 : leavesOK ctxLitU 513950000000 2 ((leaves.drop 25374).take 26) 514600000000 2 = true :=
    take_step (n := 2) (t := 26) (b := 25376) rfl rfl ArealUCore.ArealUK.chunk_12687 s88
  have s86 : leavesOK ctxLitU 513900000000 2 ((leaves.drop 25372).take 28) 514600000000 2 = true :=
    take_step (n := 2) (t := 28) (b := 25374) rfl rfl ArealUCore.ArealUK.chunk_12686 s87
  have s85 : leavesOK ctxLitU 513850000000 2 ((leaves.drop 25370).take 30) 514600000000 2 = true :=
    take_step (n := 2) (t := 30) (b := 25372) rfl rfl ArealUCore.ArealUK.chunk_12685 s86
  have s84 : leavesOK ctxLitU 513800000000 2 ((leaves.drop 25368).take 32) 514600000000 2 = true :=
    take_step (n := 2) (t := 32) (b := 25370) rfl rfl ArealUCore.ArealUK.chunk_12684 s85
  have s83 : leavesOK ctxLitU 513750000000 2 ((leaves.drop 25366).take 34) 514600000000 2 = true :=
    take_step (n := 2) (t := 34) (b := 25368) rfl rfl ArealUCore.ArealUK.chunk_12683 s84
  have s82 : leavesOK ctxLitU 513700000000 2 ((leaves.drop 25364).take 36) 514600000000 2 = true :=
    take_step (n := 2) (t := 36) (b := 25366) rfl rfl ArealUCore.ArealUK.chunk_12682 s83
  have s81 : leavesOK ctxLitU 513650000000 2 ((leaves.drop 25362).take 38) 514600000000 2 = true :=
    take_step (n := 2) (t := 38) (b := 25364) rfl rfl ArealUCore.ArealUK.chunk_12681 s82
  have s80 : leavesOK ctxLitU 513600000000 2 ((leaves.drop 25360).take 40) 514600000000 2 = true :=
    take_step (n := 2) (t := 40) (b := 25362) rfl rfl ArealUCore.ArealUK.chunk_12680 s81
  have s79 : leavesOK ctxLitU 513550000000 2 ((leaves.drop 25358).take 42) 514600000000 2 = true :=
    take_step (n := 2) (t := 42) (b := 25360) rfl rfl ArealUCore.ArealUK.chunk_12679 s80
  have s78 : leavesOK ctxLitU 513500000000 2 ((leaves.drop 25356).take 44) 514600000000 2 = true :=
    take_step (n := 2) (t := 44) (b := 25358) rfl rfl ArealUCore.ArealUK.chunk_12678 s79
  have s77 : leavesOK ctxLitU 513450000000 2 ((leaves.drop 25354).take 46) 514600000000 2 = true :=
    take_step (n := 2) (t := 46) (b := 25356) rfl rfl ArealUCore.ArealUK.chunk_12677 s78
  have s76 : leavesOK ctxLitU 513400000000 2 ((leaves.drop 25352).take 48) 514600000000 2 = true :=
    take_step (n := 2) (t := 48) (b := 25354) rfl rfl ArealUCore.ArealUK.chunk_12676 s77
  have s75 : leavesOK ctxLitU 513350000000 2 ((leaves.drop 25350).take 50) 514600000000 2 = true :=
    take_step (n := 2) (t := 50) (b := 25352) rfl rfl ArealUCore.ArealUK.chunk_12675 s76
  have s74 : leavesOK ctxLitU 513300000000 2 ((leaves.drop 25348).take 52) 514600000000 2 = true :=
    take_step (n := 2) (t := 52) (b := 25350) rfl rfl ArealUCore.ArealUK.chunk_12674 s75
  have s73 : leavesOK ctxLitU 513250000000 2 ((leaves.drop 25346).take 54) 514600000000 2 = true :=
    take_step (n := 2) (t := 54) (b := 25348) rfl rfl ArealUCore.ArealUK.chunk_12673 s74
  have s72 : leavesOK ctxLitU 513200000000 2 ((leaves.drop 25344).take 56) 514600000000 2 = true :=
    take_step (n := 2) (t := 56) (b := 25346) rfl rfl ArealUCore.ArealUK.chunk_12672 s73
  have s71 : leavesOK ctxLitU 513150000000 2 ((leaves.drop 25342).take 58) 514600000000 2 = true :=
    take_step (n := 2) (t := 58) (b := 25344) rfl rfl ArealUCore.ArealUK.chunk_12671 s72
  have s70 : leavesOK ctxLitU 513100000000 2 ((leaves.drop 25340).take 60) 514600000000 2 = true :=
    take_step (n := 2) (t := 60) (b := 25342) rfl rfl ArealUCore.ArealUK.chunk_12670 s71
  have s69 : leavesOK ctxLitU 513050000000 2 ((leaves.drop 25338).take 62) 514600000000 2 = true :=
    take_step (n := 2) (t := 62) (b := 25340) rfl rfl ArealUCore.ArealUK.chunk_12669 s70
  have s68 : leavesOK ctxLitU 513000000000 2 ((leaves.drop 25336).take 64) 514600000000 2 = true :=
    take_step (n := 2) (t := 64) (b := 25338) rfl rfl ArealUCore.ArealUK.chunk_12668 s69
  have s67 : leavesOK ctxLitU 512950000000 2 ((leaves.drop 25334).take 66) 514600000000 2 = true :=
    take_step (n := 2) (t := 66) (b := 25336) rfl rfl ArealUCore.ArealUK.chunk_12667 s68
  have s66 : leavesOK ctxLitU 512900000000 2 ((leaves.drop 25332).take 68) 514600000000 2 = true :=
    take_step (n := 2) (t := 68) (b := 25334) rfl rfl ArealUCore.ArealUK.chunk_12666 s67
  have s65 : leavesOK ctxLitU 512850000000 2 ((leaves.drop 25330).take 70) 514600000000 2 = true :=
    take_step (n := 2) (t := 70) (b := 25332) rfl rfl ArealUCore.ArealUK.chunk_12665 s66
  have s64 : leavesOK ctxLitU 512800000000 2 ((leaves.drop 25328).take 72) 514600000000 2 = true :=
    take_step (n := 2) (t := 72) (b := 25330) rfl rfl ArealUCore.ArealUK.chunk_12664 s65
  have s63 : leavesOK ctxLitU 512750000000 2 ((leaves.drop 25326).take 74) 514600000000 2 = true :=
    take_step (n := 2) (t := 74) (b := 25328) rfl rfl ArealUCore.ArealUK.chunk_12663 s64
  have s62 : leavesOK ctxLitU 512700000000 2 ((leaves.drop 25324).take 76) 514600000000 2 = true :=
    take_step (n := 2) (t := 76) (b := 25326) rfl rfl ArealUCore.ArealUK.chunk_12662 s63
  have s61 : leavesOK ctxLitU 512650000000 2 ((leaves.drop 25322).take 78) 514600000000 2 = true :=
    take_step (n := 2) (t := 78) (b := 25324) rfl rfl ArealUCore.ArealUK.chunk_12661 s62
  have s60 : leavesOK ctxLitU 512600000000 2 ((leaves.drop 25320).take 80) 514600000000 2 = true :=
    take_step (n := 2) (t := 80) (b := 25322) rfl rfl ArealUCore.ArealUK.chunk_12660 s61
  have s59 : leavesOK ctxLitU 512550000000 2 ((leaves.drop 25318).take 82) 514600000000 2 = true :=
    take_step (n := 2) (t := 82) (b := 25320) rfl rfl ArealUCore.ArealUK.chunk_12659 s60
  have s58 : leavesOK ctxLitU 512500000000 2 ((leaves.drop 25316).take 84) 514600000000 2 = true :=
    take_step (n := 2) (t := 84) (b := 25318) rfl rfl ArealUCore.ArealUK.chunk_12658 s59
  have s57 : leavesOK ctxLitU 512450000000 2 ((leaves.drop 25314).take 86) 514600000000 2 = true :=
    take_step (n := 2) (t := 86) (b := 25316) rfl rfl ArealUCore.ArealUK.chunk_12657 s58
  have s56 : leavesOK ctxLitU 512400000000 2 ((leaves.drop 25312).take 88) 514600000000 2 = true :=
    take_step (n := 2) (t := 88) (b := 25314) rfl rfl ArealUCore.ArealUK.chunk_12656 s57
  have s55 : leavesOK ctxLitU 512350000000 2 ((leaves.drop 25310).take 90) 514600000000 2 = true :=
    take_step (n := 2) (t := 90) (b := 25312) rfl rfl ArealUCore.ArealUK.chunk_12655 s56
  have s54 : leavesOK ctxLitU 512300000000 2 ((leaves.drop 25308).take 92) 514600000000 2 = true :=
    take_step (n := 2) (t := 92) (b := 25310) rfl rfl ArealUCore.ArealUK.chunk_12654 s55
  have s53 : leavesOK ctxLitU 512250000000 2 ((leaves.drop 25306).take 94) 514600000000 2 = true :=
    take_step (n := 2) (t := 94) (b := 25308) rfl rfl ArealUCore.ArealUK.chunk_12653 s54
  have s52 : leavesOK ctxLitU 512200000000 2 ((leaves.drop 25304).take 96) 514600000000 2 = true :=
    take_step (n := 2) (t := 96) (b := 25306) rfl rfl ArealUCore.ArealUK.chunk_12652 s53
  have s51 : leavesOK ctxLitU 512150000000 2 ((leaves.drop 25302).take 98) 514600000000 2 = true :=
    take_step (n := 2) (t := 98) (b := 25304) rfl rfl ArealUCore.ArealUK.chunk_12651 s52
  have s50 : leavesOK ctxLitU 512100000000 2 ((leaves.drop 25300).take 100) 514600000000 2 = true :=
    take_step (n := 2) (t := 100) (b := 25302) rfl rfl ArealUCore.ArealUK.chunk_12650 s51
  have s49 : leavesOK ctxLitU 512050000000 2 ((leaves.drop 25298).take 102) 514600000000 2 = true :=
    take_step (n := 2) (t := 102) (b := 25300) rfl rfl ArealUCore.ArealUK.chunk_12649 s50
  have s48 : leavesOK ctxLitU 512000000000 2 ((leaves.drop 25296).take 104) 514600000000 2 = true :=
    take_step (n := 2) (t := 104) (b := 25298) rfl rfl ArealUCore.ArealUK.chunk_12648 s49
  have s47 : leavesOK ctxLitU 511950000000 2 ((leaves.drop 25294).take 106) 514600000000 2 = true :=
    take_step (n := 2) (t := 106) (b := 25296) rfl rfl ArealUCore.ArealUK.chunk_12647 s48
  have s46 : leavesOK ctxLitU 511900000000 2 ((leaves.drop 25292).take 108) 514600000000 2 = true :=
    take_step (n := 2) (t := 108) (b := 25294) rfl rfl ArealUCore.ArealUK.chunk_12646 s47
  have s45 : leavesOK ctxLitU 511850000000 2 ((leaves.drop 25290).take 110) 514600000000 2 = true :=
    take_step (n := 2) (t := 110) (b := 25292) rfl rfl ArealUCore.ArealUK.chunk_12645 s46
  have s44 : leavesOK ctxLitU 511800000000 2 ((leaves.drop 25288).take 112) 514600000000 2 = true :=
    take_step (n := 2) (t := 112) (b := 25290) rfl rfl ArealUCore.ArealUK.chunk_12644 s45
  have s43 : leavesOK ctxLitU 511750000000 2 ((leaves.drop 25286).take 114) 514600000000 2 = true :=
    take_step (n := 2) (t := 114) (b := 25288) rfl rfl ArealUCore.ArealUK.chunk_12643 s44
  have s42 : leavesOK ctxLitU 511700000000 2 ((leaves.drop 25284).take 116) 514600000000 2 = true :=
    take_step (n := 2) (t := 116) (b := 25286) rfl rfl ArealUCore.ArealUK.chunk_12642 s43
  have s41 : leavesOK ctxLitU 511650000000 2 ((leaves.drop 25282).take 118) 514600000000 2 = true :=
    take_step (n := 2) (t := 118) (b := 25284) rfl rfl ArealUCore.ArealUK.chunk_12641 s42
  have s40 : leavesOK ctxLitU 511600000000 2 ((leaves.drop 25280).take 120) 514600000000 2 = true :=
    take_step (n := 2) (t := 120) (b := 25282) rfl rfl ArealUCore.ArealUK.chunk_12640 s41
  have s39 : leavesOK ctxLitU 511550000000 2 ((leaves.drop 25278).take 122) 514600000000 2 = true :=
    take_step (n := 2) (t := 122) (b := 25280) rfl rfl ArealUCore.ArealUK.chunk_12639 s40
  have s38 : leavesOK ctxLitU 511500000000 2 ((leaves.drop 25276).take 124) 514600000000 2 = true :=
    take_step (n := 2) (t := 124) (b := 25278) rfl rfl ArealUCore.ArealUK.chunk_12638 s39
  have s37 : leavesOK ctxLitU 511450000000 2 ((leaves.drop 25274).take 126) 514600000000 2 = true :=
    take_step (n := 2) (t := 126) (b := 25276) rfl rfl ArealUCore.ArealUK.chunk_12637 s38
  have s36 : leavesOK ctxLitU 511400000000 2 ((leaves.drop 25272).take 128) 514600000000 2 = true :=
    take_step (n := 2) (t := 128) (b := 25274) rfl rfl ArealUCore.ArealUK.chunk_12636 s37
  have s35 : leavesOK ctxLitU 511350000000 2 ((leaves.drop 25270).take 130) 514600000000 2 = true :=
    take_step (n := 2) (t := 130) (b := 25272) rfl rfl ArealUCore.ArealUK.chunk_12635 s36
  have s34 : leavesOK ctxLitU 511300000000 2 ((leaves.drop 25268).take 132) 514600000000 2 = true :=
    take_step (n := 2) (t := 132) (b := 25270) rfl rfl ArealUCore.ArealUK.chunk_12634 s35
  have s33 : leavesOK ctxLitU 255625000000 1 ((leaves.drop 25266).take 134) 514600000000 2 = true :=
    take_step (n := 2) (t := 134) (b := 25268) rfl rfl ArealUCore.ArealUK.chunk_12633 s34
  have s32 : leavesOK ctxLitU 255600000000 1 ((leaves.drop 25264).take 136) 514600000000 2 = true :=
    take_step (n := 2) (t := 136) (b := 25266) rfl rfl ArealUCore.ArealUK.chunk_12632 s33
  have s31 : leavesOK ctxLitU 127787500000 0 ((leaves.drop 25262).take 138) 514600000000 2 = true :=
    take_step (n := 2) (t := 138) (b := 25264) rfl rfl ArealUCore.ArealUK.chunk_12631 s32
  have s30 : leavesOK ctxLitU 127775000000 0 ((leaves.drop 25260).take 140) 514600000000 2 = true :=
    take_step (n := 2) (t := 140) (b := 25262) rfl rfl ArealUCore.ArealUK.chunk_12630 s31
  have s29 : leavesOK ctxLitU 127762500000 0 ((leaves.drop 25258).take 142) 514600000000 2 = true :=
    take_step (n := 2) (t := 142) (b := 25260) rfl rfl ArealUCore.ArealUK.chunk_12629 s30
  have s28 : leavesOK ctxLitU 127750000000 0 ((leaves.drop 25256).take 144) 514600000000 2 = true :=
    take_step (n := 2) (t := 144) (b := 25258) rfl rfl ArealUCore.ArealUK.chunk_12628 s29
  have s27 : leavesOK ctxLitU 127737500000 0 ((leaves.drop 25254).take 146) 514600000000 2 = true :=
    take_step (n := 2) (t := 146) (b := 25256) rfl rfl ArealUCore.ArealUK.chunk_12627 s28
  have s26 : leavesOK ctxLitU 255462500000 1 ((leaves.drop 25252).take 148) 514600000000 2 = true :=
    take_step (n := 2) (t := 148) (b := 25254) rfl rfl ArealUCore.ArealUK.chunk_12626 s27
  have s25 : leavesOK ctxLitU 255450000000 1 ((leaves.drop 25250).take 150) 514600000000 2 = true :=
    take_step (n := 2) (t := 150) (b := 25252) rfl rfl ArealUCore.ArealUK.chunk_12625 s26
  have s24 : leavesOK ctxLitU 255437500000 1 ((leaves.drop 25248).take 152) 514600000000 2 = true :=
    take_step (n := 2) (t := 152) (b := 25250) rfl rfl ArealUCore.ArealUK.chunk_12624 s25
  have s23 : leavesOK ctxLitU 510856250000 2 ((leaves.drop 25246).take 154) 514600000000 2 = true :=
    take_step (n := 2) (t := 154) (b := 25248) rfl rfl ArealUCore.ArealUK.chunk_12623 s24
  have s22 : leavesOK ctxLitU 1046198791304047 13 ((leaves.drop 25244).take 156) 514600000000 2 = true :=
    take_step (n := 2) (t := 156) (b := 25246) rfl rfl ArealUCore.ArealUK.chunk_12622 s23
  have s21 : leavesOK ctxLitU 523088391304044 12 ((leaves.drop 25242).take 158) 514600000000 2 = true :=
    take_step (n := 2) (t := 158) (b := 25244) rfl rfl ArealUCore.ArealUK.chunk_12621 s22
  have s20 : leavesOK ctxLitU 1021643750000 3 ((leaves.drop 25240).take 160) 514600000000 2 = true :=
    take_step (n := 2) (t := 160) (b := 25242) rfl rfl ArealUCore.ArealUK.chunk_12620 s21
  have s19 : leavesOK ctxLitU 510812500000 2 ((leaves.drop 25238).take 162) 514600000000 2 = true :=
    take_step (n := 2) (t := 162) (b := 25240) rfl rfl ArealUCore.ArealUK.chunk_12619 s20
  have s18 : leavesOK ctxLitU 510800000000 2 ((leaves.drop 25236).take 164) 514600000000 2 = true :=
    take_step (n := 2) (t := 164) (b := 25238) rfl rfl ArealUCore.ArealUK.chunk_12618 s19
  have s17 : leavesOK ctxLitU 510781250000 2 ((leaves.drop 25234).take 166) 514600000000 2 = true :=
    take_step (n := 2) (t := 166) (b := 25236) rfl rfl ArealUCore.ArealUK.chunk_12617 s18
  have s16 : leavesOK ctxLitU 510768750000 2 ((leaves.drop 25232).take 168) 514600000000 2 = true :=
    take_step (n := 2) (t := 168) (b := 25234) rfl rfl ArealUCore.ArealUK.chunk_12616 s17
  have s15 : leavesOK ctxLitU 255375000000 1 ((leaves.drop 25230).take 170) 514600000000 2 = true :=
    take_step (n := 2) (t := 170) (b := 25232) rfl rfl ArealUCore.ArealUK.chunk_12615 s16
  have s14 : leavesOK ctxLitU 255362500000 1 ((leaves.drop 25228).take 172) 514600000000 2 = true :=
    take_step (n := 2) (t := 172) (b := 25230) rfl rfl ArealUCore.ArealUK.chunk_12614 s15
  have s13 : leavesOK ctxLitU 255350000000 1 ((leaves.drop 25226).take 174) 514600000000 2 = true :=
    take_step (n := 2) (t := 174) (b := 25228) rfl rfl ArealUCore.ArealUK.chunk_12613 s14
  have s12 : leavesOK ctxLitU 127662500000 0 ((leaves.drop 25224).take 176) 514600000000 2 = true :=
    take_step (n := 2) (t := 176) (b := 25226) rfl rfl ArealUCore.ArealUK.chunk_12612 s13
  have s11 : leavesOK ctxLitU 255306250000 1 ((leaves.drop 25222).take 178) 514600000000 2 = true :=
    take_step (n := 2) (t := 178) (b := 25224) rfl rfl ArealUCore.ArealUK.chunk_12611 s12
  have s10 : leavesOK ctxLitU 127643750000 0 ((leaves.drop 25220).take 180) 514600000000 2 = true :=
    take_step (n := 2) (t := 180) (b := 25222) rfl rfl ArealUCore.ArealUK.chunk_12610 s11
  have s9 : leavesOK ctxLitU 127631250000 0 ((leaves.drop 25218).take 182) 514600000000 2 = true :=
    take_step (n := 2) (t := 182) (b := 25220) rfl rfl ArealUCore.ArealUK.chunk_12609 s10
  have s8 : leavesOK ctxLitU 255237500000 1 ((leaves.drop 25216).take 184) 514600000000 2 = true :=
    take_step (n := 2) (t := 184) (b := 25218) rfl rfl ArealUCore.ArealUK.chunk_12608 s9
  have s7 : leavesOK ctxLitU 255212500000 1 ((leaves.drop 25214).take 186) 514600000000 2 = true :=
    take_step (n := 2) (t := 186) (b := 25216) rfl rfl ArealUCore.ArealUK.chunk_12607 s8
  have s6 : leavesOK ctxLitU 510375000000 2 ((leaves.drop 25212).take 188) 514600000000 2 = true :=
    take_step (n := 2) (t := 188) (b := 25214) rfl rfl ArealUCore.ArealUK.chunk_12606 s7
  have s5 : leavesOK ctxLitU 510325000000 2 ((leaves.drop 25210).take 190) 514600000000 2 = true :=
    take_step (n := 2) (t := 190) (b := 25212) rfl rfl ArealUCore.ArealUK.chunk_12605 s6
  have s4 : leavesOK ctxLitU 510275000000 2 ((leaves.drop 25208).take 192) 514600000000 2 = true :=
    take_step (n := 2) (t := 192) (b := 25210) rfl rfl ArealUCore.ArealUK.chunk_12604 s5
  have s3 : leavesOK ctxLitU 510225000000 2 ((leaves.drop 25206).take 194) 514600000000 2 = true :=
    take_step (n := 2) (t := 194) (b := 25208) rfl rfl ArealUCore.ArealUK.chunk_12603 s4
  have s2 : leavesOK ctxLitU 510175000000 2 ((leaves.drop 25204).take 196) 514600000000 2 = true :=
    take_step (n := 2) (t := 196) (b := 25206) rfl rfl ArealUCore.ArealUK.chunk_12602 s3
  have s1 : leavesOK ctxLitU 510125000000 2 ((leaves.drop 25202).take 198) 514600000000 2 = true :=
    take_step (n := 2) (t := 198) (b := 25204) rfl rfl ArealUCore.ArealUK.chunk_12601 s2
  have s0 : leavesOK ctxLitU 510075000000 2 ((leaves.drop 25200).take 200) 514600000000 2 = true :=
    take_step (n := 2) (t := 200) (b := 25202) rfl rfl ArealUCore.ArealUK.chunk_12600 s1
  exact s0

end Areal.UCert

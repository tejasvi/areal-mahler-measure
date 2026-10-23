import ArealUK.Chunk13600
import ArealUK.Chunk13601
import ArealUK.Chunk13602
import ArealUK.Chunk13603
import ArealUK.Chunk13604
import ArealUK.Chunk13605
import ArealUK.Chunk13606
import ArealUK.Chunk13607
import ArealUK.Chunk13608
import ArealUK.Chunk13609
import ArealUK.Chunk13610
import ArealUK.Chunk13611
import ArealUK.Chunk13612
import ArealUK.Chunk13613
import ArealUK.Chunk13614
import ArealUK.Chunk13615
import ArealUK.Chunk13616
import ArealUK.Chunk13617
import ArealUK.Chunk13618
import ArealUK.Chunk13619
import ArealUK.Chunk13620
import ArealUK.Chunk13621
import ArealUK.Chunk13622
import ArealUK.Chunk13623
import ArealUK.Chunk13624
import ArealUK.Chunk13625
import ArealUK.Chunk13626
import ArealUK.Chunk13627
import ArealUK.Chunk13628
import ArealUK.Chunk13629
import ArealUK.Chunk13630
import ArealUK.Chunk13631
import ArealUK.Chunk13632
import ArealUK.Chunk13633
import ArealUK.Chunk13634
import ArealUK.Chunk13635
import ArealUK.Chunk13636
import ArealUK.Chunk13637
import ArealUK.Chunk13638
import ArealUK.Chunk13639
import ArealUK.Chunk13640
import ArealUK.Chunk13641
import ArealUK.Chunk13642
import ArealUK.Chunk13643
import ArealUK.Chunk13644
import ArealUK.Chunk13645
import ArealUK.Chunk13646
import ArealUK.Chunk13647
import ArealUK.Chunk13648
import ArealUK.Chunk13649
import ArealUK.Chunk13650
import ArealUK.Chunk13651
import ArealUK.Chunk13652
import ArealUK.Chunk13653
import ArealUK.Chunk13654
import ArealUK.Chunk13655
import ArealUK.Chunk13656
import ArealUK.Chunk13657
import ArealUK.Chunk13658
import ArealUK.Chunk13659
import ArealUK.Chunk13660
import ArealUK.Chunk13661
import ArealUK.Chunk13662
import ArealUK.Chunk13663
import ArealUK.Chunk13664
import ArealUK.Chunk13665
import ArealUK.Chunk13666
import ArealUK.Chunk13667
import ArealUK.Chunk13668
import ArealUK.Chunk13669
import ArealUK.Chunk13670
import ArealUK.Chunk13671
import ArealUK.Chunk13672
import ArealUK.Chunk13673
import ArealUK.Chunk13674
import ArealUK.Chunk13675
import ArealUK.Chunk13676
import ArealUK.Chunk13677
import ArealUK.Chunk13678
import ArealUK.Chunk13679
import ArealUK.Chunk13680
import ArealUK.Chunk13681
import ArealUK.Chunk13682
import ArealUK.Chunk13683
import ArealUK.Chunk13684
import ArealUK.Chunk13685
import ArealUK.Chunk13686
import ArealUK.Chunk13687
import ArealUK.Chunk13688
import ArealUK.Chunk13689
import ArealUK.Chunk13690
import ArealUK.Chunk13691
import ArealUK.Chunk13692
import ArealUK.Chunk13693
import ArealUK.Chunk13694
import ArealUK.Chunk13695
import ArealUK.Chunk13696
import ArealUK.Chunk13697
import ArealUK.Chunk13698
import ArealUK.Chunk13699
import Areal.UCert.LeavesKGen

/-! Group 136 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_136 : leavesOK ctxLitU 278262500000 1 ((leaves.drop 27200).take 200) 140325000000 0 = true := by
  have s99 := ArealUCore.ArealUK.chunk_13699
  have s98 : leavesOK ctxLitU 280600000000 1 ((leaves.drop 27396).take 4) 140325000000 0 = true :=
    take_step (n := 2) (t := 4) (b := 27398) rfl rfl ArealUCore.ArealUK.chunk_13698 s99
  have s97 : leavesOK ctxLitU 280575000000 1 ((leaves.drop 27394).take 6) 140325000000 0 = true :=
    take_step (n := 2) (t := 6) (b := 27396) rfl rfl ArealUCore.ArealUK.chunk_13697 s98
  have s96 : leavesOK ctxLitU 280550000000 1 ((leaves.drop 27392).take 8) 140325000000 0 = true :=
    take_step (n := 2) (t := 8) (b := 27394) rfl rfl ArealUCore.ArealUK.chunk_13696 s97
  have s95 : leavesOK ctxLitU 140262500000 0 ((leaves.drop 27390).take 10) 140325000000 0 = true :=
    take_step (n := 2) (t := 10) (b := 27392) rfl rfl ArealUCore.ArealUK.chunk_13695 s96
  have s94 : leavesOK ctxLitU 140250000000 0 ((leaves.drop 27388).take 12) 140325000000 0 = true :=
    take_step (n := 2) (t := 12) (b := 27390) rfl rfl ArealUCore.ArealUK.chunk_13694 s95
  have s93 : leavesOK ctxLitU 140237500000 0 ((leaves.drop 27386).take 14) 140325000000 0 = true :=
    take_step (n := 2) (t := 14) (b := 27388) rfl rfl ArealUCore.ArealUK.chunk_13693 s94
  have s92 : leavesOK ctxLitU 280456250000 1 ((leaves.drop 27384).take 16) 140325000000 0 = true :=
    take_step (n := 2) (t := 16) (b := 27386) rfl rfl ArealUCore.ArealUK.chunk_13692 s93
  have s91 : leavesOK ctxLitU 280437500000 1 ((leaves.drop 27382).take 18) 140325000000 0 = true :=
    take_step (n := 2) (t := 18) (b := 27384) rfl rfl ArealUCore.ArealUK.chunk_13691 s92
  have s90 : leavesOK ctxLitU 280412500000 1 ((leaves.drop 27380).take 20) 140325000000 0 = true :=
    take_step (n := 2) (t := 20) (b := 27382) rfl rfl ArealUCore.ArealUK.chunk_13690 s91
  have s89 : leavesOK ctxLitU 280387500000 1 ((leaves.drop 27378).take 22) 140325000000 0 = true :=
    take_step (n := 2) (t := 22) (b := 27380) rfl rfl ArealUCore.ArealUK.chunk_13689 s90
  have s88 : leavesOK ctxLitU 280362500000 1 ((leaves.drop 27376).take 24) 140325000000 0 = true :=
    take_step (n := 2) (t := 24) (b := 27378) rfl rfl ArealUCore.ArealUK.chunk_13688 s89
  have s87 : leavesOK ctxLitU 140168750000 0 ((leaves.drop 27374).take 26) 140325000000 0 = true :=
    take_step (n := 2) (t := 26) (b := 27376) rfl rfl ArealUCore.ArealUK.chunk_13687 s88
  have s86 : leavesOK ctxLitU 140156250000 0 ((leaves.drop 27372).take 28) 140325000000 0 = true :=
    take_step (n := 2) (t := 28) (b := 27374) rfl rfl ArealUCore.ArealUK.chunk_13686 s87
  have s85 : leavesOK ctxLitU 280287500000 1 ((leaves.drop 27370).take 30) 140325000000 0 = true :=
    take_step (n := 2) (t := 30) (b := 27372) rfl rfl ArealUCore.ArealUK.chunk_13685 s86
  have s84 : leavesOK ctxLitU 280262500000 1 ((leaves.drop 27368).take 32) 140325000000 0 = true :=
    take_step (n := 2) (t := 32) (b := 27370) rfl rfl ArealUCore.ArealUK.chunk_13684 s85
  have s83 : leavesOK ctxLitU 560475000000 2 ((leaves.drop 27366).take 34) 140325000000 0 = true :=
    take_step (n := 2) (t := 34) (b := 27368) rfl rfl ArealUCore.ArealUK.chunk_13683 s84
  have s82 : leavesOK ctxLitU 560425000000 2 ((leaves.drop 27364).take 36) 140325000000 0 = true :=
    take_step (n := 2) (t := 36) (b := 27366) rfl rfl ArealUCore.ArealUK.chunk_13682 s83
  have s81 : leavesOK ctxLitU 280187500000 1 ((leaves.drop 27362).take 38) 140325000000 0 = true :=
    take_step (n := 2) (t := 38) (b := 27364) rfl rfl ArealUCore.ArealUK.chunk_13681 s82
  have s80 : leavesOK ctxLitU 280162500000 1 ((leaves.drop 27360).take 40) 140325000000 0 = true :=
    take_step (n := 2) (t := 40) (b := 27362) rfl rfl ArealUCore.ArealUK.chunk_13680 s81
  have s79 : leavesOK ctxLitU 280143750000 1 ((leaves.drop 27358).take 42) 140325000000 0 = true :=
    take_step (n := 2) (t := 42) (b := 27360) rfl rfl ArealUCore.ArealUK.chunk_13679 s80
  have s78 : leavesOK ctxLitU 280131250000 1 ((leaves.drop 27356).take 44) 140325000000 0 = true :=
    take_step (n := 2) (t := 44) (b := 27358) rfl rfl ArealUCore.ArealUK.chunk_13678 s79
  have s77 : leavesOK ctxLitU 140056250000 0 ((leaves.drop 27354).take 46) 140325000000 0 = true :=
    take_step (n := 2) (t := 46) (b := 27356) rfl rfl ArealUCore.ArealUK.chunk_13677 s78
  have s76 : leavesOK ctxLitU 140043750000 0 ((leaves.drop 27352).take 48) 140325000000 0 = true :=
    take_step (n := 2) (t := 48) (b := 27354) rfl rfl ArealUCore.ArealUK.chunk_13676 s77
  have s75 : leavesOK ctxLitU 140031250000 0 ((leaves.drop 27350).take 50) 140325000000 0 = true :=
    take_step (n := 2) (t := 50) (b := 27352) rfl rfl ArealUCore.ArealUK.chunk_13675 s76
  have s74 : leavesOK ctxLitU 280037500000 1 ((leaves.drop 27348).take 52) 140325000000 0 = true :=
    take_step (n := 2) (t := 52) (b := 27350) rfl rfl ArealUCore.ArealUK.chunk_13674 s75
  have s73 : leavesOK ctxLitU 280012500000 1 ((leaves.drop 27346).take 54) 140325000000 0 = true :=
    take_step (n := 2) (t := 54) (b := 27348) rfl rfl ArealUCore.ArealUK.chunk_13673 s74
  have s72 : leavesOK ctxLitU 559975000000 2 ((leaves.drop 27344).take 56) 140325000000 0 = true :=
    take_step (n := 2) (t := 56) (b := 27346) rfl rfl ArealUCore.ArealUK.chunk_13672 s73
  have s71 : leavesOK ctxLitU 559925000000 2 ((leaves.drop 27342).take 58) 140325000000 0 = true :=
    take_step (n := 2) (t := 58) (b := 27344) rfl rfl ArealUCore.ArealUK.chunk_13671 s72
  have s70 : leavesOK ctxLitU 559875000000 2 ((leaves.drop 27340).take 60) 140325000000 0 = true :=
    take_step (n := 2) (t := 60) (b := 27342) rfl rfl ArealUCore.ArealUK.chunk_13670 s71
  have s69 : leavesOK ctxLitU 559825000000 2 ((leaves.drop 27338).take 62) 140325000000 0 = true :=
    take_step (n := 2) (t := 62) (b := 27340) rfl rfl ArealUCore.ArealUK.chunk_13669 s70
  have s68 : leavesOK ctxLitU 559775000000 2 ((leaves.drop 27336).take 64) 140325000000 0 = true :=
    take_step (n := 2) (t := 64) (b := 27338) rfl rfl ArealUCore.ArealUK.chunk_13668 s69
  have s67 : leavesOK ctxLitU 559725000000 2 ((leaves.drop 27334).take 66) 140325000000 0 = true :=
    take_step (n := 2) (t := 66) (b := 27336) rfl rfl ArealUCore.ArealUK.chunk_13667 s68
  have s66 : leavesOK ctxLitU 559675000000 2 ((leaves.drop 27332).take 68) 140325000000 0 = true :=
    take_step (n := 2) (t := 68) (b := 27334) rfl rfl ArealUCore.ArealUK.chunk_13666 s67
  have s65 : leavesOK ctxLitU 559625000000 2 ((leaves.drop 27330).take 70) 140325000000 0 = true :=
    take_step (n := 2) (t := 70) (b := 27332) rfl rfl ArealUCore.ArealUK.chunk_13665 s66
  have s64 : leavesOK ctxLitU 559575000000 2 ((leaves.drop 27328).take 72) 140325000000 0 = true :=
    take_step (n := 2) (t := 72) (b := 27330) rfl rfl ArealUCore.ArealUK.chunk_13664 s65
  have s63 : leavesOK ctxLitU 559525000000 2 ((leaves.drop 27326).take 74) 140325000000 0 = true :=
    take_step (n := 2) (t := 74) (b := 27328) rfl rfl ArealUCore.ArealUK.chunk_13663 s64
  have s62 : leavesOK ctxLitU 559475000000 2 ((leaves.drop 27324).take 76) 140325000000 0 = true :=
    take_step (n := 2) (t := 76) (b := 27326) rfl rfl ArealUCore.ArealUK.chunk_13662 s63
  have s61 : leavesOK ctxLitU 559425000000 2 ((leaves.drop 27322).take 78) 140325000000 0 = true :=
    take_step (n := 2) (t := 78) (b := 27324) rfl rfl ArealUCore.ArealUK.chunk_13661 s62
  have s60 : leavesOK ctxLitU 559375000000 2 ((leaves.drop 27320).take 80) 140325000000 0 = true :=
    take_step (n := 2) (t := 80) (b := 27322) rfl rfl ArealUCore.ArealUK.chunk_13660 s61
  have s59 : leavesOK ctxLitU 559325000000 2 ((leaves.drop 27318).take 82) 140325000000 0 = true :=
    take_step (n := 2) (t := 82) (b := 27320) rfl rfl ArealUCore.ArealUK.chunk_13659 s60
  have s58 : leavesOK ctxLitU 559275000000 2 ((leaves.drop 27316).take 84) 140325000000 0 = true :=
    take_step (n := 2) (t := 84) (b := 27318) rfl rfl ArealUCore.ArealUK.chunk_13658 s59
  have s57 : leavesOK ctxLitU 559225000000 2 ((leaves.drop 27314).take 86) 140325000000 0 = true :=
    take_step (n := 2) (t := 86) (b := 27316) rfl rfl ArealUCore.ArealUK.chunk_13657 s58
  have s56 : leavesOK ctxLitU 279587500000 1 ((leaves.drop 27312).take 88) 140325000000 0 = true :=
    take_step (n := 2) (t := 88) (b := 27314) rfl rfl ArealUCore.ArealUK.chunk_13656 s57
  have s55 : leavesOK ctxLitU 279562500000 1 ((leaves.drop 27310).take 90) 140325000000 0 = true :=
    take_step (n := 2) (t := 90) (b := 27312) rfl rfl ArealUCore.ArealUK.chunk_13655 s56
  have s54 : leavesOK ctxLitU 139768750000 0 ((leaves.drop 27308).take 92) 140325000000 0 = true :=
    take_step (n := 2) (t := 92) (b := 27310) rfl rfl ArealUCore.ArealUK.chunk_13654 s55
  have s53 : leavesOK ctxLitU 139756250000 0 ((leaves.drop 27306).take 94) 140325000000 0 = true :=
    take_step (n := 2) (t := 94) (b := 27308) rfl rfl ArealUCore.ArealUK.chunk_13653 s54
  have s52 : leavesOK ctxLitU 139743750000 0 ((leaves.drop 27304).take 96) 140325000000 0 = true :=
    take_step (n := 2) (t := 96) (b := 27306) rfl rfl ArealUCore.ArealUK.chunk_13652 s53
  have s51 : leavesOK ctxLitU 139731250000 0 ((leaves.drop 27302).take 98) 140325000000 0 = true :=
    take_step (n := 2) (t := 98) (b := 27304) rfl rfl ArealUCore.ArealUK.chunk_13651 s52
  have s50 : leavesOK ctxLitU 279437500000 1 ((leaves.drop 27300).take 100) 140325000000 0 = true :=
    take_step (n := 2) (t := 100) (b := 27302) rfl rfl ArealUCore.ArealUK.chunk_13650 s51
  have s49 : leavesOK ctxLitU 279412500000 1 ((leaves.drop 27298).take 102) 140325000000 0 = true :=
    take_step (n := 2) (t := 102) (b := 27300) rfl rfl ArealUCore.ArealUK.chunk_13649 s50
  have s48 : leavesOK ctxLitU 558775000000 2 ((leaves.drop 27296).take 104) 140325000000 0 = true :=
    take_step (n := 2) (t := 104) (b := 27298) rfl rfl ArealUCore.ArealUK.chunk_13648 s49
  have s47 : leavesOK ctxLitU 558725000000 2 ((leaves.drop 27294).take 106) 140325000000 0 = true :=
    take_step (n := 2) (t := 106) (b := 27296) rfl rfl ArealUCore.ArealUK.chunk_13647 s48
  have s46 : leavesOK ctxLitU 558675000000 2 ((leaves.drop 27292).take 108) 140325000000 0 = true :=
    take_step (n := 2) (t := 108) (b := 27294) rfl rfl ArealUCore.ArealUK.chunk_13646 s47
  have s45 : leavesOK ctxLitU 558625000000 2 ((leaves.drop 27290).take 110) 140325000000 0 = true :=
    take_step (n := 2) (t := 110) (b := 27292) rfl rfl ArealUCore.ArealUK.chunk_13645 s46
  have s44 : leavesOK ctxLitU 558575000000 2 ((leaves.drop 27288).take 112) 140325000000 0 = true :=
    take_step (n := 2) (t := 112) (b := 27290) rfl rfl ArealUCore.ArealUK.chunk_13644 s45
  have s43 : leavesOK ctxLitU 558525000000 2 ((leaves.drop 27286).take 114) 140325000000 0 = true :=
    take_step (n := 2) (t := 114) (b := 27288) rfl rfl ArealUCore.ArealUK.chunk_13643 s44
  have s42 : leavesOK ctxLitU 558475000000 2 ((leaves.drop 27284).take 116) 140325000000 0 = true :=
    take_step (n := 2) (t := 116) (b := 27286) rfl rfl ArealUCore.ArealUK.chunk_13642 s43
  have s41 : leavesOK ctxLitU 558425000000 2 ((leaves.drop 27282).take 118) 140325000000 0 = true :=
    take_step (n := 2) (t := 118) (b := 27284) rfl rfl ArealUCore.ArealUK.chunk_13641 s42
  have s40 : leavesOK ctxLitU 279187500000 1 ((leaves.drop 27280).take 120) 140325000000 0 = true :=
    take_step (n := 2) (t := 120) (b := 27282) rfl rfl ArealUCore.ArealUK.chunk_13640 s41
  have s39 : leavesOK ctxLitU 279162500000 1 ((leaves.drop 27278).take 122) 140325000000 0 = true :=
    take_step (n := 2) (t := 122) (b := 27280) rfl rfl ArealUCore.ArealUK.chunk_13639 s40
  have s38 : leavesOK ctxLitU 279143750000 1 ((leaves.drop 27276).take 124) 140325000000 0 = true :=
    take_step (n := 2) (t := 124) (b := 27278) rfl rfl ArealUCore.ArealUK.chunk_13638 s39
  have s37 : leavesOK ctxLitU 279131250000 1 ((leaves.drop 27274).take 126) 140325000000 0 = true :=
    take_step (n := 2) (t := 126) (b := 27276) rfl rfl ArealUCore.ArealUK.chunk_13637 s38
  have s36 : leavesOK ctxLitU 139556250000 0 ((leaves.drop 27272).take 128) 140325000000 0 = true :=
    take_step (n := 2) (t := 128) (b := 27274) rfl rfl ArealUCore.ArealUK.chunk_13636 s37
  have s35 : leavesOK ctxLitU 279087500000 1 ((leaves.drop 27270).take 130) 140325000000 0 = true :=
    take_step (n := 2) (t := 130) (b := 27272) rfl rfl ArealUCore.ArealUK.chunk_13635 s36
  have s34 : leavesOK ctxLitU 279062500000 1 ((leaves.drop 27268).take 132) 140325000000 0 = true :=
    take_step (n := 2) (t := 132) (b := 27270) rfl rfl ArealUCore.ArealUK.chunk_13634 s35
  have s33 : leavesOK ctxLitU 558075000000 2 ((leaves.drop 27266).take 134) 140325000000 0 = true :=
    take_step (n := 2) (t := 134) (b := 27268) rfl rfl ArealUCore.ArealUK.chunk_13633 s34
  have s32 : leavesOK ctxLitU 558025000000 2 ((leaves.drop 27264).take 136) 140325000000 0 = true :=
    take_step (n := 2) (t := 136) (b := 27266) rfl rfl ArealUCore.ArealUK.chunk_13632 s33
  have s31 : leavesOK ctxLitU 557975000000 2 ((leaves.drop 27262).take 138) 140325000000 0 = true :=
    take_step (n := 2) (t := 138) (b := 27264) rfl rfl ArealUCore.ArealUK.chunk_13631 s32
  have s30 : leavesOK ctxLitU 557925000000 2 ((leaves.drop 27260).take 140) 140325000000 0 = true :=
    take_step (n := 2) (t := 140) (b := 27262) rfl rfl ArealUCore.ArealUK.chunk_13630 s31
  have s29 : leavesOK ctxLitU 278937500000 1 ((leaves.drop 27258).take 142) 140325000000 0 = true :=
    take_step (n := 2) (t := 142) (b := 27260) rfl rfl ArealUCore.ArealUK.chunk_13629 s30
  have s28 : leavesOK ctxLitU 278912500000 1 ((leaves.drop 27256).take 144) 140325000000 0 = true :=
    take_step (n := 2) (t := 144) (b := 27258) rfl rfl ArealUCore.ArealUK.chunk_13628 s29
  have s27 : leavesOK ctxLitU 139443750000 0 ((leaves.drop 27254).take 146) 140325000000 0 = true :=
    take_step (n := 2) (t := 146) (b := 27256) rfl rfl ArealUCore.ArealUK.chunk_13627 s28
  have s26 : leavesOK ctxLitU 278868750000 1 ((leaves.drop 27252).take 148) 140325000000 0 = true :=
    take_step (n := 2) (t := 148) (b := 27254) rfl rfl ArealUCore.ArealUK.chunk_13626 s27
  have s25 : leavesOK ctxLitU 278856250000 1 ((leaves.drop 27250).take 150) 140325000000 0 = true :=
    take_step (n := 2) (t := 150) (b := 27252) rfl rfl ArealUCore.ArealUK.chunk_13625 s26
  have s24 : leavesOK ctxLitU 278837500000 1 ((leaves.drop 27248).take 152) 140325000000 0 = true :=
    take_step (n := 2) (t := 152) (b := 27250) rfl rfl ArealUCore.ArealUK.chunk_13624 s25
  have s23 : leavesOK ctxLitU 278812500000 1 ((leaves.drop 27246).take 154) 140325000000 0 = true :=
    take_step (n := 2) (t := 154) (b := 27248) rfl rfl ArealUCore.ArealUK.chunk_13623 s24
  have s22 : leavesOK ctxLitU 278787500000 1 ((leaves.drop 27244).take 156) 140325000000 0 = true :=
    take_step (n := 2) (t := 156) (b := 27246) rfl rfl ArealUCore.ArealUK.chunk_13622 s23
  have s21 : leavesOK ctxLitU 278762500000 1 ((leaves.drop 27242).take 158) 140325000000 0 = true :=
    take_step (n := 2) (t := 158) (b := 27244) rfl rfl ArealUCore.ArealUK.chunk_13621 s22
  have s20 : leavesOK ctxLitU 278743750000 1 ((leaves.drop 27240).take 160) 140325000000 0 = true :=
    take_step (n := 2) (t := 160) (b := 27242) rfl rfl ArealUCore.ArealUK.chunk_13620 s21
  have s19 : leavesOK ctxLitU 139362500000 0 ((leaves.drop 27238).take 162) 140325000000 0 = true :=
    take_step (n := 2) (t := 162) (b := 27240) rfl rfl ArealUCore.ArealUK.chunk_13619 s20
  have s18 : leavesOK ctxLitU 139350000000 0 ((leaves.drop 27236).take 164) 140325000000 0 = true :=
    take_step (n := 2) (t := 164) (b := 27238) rfl rfl ArealUCore.ArealUK.chunk_13618 s19
  have s17 : leavesOK ctxLitU 139337500000 0 ((leaves.drop 27234).take 166) 140325000000 0 = true :=
    take_step (n := 2) (t := 166) (b := 27236) rfl rfl ArealUCore.ArealUK.chunk_13617 s18
  have s16 : leavesOK ctxLitU 139325000000 0 ((leaves.drop 27232).take 168) 140325000000 0 = true :=
    take_step (n := 2) (t := 168) (b := 27234) rfl rfl ArealUCore.ArealUK.chunk_13616 s17
  have s15 : leavesOK ctxLitU 278625000000 1 ((leaves.drop 27230).take 170) 140325000000 0 = true :=
    take_step (n := 2) (t := 170) (b := 27232) rfl rfl ArealUCore.ArealUK.chunk_13615 s16
  have s14 : leavesOK ctxLitU 278600000000 1 ((leaves.drop 27228).take 172) 140325000000 0 = true :=
    take_step (n := 2) (t := 172) (b := 27230) rfl rfl ArealUCore.ArealUK.chunk_13614 s15
  have s13 : leavesOK ctxLitU 278575000000 1 ((leaves.drop 27226).take 174) 140325000000 0 = true :=
    take_step (n := 2) (t := 174) (b := 27228) rfl rfl ArealUCore.ArealUK.chunk_13613 s14
  have s12 : leavesOK ctxLitU 278550000000 1 ((leaves.drop 27224).take 176) 140325000000 0 = true :=
    take_step (n := 2) (t := 176) (b := 27226) rfl rfl ArealUCore.ArealUK.chunk_13612 s13
  have s11 : leavesOK ctxLitU 139262500000 0 ((leaves.drop 27222).take 178) 140325000000 0 = true :=
    take_step (n := 2) (t := 178) (b := 27224) rfl rfl ArealUCore.ArealUK.chunk_13611 s12
  have s10 : leavesOK ctxLitU 139250000000 0 ((leaves.drop 27220).take 180) 140325000000 0 = true :=
    take_step (n := 2) (t := 180) (b := 27222) rfl rfl ArealUCore.ArealUK.chunk_13610 s11
  have s9 : leavesOK ctxLitU 139237500000 0 ((leaves.drop 27218).take 182) 140325000000 0 = true :=
    take_step (n := 2) (t := 182) (b := 27220) rfl rfl ArealUCore.ArealUK.chunk_13609 s10
  have s8 : leavesOK ctxLitU 278456250000 1 ((leaves.drop 27216).take 184) 140325000000 0 = true :=
    take_step (n := 2) (t := 184) (b := 27218) rfl rfl ArealUCore.ArealUK.chunk_13608 s9
  have s7 : leavesOK ctxLitU 278437500000 1 ((leaves.drop 27214).take 186) 140325000000 0 = true :=
    take_step (n := 2) (t := 186) (b := 27216) rfl rfl ArealUCore.ArealUK.chunk_13607 s8
  have s6 : leavesOK ctxLitU 278412500000 1 ((leaves.drop 27212).take 188) 140325000000 0 = true :=
    take_step (n := 2) (t := 188) (b := 27214) rfl rfl ArealUCore.ArealUK.chunk_13606 s7
  have s5 : leavesOK ctxLitU 278387500000 1 ((leaves.drop 27210).take 190) 140325000000 0 = true :=
    take_step (n := 2) (t := 190) (b := 27212) rfl rfl ArealUCore.ArealUK.chunk_13605 s6
  have s4 : leavesOK ctxLitU 278362500000 1 ((leaves.drop 27208).take 192) 140325000000 0 = true :=
    take_step (n := 2) (t := 192) (b := 27210) rfl rfl ArealUCore.ArealUK.chunk_13604 s5
  have s3 : leavesOK ctxLitU 139168750000 0 ((leaves.drop 27206).take 194) 140325000000 0 = true :=
    take_step (n := 2) (t := 194) (b := 27208) rfl rfl ArealUCore.ArealUK.chunk_13603 s4
  have s2 : leavesOK ctxLitU 139156250000 0 ((leaves.drop 27204).take 196) 140325000000 0 = true :=
    take_step (n := 2) (t := 196) (b := 27206) rfl rfl ArealUCore.ArealUK.chunk_13602 s3
  have s1 : leavesOK ctxLitU 278287500000 1 ((leaves.drop 27202).take 198) 140325000000 0 = true :=
    take_step (n := 2) (t := 198) (b := 27204) rfl rfl ArealUCore.ArealUK.chunk_13601 s2
  have s0 : leavesOK ctxLitU 278262500000 1 ((leaves.drop 27200).take 200) 140325000000 0 = true :=
    take_step (n := 2) (t := 200) (b := 27202) rfl rfl ArealUCore.ArealUK.chunk_13600 s1
  exact s0

end Areal.UCert

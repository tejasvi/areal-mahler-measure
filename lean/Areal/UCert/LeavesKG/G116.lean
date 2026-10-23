import ArealUK.Chunk11600
import ArealUK.Chunk11601
import ArealUK.Chunk11602
import ArealUK.Chunk11603
import ArealUK.Chunk11604
import ArealUK.Chunk11605
import ArealUK.Chunk11606
import ArealUK.Chunk11607
import ArealUK.Chunk11608
import ArealUK.Chunk11609
import ArealUK.Chunk11610
import ArealUK.Chunk11611
import ArealUK.Chunk11612
import ArealUK.Chunk11613
import ArealUK.Chunk11614
import ArealUK.Chunk11615
import ArealUK.Chunk11616
import ArealUK.Chunk11617
import ArealUK.Chunk11618
import ArealUK.Chunk11619
import ArealUK.Chunk11620
import ArealUK.Chunk11621
import ArealUK.Chunk11622
import ArealUK.Chunk11623
import ArealUK.Chunk11624
import ArealUK.Chunk11625
import ArealUK.Chunk11626
import ArealUK.Chunk11627
import ArealUK.Chunk11628
import ArealUK.Chunk11629
import ArealUK.Chunk11630
import ArealUK.Chunk11631
import ArealUK.Chunk11632
import ArealUK.Chunk11633
import ArealUK.Chunk11634
import ArealUK.Chunk11635
import ArealUK.Chunk11636
import ArealUK.Chunk11637
import ArealUK.Chunk11638
import ArealUK.Chunk11639
import ArealUK.Chunk11640
import ArealUK.Chunk11641
import ArealUK.Chunk11642
import ArealUK.Chunk11643
import ArealUK.Chunk11644
import ArealUK.Chunk11645
import ArealUK.Chunk11646
import ArealUK.Chunk11647
import ArealUK.Chunk11648
import ArealUK.Chunk11649
import ArealUK.Chunk11650
import ArealUK.Chunk11651
import ArealUK.Chunk11652
import ArealUK.Chunk11653
import ArealUK.Chunk11654
import ArealUK.Chunk11655
import ArealUK.Chunk11656
import ArealUK.Chunk11657
import ArealUK.Chunk11658
import ArealUK.Chunk11659
import ArealUK.Chunk11660
import ArealUK.Chunk11661
import ArealUK.Chunk11662
import ArealUK.Chunk11663
import ArealUK.Chunk11664
import ArealUK.Chunk11665
import ArealUK.Chunk11666
import ArealUK.Chunk11667
import ArealUK.Chunk11668
import ArealUK.Chunk11669
import ArealUK.Chunk11670
import ArealUK.Chunk11671
import ArealUK.Chunk11672
import ArealUK.Chunk11673
import ArealUK.Chunk11674
import ArealUK.Chunk11675
import ArealUK.Chunk11676
import ArealUK.Chunk11677
import ArealUK.Chunk11678
import ArealUK.Chunk11679
import ArealUK.Chunk11680
import ArealUK.Chunk11681
import ArealUK.Chunk11682
import ArealUK.Chunk11683
import ArealUK.Chunk11684
import ArealUK.Chunk11685
import ArealUK.Chunk11686
import ArealUK.Chunk11687
import ArealUK.Chunk11688
import ArealUK.Chunk11689
import ArealUK.Chunk11690
import ArealUK.Chunk11691
import ArealUK.Chunk11692
import ArealUK.Chunk11693
import ArealUK.Chunk11694
import ArealUK.Chunk11695
import ArealUK.Chunk11696
import ArealUK.Chunk11697
import ArealUK.Chunk11698
import ArealUK.Chunk11699
import Areal.UCert.LeavesKGen

/-! Group 116 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_116 : leavesOK ctxLitU 456750000000 2 ((leaves.drop 23200).take 200) 461750000000 2 = true := by
  have s99 := ArealUCore.ArealUK.chunk_11699
  have s98 : leavesOK ctxLitU 461650000000 2 ((leaves.drop 23396).take 4) 461750000000 2 = true :=
    take_step (n := 2) (t := 4) (b := 23398) rfl rfl ArealUCore.ArealUK.chunk_11698 s99
  have s97 : leavesOK ctxLitU 461600000000 2 ((leaves.drop 23394).take 6) 461750000000 2 = true :=
    take_step (n := 2) (t := 6) (b := 23396) rfl rfl ArealUCore.ArealUK.chunk_11697 s98
  have s96 : leavesOK ctxLitU 461550000000 2 ((leaves.drop 23392).take 8) 461750000000 2 = true :=
    take_step (n := 2) (t := 8) (b := 23394) rfl rfl ArealUCore.ArealUK.chunk_11696 s97
  have s95 : leavesOK ctxLitU 461500000000 2 ((leaves.drop 23390).take 10) 461750000000 2 = true :=
    take_step (n := 2) (t := 10) (b := 23392) rfl rfl ArealUCore.ArealUK.chunk_11695 s96
  have s94 : leavesOK ctxLitU 461450000000 2 ((leaves.drop 23388).take 12) 461750000000 2 = true :=
    take_step (n := 2) (t := 12) (b := 23390) rfl rfl ArealUCore.ArealUK.chunk_11694 s95
  have s93 : leavesOK ctxLitU 461400000000 2 ((leaves.drop 23386).take 14) 461750000000 2 = true :=
    take_step (n := 2) (t := 14) (b := 23388) rfl rfl ArealUCore.ArealUK.chunk_11693 s94
  have s92 : leavesOK ctxLitU 461350000000 2 ((leaves.drop 23384).take 16) 461750000000 2 = true :=
    take_step (n := 2) (t := 16) (b := 23386) rfl rfl ArealUCore.ArealUK.chunk_11692 s93
  have s91 : leavesOK ctxLitU 461300000000 2 ((leaves.drop 23382).take 18) 461750000000 2 = true :=
    take_step (n := 2) (t := 18) (b := 23384) rfl rfl ArealUCore.ArealUK.chunk_11691 s92
  have s90 : leavesOK ctxLitU 461250000000 2 ((leaves.drop 23380).take 20) 461750000000 2 = true :=
    take_step (n := 2) (t := 20) (b := 23382) rfl rfl ArealUCore.ArealUK.chunk_11690 s91
  have s89 : leavesOK ctxLitU 461200000000 2 ((leaves.drop 23378).take 22) 461750000000 2 = true :=
    take_step (n := 2) (t := 22) (b := 23380) rfl rfl ArealUCore.ArealUK.chunk_11689 s90
  have s88 : leavesOK ctxLitU 461150000000 2 ((leaves.drop 23376).take 24) 461750000000 2 = true :=
    take_step (n := 2) (t := 24) (b := 23378) rfl rfl ArealUCore.ArealUK.chunk_11688 s89
  have s87 : leavesOK ctxLitU 461100000000 2 ((leaves.drop 23374).take 26) 461750000000 2 = true :=
    take_step (n := 2) (t := 26) (b := 23376) rfl rfl ArealUCore.ArealUK.chunk_11687 s88
  have s86 : leavesOK ctxLitU 461050000000 2 ((leaves.drop 23372).take 28) 461750000000 2 = true :=
    take_step (n := 2) (t := 28) (b := 23374) rfl rfl ArealUCore.ArealUK.chunk_11686 s87
  have s85 : leavesOK ctxLitU 461000000000 2 ((leaves.drop 23370).take 30) 461750000000 2 = true :=
    take_step (n := 2) (t := 30) (b := 23372) rfl rfl ArealUCore.ArealUK.chunk_11685 s86
  have s84 : leavesOK ctxLitU 460950000000 2 ((leaves.drop 23368).take 32) 461750000000 2 = true :=
    take_step (n := 2) (t := 32) (b := 23370) rfl rfl ArealUCore.ArealUK.chunk_11684 s85
  have s83 : leavesOK ctxLitU 460900000000 2 ((leaves.drop 23366).take 34) 461750000000 2 = true :=
    take_step (n := 2) (t := 34) (b := 23368) rfl rfl ArealUCore.ArealUK.chunk_11683 s84
  have s82 : leavesOK ctxLitU 460850000000 2 ((leaves.drop 23364).take 36) 461750000000 2 = true :=
    take_step (n := 2) (t := 36) (b := 23366) rfl rfl ArealUCore.ArealUK.chunk_11682 s83
  have s81 : leavesOK ctxLitU 460800000000 2 ((leaves.drop 23362).take 38) 461750000000 2 = true :=
    take_step (n := 2) (t := 38) (b := 23364) rfl rfl ArealUCore.ArealUK.chunk_11681 s82
  have s80 : leavesOK ctxLitU 460750000000 2 ((leaves.drop 23360).take 40) 461750000000 2 = true :=
    take_step (n := 2) (t := 40) (b := 23362) rfl rfl ArealUCore.ArealUK.chunk_11680 s81
  have s79 : leavesOK ctxLitU 460700000000 2 ((leaves.drop 23358).take 42) 461750000000 2 = true :=
    take_step (n := 2) (t := 42) (b := 23360) rfl rfl ArealUCore.ArealUK.chunk_11679 s80
  have s78 : leavesOK ctxLitU 460650000000 2 ((leaves.drop 23356).take 44) 461750000000 2 = true :=
    take_step (n := 2) (t := 44) (b := 23358) rfl rfl ArealUCore.ArealUK.chunk_11678 s79
  have s77 : leavesOK ctxLitU 460600000000 2 ((leaves.drop 23354).take 46) 461750000000 2 = true :=
    take_step (n := 2) (t := 46) (b := 23356) rfl rfl ArealUCore.ArealUK.chunk_11677 s78
  have s76 : leavesOK ctxLitU 460550000000 2 ((leaves.drop 23352).take 48) 461750000000 2 = true :=
    take_step (n := 2) (t := 48) (b := 23354) rfl rfl ArealUCore.ArealUK.chunk_11676 s77
  have s75 : leavesOK ctxLitU 460500000000 2 ((leaves.drop 23350).take 50) 461750000000 2 = true :=
    take_step (n := 2) (t := 50) (b := 23352) rfl rfl ArealUCore.ArealUK.chunk_11675 s76
  have s74 : leavesOK ctxLitU 460450000000 2 ((leaves.drop 23348).take 52) 461750000000 2 = true :=
    take_step (n := 2) (t := 52) (b := 23350) rfl rfl ArealUCore.ArealUK.chunk_11674 s75
  have s73 : leavesOK ctxLitU 460400000000 2 ((leaves.drop 23346).take 54) 461750000000 2 = true :=
    take_step (n := 2) (t := 54) (b := 23348) rfl rfl ArealUCore.ArealUK.chunk_11673 s74
  have s72 : leavesOK ctxLitU 460350000000 2 ((leaves.drop 23344).take 56) 461750000000 2 = true :=
    take_step (n := 2) (t := 56) (b := 23346) rfl rfl ArealUCore.ArealUK.chunk_11672 s73
  have s71 : leavesOK ctxLitU 460300000000 2 ((leaves.drop 23342).take 58) 461750000000 2 = true :=
    take_step (n := 2) (t := 58) (b := 23344) rfl rfl ArealUCore.ArealUK.chunk_11671 s72
  have s70 : leavesOK ctxLitU 460250000000 2 ((leaves.drop 23340).take 60) 461750000000 2 = true :=
    take_step (n := 2) (t := 60) (b := 23342) rfl rfl ArealUCore.ArealUK.chunk_11670 s71
  have s69 : leavesOK ctxLitU 460200000000 2 ((leaves.drop 23338).take 62) 461750000000 2 = true :=
    take_step (n := 2) (t := 62) (b := 23340) rfl rfl ArealUCore.ArealUK.chunk_11669 s70
  have s68 : leavesOK ctxLitU 460150000000 2 ((leaves.drop 23336).take 64) 461750000000 2 = true :=
    take_step (n := 2) (t := 64) (b := 23338) rfl rfl ArealUCore.ArealUK.chunk_11668 s69
  have s67 : leavesOK ctxLitU 460100000000 2 ((leaves.drop 23334).take 66) 461750000000 2 = true :=
    take_step (n := 2) (t := 66) (b := 23336) rfl rfl ArealUCore.ArealUK.chunk_11667 s68
  have s66 : leavesOK ctxLitU 460050000000 2 ((leaves.drop 23332).take 68) 461750000000 2 = true :=
    take_step (n := 2) (t := 68) (b := 23334) rfl rfl ArealUCore.ArealUK.chunk_11666 s67
  have s65 : leavesOK ctxLitU 460000000000 2 ((leaves.drop 23330).take 70) 461750000000 2 = true :=
    take_step (n := 2) (t := 70) (b := 23332) rfl rfl ArealUCore.ArealUK.chunk_11665 s66
  have s64 : leavesOK ctxLitU 459950000000 2 ((leaves.drop 23328).take 72) 461750000000 2 = true :=
    take_step (n := 2) (t := 72) (b := 23330) rfl rfl ArealUCore.ArealUK.chunk_11664 s65
  have s63 : leavesOK ctxLitU 459900000000 2 ((leaves.drop 23326).take 74) 461750000000 2 = true :=
    take_step (n := 2) (t := 74) (b := 23328) rfl rfl ArealUCore.ArealUK.chunk_11663 s64
  have s62 : leavesOK ctxLitU 459850000000 2 ((leaves.drop 23324).take 76) 461750000000 2 = true :=
    take_step (n := 2) (t := 76) (b := 23326) rfl rfl ArealUCore.ArealUK.chunk_11662 s63
  have s61 : leavesOK ctxLitU 459800000000 2 ((leaves.drop 23322).take 78) 461750000000 2 = true :=
    take_step (n := 2) (t := 78) (b := 23324) rfl rfl ArealUCore.ArealUK.chunk_11661 s62
  have s60 : leavesOK ctxLitU 459750000000 2 ((leaves.drop 23320).take 80) 461750000000 2 = true :=
    take_step (n := 2) (t := 80) (b := 23322) rfl rfl ArealUCore.ArealUK.chunk_11660 s61
  have s59 : leavesOK ctxLitU 459700000000 2 ((leaves.drop 23318).take 82) 461750000000 2 = true :=
    take_step (n := 2) (t := 82) (b := 23320) rfl rfl ArealUCore.ArealUK.chunk_11659 s60
  have s58 : leavesOK ctxLitU 459650000000 2 ((leaves.drop 23316).take 84) 461750000000 2 = true :=
    take_step (n := 2) (t := 84) (b := 23318) rfl rfl ArealUCore.ArealUK.chunk_11658 s59
  have s57 : leavesOK ctxLitU 459600000000 2 ((leaves.drop 23314).take 86) 461750000000 2 = true :=
    take_step (n := 2) (t := 86) (b := 23316) rfl rfl ArealUCore.ArealUK.chunk_11657 s58
  have s56 : leavesOK ctxLitU 459550000000 2 ((leaves.drop 23312).take 88) 461750000000 2 = true :=
    take_step (n := 2) (t := 88) (b := 23314) rfl rfl ArealUCore.ArealUK.chunk_11656 s57
  have s55 : leavesOK ctxLitU 459500000000 2 ((leaves.drop 23310).take 90) 461750000000 2 = true :=
    take_step (n := 2) (t := 90) (b := 23312) rfl rfl ArealUCore.ArealUK.chunk_11655 s56
  have s54 : leavesOK ctxLitU 459450000000 2 ((leaves.drop 23308).take 92) 461750000000 2 = true :=
    take_step (n := 2) (t := 92) (b := 23310) rfl rfl ArealUCore.ArealUK.chunk_11654 s55
  have s53 : leavesOK ctxLitU 459400000000 2 ((leaves.drop 23306).take 94) 461750000000 2 = true :=
    take_step (n := 2) (t := 94) (b := 23308) rfl rfl ArealUCore.ArealUK.chunk_11653 s54
  have s52 : leavesOK ctxLitU 459350000000 2 ((leaves.drop 23304).take 96) 461750000000 2 = true :=
    take_step (n := 2) (t := 96) (b := 23306) rfl rfl ArealUCore.ArealUK.chunk_11652 s53
  have s51 : leavesOK ctxLitU 459300000000 2 ((leaves.drop 23302).take 98) 461750000000 2 = true :=
    take_step (n := 2) (t := 98) (b := 23304) rfl rfl ArealUCore.ArealUK.chunk_11651 s52
  have s50 : leavesOK ctxLitU 459250000000 2 ((leaves.drop 23300).take 100) 461750000000 2 = true :=
    take_step (n := 2) (t := 100) (b := 23302) rfl rfl ArealUCore.ArealUK.chunk_11650 s51
  have s49 : leavesOK ctxLitU 459200000000 2 ((leaves.drop 23298).take 102) 461750000000 2 = true :=
    take_step (n := 2) (t := 102) (b := 23300) rfl rfl ArealUCore.ArealUK.chunk_11649 s50
  have s48 : leavesOK ctxLitU 459150000000 2 ((leaves.drop 23296).take 104) 461750000000 2 = true :=
    take_step (n := 2) (t := 104) (b := 23298) rfl rfl ArealUCore.ArealUK.chunk_11648 s49
  have s47 : leavesOK ctxLitU 459100000000 2 ((leaves.drop 23294).take 106) 461750000000 2 = true :=
    take_step (n := 2) (t := 106) (b := 23296) rfl rfl ArealUCore.ArealUK.chunk_11647 s48
  have s46 : leavesOK ctxLitU 459050000000 2 ((leaves.drop 23292).take 108) 461750000000 2 = true :=
    take_step (n := 2) (t := 108) (b := 23294) rfl rfl ArealUCore.ArealUK.chunk_11646 s47
  have s45 : leavesOK ctxLitU 459000000000 2 ((leaves.drop 23290).take 110) 461750000000 2 = true :=
    take_step (n := 2) (t := 110) (b := 23292) rfl rfl ArealUCore.ArealUK.chunk_11645 s46
  have s44 : leavesOK ctxLitU 458950000000 2 ((leaves.drop 23288).take 112) 461750000000 2 = true :=
    take_step (n := 2) (t := 112) (b := 23290) rfl rfl ArealUCore.ArealUK.chunk_11644 s45
  have s43 : leavesOK ctxLitU 458900000000 2 ((leaves.drop 23286).take 114) 461750000000 2 = true :=
    take_step (n := 2) (t := 114) (b := 23288) rfl rfl ArealUCore.ArealUK.chunk_11643 s44
  have s42 : leavesOK ctxLitU 458850000000 2 ((leaves.drop 23284).take 116) 461750000000 2 = true :=
    take_step (n := 2) (t := 116) (b := 23286) rfl rfl ArealUCore.ArealUK.chunk_11642 s43
  have s41 : leavesOK ctxLitU 458800000000 2 ((leaves.drop 23282).take 118) 461750000000 2 = true :=
    take_step (n := 2) (t := 118) (b := 23284) rfl rfl ArealUCore.ArealUK.chunk_11641 s42
  have s40 : leavesOK ctxLitU 458750000000 2 ((leaves.drop 23280).take 120) 461750000000 2 = true :=
    take_step (n := 2) (t := 120) (b := 23282) rfl rfl ArealUCore.ArealUK.chunk_11640 s41
  have s39 : leavesOK ctxLitU 458700000000 2 ((leaves.drop 23278).take 122) 461750000000 2 = true :=
    take_step (n := 2) (t := 122) (b := 23280) rfl rfl ArealUCore.ArealUK.chunk_11639 s40
  have s38 : leavesOK ctxLitU 458650000000 2 ((leaves.drop 23276).take 124) 461750000000 2 = true :=
    take_step (n := 2) (t := 124) (b := 23278) rfl rfl ArealUCore.ArealUK.chunk_11638 s39
  have s37 : leavesOK ctxLitU 458600000000 2 ((leaves.drop 23274).take 126) 461750000000 2 = true :=
    take_step (n := 2) (t := 126) (b := 23276) rfl rfl ArealUCore.ArealUK.chunk_11637 s38
  have s36 : leavesOK ctxLitU 458550000000 2 ((leaves.drop 23272).take 128) 461750000000 2 = true :=
    take_step (n := 2) (t := 128) (b := 23274) rfl rfl ArealUCore.ArealUK.chunk_11636 s37
  have s35 : leavesOK ctxLitU 458500000000 2 ((leaves.drop 23270).take 130) 461750000000 2 = true :=
    take_step (n := 2) (t := 130) (b := 23272) rfl rfl ArealUCore.ArealUK.chunk_11635 s36
  have s34 : leavesOK ctxLitU 458450000000 2 ((leaves.drop 23268).take 132) 461750000000 2 = true :=
    take_step (n := 2) (t := 132) (b := 23270) rfl rfl ArealUCore.ArealUK.chunk_11634 s35
  have s33 : leavesOK ctxLitU 458400000000 2 ((leaves.drop 23266).take 134) 461750000000 2 = true :=
    take_step (n := 2) (t := 134) (b := 23268) rfl rfl ArealUCore.ArealUK.chunk_11633 s34
  have s32 : leavesOK ctxLitU 458350000000 2 ((leaves.drop 23264).take 136) 461750000000 2 = true :=
    take_step (n := 2) (t := 136) (b := 23266) rfl rfl ArealUCore.ArealUK.chunk_11632 s33
  have s31 : leavesOK ctxLitU 458300000000 2 ((leaves.drop 23262).take 138) 461750000000 2 = true :=
    take_step (n := 2) (t := 138) (b := 23264) rfl rfl ArealUCore.ArealUK.chunk_11631 s32
  have s30 : leavesOK ctxLitU 458250000000 2 ((leaves.drop 23260).take 140) 461750000000 2 = true :=
    take_step (n := 2) (t := 140) (b := 23262) rfl rfl ArealUCore.ArealUK.chunk_11630 s31
  have s29 : leavesOK ctxLitU 458200000000 2 ((leaves.drop 23258).take 142) 461750000000 2 = true :=
    take_step (n := 2) (t := 142) (b := 23260) rfl rfl ArealUCore.ArealUK.chunk_11629 s30
  have s28 : leavesOK ctxLitU 458150000000 2 ((leaves.drop 23256).take 144) 461750000000 2 = true :=
    take_step (n := 2) (t := 144) (b := 23258) rfl rfl ArealUCore.ArealUK.chunk_11628 s29
  have s27 : leavesOK ctxLitU 458100000000 2 ((leaves.drop 23254).take 146) 461750000000 2 = true :=
    take_step (n := 2) (t := 146) (b := 23256) rfl rfl ArealUCore.ArealUK.chunk_11627 s28
  have s26 : leavesOK ctxLitU 458050000000 2 ((leaves.drop 23252).take 148) 461750000000 2 = true :=
    take_step (n := 2) (t := 148) (b := 23254) rfl rfl ArealUCore.ArealUK.chunk_11626 s27
  have s25 : leavesOK ctxLitU 458000000000 2 ((leaves.drop 23250).take 150) 461750000000 2 = true :=
    take_step (n := 2) (t := 150) (b := 23252) rfl rfl ArealUCore.ArealUK.chunk_11625 s26
  have s24 : leavesOK ctxLitU 457950000000 2 ((leaves.drop 23248).take 152) 461750000000 2 = true :=
    take_step (n := 2) (t := 152) (b := 23250) rfl rfl ArealUCore.ArealUK.chunk_11624 s25
  have s23 : leavesOK ctxLitU 457900000000 2 ((leaves.drop 23246).take 154) 461750000000 2 = true :=
    take_step (n := 2) (t := 154) (b := 23248) rfl rfl ArealUCore.ArealUK.chunk_11623 s24
  have s22 : leavesOK ctxLitU 457850000000 2 ((leaves.drop 23244).take 156) 461750000000 2 = true :=
    take_step (n := 2) (t := 156) (b := 23246) rfl rfl ArealUCore.ArealUK.chunk_11622 s23
  have s21 : leavesOK ctxLitU 457800000000 2 ((leaves.drop 23242).take 158) 461750000000 2 = true :=
    take_step (n := 2) (t := 158) (b := 23244) rfl rfl ArealUCore.ArealUK.chunk_11621 s22
  have s20 : leavesOK ctxLitU 457750000000 2 ((leaves.drop 23240).take 160) 461750000000 2 = true :=
    take_step (n := 2) (t := 160) (b := 23242) rfl rfl ArealUCore.ArealUK.chunk_11620 s21
  have s19 : leavesOK ctxLitU 457700000000 2 ((leaves.drop 23238).take 162) 461750000000 2 = true :=
    take_step (n := 2) (t := 162) (b := 23240) rfl rfl ArealUCore.ArealUK.chunk_11619 s20
  have s18 : leavesOK ctxLitU 457650000000 2 ((leaves.drop 23236).take 164) 461750000000 2 = true :=
    take_step (n := 2) (t := 164) (b := 23238) rfl rfl ArealUCore.ArealUK.chunk_11618 s19
  have s17 : leavesOK ctxLitU 457600000000 2 ((leaves.drop 23234).take 166) 461750000000 2 = true :=
    take_step (n := 2) (t := 166) (b := 23236) rfl rfl ArealUCore.ArealUK.chunk_11617 s18
  have s16 : leavesOK ctxLitU 457550000000 2 ((leaves.drop 23232).take 168) 461750000000 2 = true :=
    take_step (n := 2) (t := 168) (b := 23234) rfl rfl ArealUCore.ArealUK.chunk_11616 s17
  have s15 : leavesOK ctxLitU 457500000000 2 ((leaves.drop 23230).take 170) 461750000000 2 = true :=
    take_step (n := 2) (t := 170) (b := 23232) rfl rfl ArealUCore.ArealUK.chunk_11615 s16
  have s14 : leavesOK ctxLitU 457450000000 2 ((leaves.drop 23228).take 172) 461750000000 2 = true :=
    take_step (n := 2) (t := 172) (b := 23230) rfl rfl ArealUCore.ArealUK.chunk_11614 s15
  have s13 : leavesOK ctxLitU 457400000000 2 ((leaves.drop 23226).take 174) 461750000000 2 = true :=
    take_step (n := 2) (t := 174) (b := 23228) rfl rfl ArealUCore.ArealUK.chunk_11613 s14
  have s12 : leavesOK ctxLitU 457350000000 2 ((leaves.drop 23224).take 176) 461750000000 2 = true :=
    take_step (n := 2) (t := 176) (b := 23226) rfl rfl ArealUCore.ArealUK.chunk_11612 s13
  have s11 : leavesOK ctxLitU 457300000000 2 ((leaves.drop 23222).take 178) 461750000000 2 = true :=
    take_step (n := 2) (t := 178) (b := 23224) rfl rfl ArealUCore.ArealUK.chunk_11611 s12
  have s10 : leavesOK ctxLitU 457250000000 2 ((leaves.drop 23220).take 180) 461750000000 2 = true :=
    take_step (n := 2) (t := 180) (b := 23222) rfl rfl ArealUCore.ArealUK.chunk_11610 s11
  have s9 : leavesOK ctxLitU 457200000000 2 ((leaves.drop 23218).take 182) 461750000000 2 = true :=
    take_step (n := 2) (t := 182) (b := 23220) rfl rfl ArealUCore.ArealUK.chunk_11609 s10
  have s8 : leavesOK ctxLitU 457150000000 2 ((leaves.drop 23216).take 184) 461750000000 2 = true :=
    take_step (n := 2) (t := 184) (b := 23218) rfl rfl ArealUCore.ArealUK.chunk_11608 s9
  have s7 : leavesOK ctxLitU 457100000000 2 ((leaves.drop 23214).take 186) 461750000000 2 = true :=
    take_step (n := 2) (t := 186) (b := 23216) rfl rfl ArealUCore.ArealUK.chunk_11607 s8
  have s6 : leavesOK ctxLitU 457050000000 2 ((leaves.drop 23212).take 188) 461750000000 2 = true :=
    take_step (n := 2) (t := 188) (b := 23214) rfl rfl ArealUCore.ArealUK.chunk_11606 s7
  have s5 : leavesOK ctxLitU 457000000000 2 ((leaves.drop 23210).take 190) 461750000000 2 = true :=
    take_step (n := 2) (t := 190) (b := 23212) rfl rfl ArealUCore.ArealUK.chunk_11605 s6
  have s4 : leavesOK ctxLitU 456950000000 2 ((leaves.drop 23208).take 192) 461750000000 2 = true :=
    take_step (n := 2) (t := 192) (b := 23210) rfl rfl ArealUCore.ArealUK.chunk_11604 s5
  have s3 : leavesOK ctxLitU 456900000000 2 ((leaves.drop 23206).take 194) 461750000000 2 = true :=
    take_step (n := 2) (t := 194) (b := 23208) rfl rfl ArealUCore.ArealUK.chunk_11603 s4
  have s2 : leavesOK ctxLitU 456850000000 2 ((leaves.drop 23204).take 196) 461750000000 2 = true :=
    take_step (n := 2) (t := 196) (b := 23206) rfl rfl ArealUCore.ArealUK.chunk_11602 s3
  have s1 : leavesOK ctxLitU 456800000000 2 ((leaves.drop 23202).take 198) 461750000000 2 = true :=
    take_step (n := 2) (t := 198) (b := 23204) rfl rfl ArealUCore.ArealUK.chunk_11601 s2
  have s0 : leavesOK ctxLitU 456750000000 2 ((leaves.drop 23200).take 200) 461750000000 2 = true :=
    take_step (n := 2) (t := 200) (b := 23202) rfl rfl ArealUCore.ArealUK.chunk_11600 s1
  exact s0

end Areal.UCert

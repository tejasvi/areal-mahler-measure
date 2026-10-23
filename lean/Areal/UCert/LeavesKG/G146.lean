import ArealUK.Chunk14600
import ArealUK.Chunk14601
import ArealUK.Chunk14602
import ArealUK.Chunk14603
import ArealUK.Chunk14604
import ArealUK.Chunk14605
import ArealUK.Chunk14606
import ArealUK.Chunk14607
import ArealUK.Chunk14608
import ArealUK.Chunk14609
import ArealUK.Chunk14610
import ArealUK.Chunk14611
import ArealUK.Chunk14612
import ArealUK.Chunk14613
import ArealUK.Chunk14614
import ArealUK.Chunk14615
import ArealUK.Chunk14616
import ArealUK.Chunk14617
import ArealUK.Chunk14618
import ArealUK.Chunk14619
import ArealUK.Chunk14620
import ArealUK.Chunk14621
import ArealUK.Chunk14622
import ArealUK.Chunk14623
import ArealUK.Chunk14624
import ArealUK.Chunk14625
import ArealUK.Chunk14626
import ArealUK.Chunk14627
import ArealUK.Chunk14628
import ArealUK.Chunk14629
import ArealUK.Chunk14630
import ArealUK.Chunk14631
import ArealUK.Chunk14632
import ArealUK.Chunk14633
import ArealUK.Chunk14634
import ArealUK.Chunk14635
import ArealUK.Chunk14636
import ArealUK.Chunk14637
import ArealUK.Chunk14638
import ArealUK.Chunk14639
import ArealUK.Chunk14640
import ArealUK.Chunk14641
import ArealUK.Chunk14642
import ArealUK.Chunk14643
import ArealUK.Chunk14644
import ArealUK.Chunk14645
import ArealUK.Chunk14646
import ArealUK.Chunk14647
import ArealUK.Chunk14648
import ArealUK.Chunk14649
import ArealUK.Chunk14650
import ArealUK.Chunk14651
import ArealUK.Chunk14652
import ArealUK.Chunk14653
import ArealUK.Chunk14654
import ArealUK.Chunk14655
import ArealUK.Chunk14656
import ArealUK.Chunk14657
import ArealUK.Chunk14658
import ArealUK.Chunk14659
import ArealUK.Chunk14660
import ArealUK.Chunk14661
import ArealUK.Chunk14662
import ArealUK.Chunk14663
import ArealUK.Chunk14664
import ArealUK.Chunk14665
import ArealUK.Chunk14666
import ArealUK.Chunk14667
import ArealUK.Chunk14668
import ArealUK.Chunk14669
import ArealUK.Chunk14670
import ArealUK.Chunk14671
import ArealUK.Chunk14672
import ArealUK.Chunk14673
import ArealUK.Chunk14674
import ArealUK.Chunk14675
import ArealUK.Chunk14676
import ArealUK.Chunk14677
import ArealUK.Chunk14678
import ArealUK.Chunk14679
import ArealUK.Chunk14680
import ArealUK.Chunk14681
import ArealUK.Chunk14682
import ArealUK.Chunk14683
import ArealUK.Chunk14684
import ArealUK.Chunk14685
import ArealUK.Chunk14686
import ArealUK.Chunk14687
import ArealUK.Chunk14688
import ArealUK.Chunk14689
import ArealUK.Chunk14690
import ArealUK.Chunk14691
import ArealUK.Chunk14692
import ArealUK.Chunk14693
import ArealUK.Chunk14694
import ArealUK.Chunk14695
import ArealUK.Chunk14696
import ArealUK.Chunk14697
import ArealUK.Chunk14698
import ArealUK.Chunk14699
import Areal.UCert.LeavesKGen

/-! Group 146 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_146 : leavesOK ctxLitU 302125000000 1 ((leaves.drop 29200).take 200) 152356250000 0 = true := by
  have s99 := ArealUCore.ArealUK.chunk_14699
  have s98 : leavesOK ctxLitU 152331250000 0 ((leaves.drop 29396).take 4) 152356250000 0 = true :=
    take_step (n := 2) (t := 4) (b := 29398) rfl rfl ArealUCore.ArealUK.chunk_14698 s99
  have s97 : leavesOK ctxLitU 304637500000 1 ((leaves.drop 29394).take 6) 152356250000 0 = true :=
    take_step (n := 2) (t := 6) (b := 29396) rfl rfl ArealUCore.ArealUK.chunk_14697 s98
  have s96 : leavesOK ctxLitU 304612500000 1 ((leaves.drop 29392).take 8) 152356250000 0 = true :=
    take_step (n := 2) (t := 8) (b := 29394) rfl rfl ArealUCore.ArealUK.chunk_14696 s97
  have s95 : leavesOK ctxLitU 304587500000 1 ((leaves.drop 29390).take 10) 152356250000 0 = true :=
    take_step (n := 2) (t := 10) (b := 29392) rfl rfl ArealUCore.ArealUK.chunk_14695 s96
  have s94 : leavesOK ctxLitU 304562500000 1 ((leaves.drop 29388).take 12) 152356250000 0 = true :=
    take_step (n := 2) (t := 12) (b := 29390) rfl rfl ArealUCore.ArealUK.chunk_14694 s95
  have s93 : leavesOK ctxLitU 152268750000 0 ((leaves.drop 29386).take 14) 152356250000 0 = true :=
    take_step (n := 2) (t := 14) (b := 29388) rfl rfl ArealUCore.ArealUK.chunk_14693 s94
  have s92 : leavesOK ctxLitU 152256250000 0 ((leaves.drop 29384).take 16) 152356250000 0 = true :=
    take_step (n := 2) (t := 16) (b := 29386) rfl rfl ArealUCore.ArealUK.chunk_14692 s93
  have s91 : leavesOK ctxLitU 152243750000 0 ((leaves.drop 29382).take 18) 152356250000 0 = true :=
    take_step (n := 2) (t := 18) (b := 29384) rfl rfl ArealUCore.ArealUK.chunk_14691 s92
  have s90 : leavesOK ctxLitU 152231250000 0 ((leaves.drop 29380).take 20) 152356250000 0 = true :=
    take_step (n := 2) (t := 20) (b := 29382) rfl rfl ArealUCore.ArealUK.chunk_14690 s91
  have s89 : leavesOK ctxLitU 304437500000 1 ((leaves.drop 29378).take 22) 152356250000 0 = true :=
    take_step (n := 2) (t := 22) (b := 29380) rfl rfl ArealUCore.ArealUK.chunk_14689 s90
  have s88 : leavesOK ctxLitU 152200000000 0 ((leaves.drop 29376).take 24) 152356250000 0 = true :=
    take_step (n := 2) (t := 24) (b := 29378) rfl rfl ArealUCore.ArealUK.chunk_14688 s89
  have s87 : leavesOK ctxLitU 304375000000 1 ((leaves.drop 29374).take 26) 152356250000 0 = true :=
    take_step (n := 2) (t := 26) (b := 29376) rfl rfl ArealUCore.ArealUK.chunk_14687 s88
  have s86 : leavesOK ctxLitU 304350000000 1 ((leaves.drop 29372).take 28) 152356250000 0 = true :=
    take_step (n := 2) (t := 28) (b := 29374) rfl rfl ArealUCore.ArealUK.chunk_14686 s87
  have s85 : leavesOK ctxLitU 152162500000 0 ((leaves.drop 29370).take 30) 152356250000 0 = true :=
    take_step (n := 2) (t := 30) (b := 29372) rfl rfl ArealUCore.ArealUK.chunk_14685 s86
  have s84 : leavesOK ctxLitU 152150000000 0 ((leaves.drop 29368).take 32) 152356250000 0 = true :=
    take_step (n := 2) (t := 32) (b := 29370) rfl rfl ArealUCore.ArealUK.chunk_14684 s85
  have s83 : leavesOK ctxLitU 152137500000 0 ((leaves.drop 29366).take 34) 152356250000 0 = true :=
    take_step (n := 2) (t := 34) (b := 29368) rfl rfl ArealUCore.ArealUK.chunk_14683 s84
  have s82 : leavesOK ctxLitU 152125000000 0 ((leaves.drop 29364).take 36) 152356250000 0 = true :=
    take_step (n := 2) (t := 36) (b := 29366) rfl rfl ArealUCore.ArealUK.chunk_14682 s83
  have s81 : leavesOK ctxLitU 304225000000 1 ((leaves.drop 29362).take 38) 152356250000 0 = true :=
    take_step (n := 2) (t := 38) (b := 29364) rfl rfl ArealUCore.ArealUK.chunk_14681 s82
  have s80 : leavesOK ctxLitU 304200000000 1 ((leaves.drop 29360).take 40) 152356250000 0 = true :=
    take_step (n := 2) (t := 40) (b := 29362) rfl rfl ArealUCore.ArealUK.chunk_14680 s81
  have s79 : leavesOK ctxLitU 304175000000 1 ((leaves.drop 29358).take 42) 152356250000 0 = true :=
    take_step (n := 2) (t := 42) (b := 29360) rfl rfl ArealUCore.ArealUK.chunk_14679 s80
  have s78 : leavesOK ctxLitU 304150000000 1 ((leaves.drop 29356).take 44) 152356250000 0 = true :=
    take_step (n := 2) (t := 44) (b := 29358) rfl rfl ArealUCore.ArealUK.chunk_14678 s79
  have s77 : leavesOK ctxLitU 152062500000 0 ((leaves.drop 29354).take 46) 152356250000 0 = true :=
    take_step (n := 2) (t := 46) (b := 29356) rfl rfl ArealUCore.ArealUK.chunk_14677 s78
  have s76 : leavesOK ctxLitU 152050000000 0 ((leaves.drop 29352).take 48) 152356250000 0 = true :=
    take_step (n := 2) (t := 48) (b := 29354) rfl rfl ArealUCore.ArealUK.chunk_14676 s77
  have s75 : leavesOK ctxLitU 152037500000 0 ((leaves.drop 29350).take 50) 152356250000 0 = true :=
    take_step (n := 2) (t := 50) (b := 29352) rfl rfl ArealUCore.ArealUK.chunk_14675 s76
  have s74 : leavesOK ctxLitU 152025000000 0 ((leaves.drop 29348).take 52) 152356250000 0 = true :=
    take_step (n := 2) (t := 52) (b := 29350) rfl rfl ArealUCore.ArealUK.chunk_14674 s75
  have s73 : leavesOK ctxLitU 304025000000 1 ((leaves.drop 29346).take 54) 152356250000 0 = true :=
    take_step (n := 2) (t := 54) (b := 29348) rfl rfl ArealUCore.ArealUK.chunk_14673 s74
  have s72 : leavesOK ctxLitU 151987500000 0 ((leaves.drop 29344).take 56) 152356250000 0 = true :=
    take_step (n := 2) (t := 56) (b := 29346) rfl rfl ArealUCore.ArealUK.chunk_14672 s73
  have s71 : leavesOK ctxLitU 303950000000 1 ((leaves.drop 29342).take 58) 152356250000 0 = true :=
    take_step (n := 2) (t := 58) (b := 29344) rfl rfl ArealUCore.ArealUK.chunk_14671 s72
  have s70 : leavesOK ctxLitU 151962500000 0 ((leaves.drop 29340).take 60) 152356250000 0 = true :=
    take_step (n := 2) (t := 60) (b := 29342) rfl rfl ArealUCore.ArealUK.chunk_14670 s71
  have s69 : leavesOK ctxLitU 151950000000 0 ((leaves.drop 29338).take 62) 152356250000 0 = true :=
    take_step (n := 2) (t := 62) (b := 29340) rfl rfl ArealUCore.ArealUK.chunk_14669 s70
  have s68 : leavesOK ctxLitU 151937500000 0 ((leaves.drop 29336).take 64) 152356250000 0 = true :=
    take_step (n := 2) (t := 64) (b := 29338) rfl rfl ArealUCore.ArealUK.chunk_14668 s69
  have s67 : leavesOK ctxLitU 151925000000 0 ((leaves.drop 29334).take 66) 152356250000 0 = true :=
    take_step (n := 2) (t := 66) (b := 29336) rfl rfl ArealUCore.ArealUK.chunk_14667 s68
  have s66 : leavesOK ctxLitU 303825000000 1 ((leaves.drop 29332).take 68) 152356250000 0 = true :=
    take_step (n := 2) (t := 68) (b := 29334) rfl rfl ArealUCore.ArealUK.chunk_14666 s67
  have s65 : leavesOK ctxLitU 303800000000 1 ((leaves.drop 29330).take 70) 152356250000 0 = true :=
    take_step (n := 2) (t := 70) (b := 29332) rfl rfl ArealUCore.ArealUK.chunk_14665 s66
  have s64 : leavesOK ctxLitU 303775000000 1 ((leaves.drop 29328).take 72) 152356250000 0 = true :=
    take_step (n := 2) (t := 72) (b := 29330) rfl rfl ArealUCore.ArealUK.chunk_14664 s65
  have s63 : leavesOK ctxLitU 303750000000 1 ((leaves.drop 29326).take 74) 152356250000 0 = true :=
    take_step (n := 2) (t := 74) (b := 29328) rfl rfl ArealUCore.ArealUK.chunk_14663 s64
  have s62 : leavesOK ctxLitU 151862500000 0 ((leaves.drop 29324).take 76) 152356250000 0 = true :=
    take_step (n := 2) (t := 76) (b := 29326) rfl rfl ArealUCore.ArealUK.chunk_14662 s63
  have s61 : leavesOK ctxLitU 151850000000 0 ((leaves.drop 29322).take 78) 152356250000 0 = true :=
    take_step (n := 2) (t := 78) (b := 29324) rfl rfl ArealUCore.ArealUK.chunk_14661 s62
  have s60 : leavesOK ctxLitU 151837500000 0 ((leaves.drop 29320).take 80) 152356250000 0 = true :=
    take_step (n := 2) (t := 80) (b := 29322) rfl rfl ArealUCore.ArealUK.chunk_14660 s61
  have s59 : leavesOK ctxLitU 151825000000 0 ((leaves.drop 29318).take 82) 152356250000 0 = true :=
    take_step (n := 2) (t := 82) (b := 29320) rfl rfl ArealUCore.ArealUK.chunk_14659 s60
  have s58 : leavesOK ctxLitU 303625000000 1 ((leaves.drop 29316).take 84) 152356250000 0 = true :=
    take_step (n := 2) (t := 84) (b := 29318) rfl rfl ArealUCore.ArealUK.chunk_14658 s59
  have s57 : leavesOK ctxLitU 303600000000 1 ((leaves.drop 29314).take 86) 152356250000 0 = true :=
    take_step (n := 2) (t := 86) (b := 29316) rfl rfl ArealUCore.ArealUK.chunk_14657 s58
  have s56 : leavesOK ctxLitU 303575000000 1 ((leaves.drop 29312).take 88) 152356250000 0 = true :=
    take_step (n := 2) (t := 88) (b := 29314) rfl rfl ArealUCore.ArealUK.chunk_14656 s57
  have s55 : leavesOK ctxLitU 303550000000 1 ((leaves.drop 29310).take 90) 152356250000 0 = true :=
    take_step (n := 2) (t := 90) (b := 29312) rfl rfl ArealUCore.ArealUK.chunk_14655 s56
  have s54 : leavesOK ctxLitU 151762500000 0 ((leaves.drop 29308).take 92) 152356250000 0 = true :=
    take_step (n := 2) (t := 92) (b := 29310) rfl rfl ArealUCore.ArealUK.chunk_14654 s55
  have s53 : leavesOK ctxLitU 151750000000 0 ((leaves.drop 29306).take 94) 152356250000 0 = true :=
    take_step (n := 2) (t := 94) (b := 29308) rfl rfl ArealUCore.ArealUK.chunk_14653 s54
  have s52 : leavesOK ctxLitU 151737500000 0 ((leaves.drop 29304).take 96) 152356250000 0 = true :=
    take_step (n := 2) (t := 96) (b := 29306) rfl rfl ArealUCore.ArealUK.chunk_14652 s53
  have s51 : leavesOK ctxLitU 151725000000 0 ((leaves.drop 29302).take 98) 152356250000 0 = true :=
    take_step (n := 2) (t := 98) (b := 29304) rfl rfl ArealUCore.ArealUK.chunk_14651 s52
  have s50 : leavesOK ctxLitU 303425000000 1 ((leaves.drop 29300).take 100) 152356250000 0 = true :=
    take_step (n := 2) (t := 100) (b := 29302) rfl rfl ArealUCore.ArealUK.chunk_14650 s51
  have s49 : leavesOK ctxLitU 303400000000 1 ((leaves.drop 29298).take 102) 152356250000 0 = true :=
    take_step (n := 2) (t := 102) (b := 29300) rfl rfl ArealUCore.ArealUK.chunk_14649 s50
  have s48 : leavesOK ctxLitU 303375000000 1 ((leaves.drop 29296).take 104) 152356250000 0 = true :=
    take_step (n := 2) (t := 104) (b := 29298) rfl rfl ArealUCore.ArealUK.chunk_14648 s49
  have s47 : leavesOK ctxLitU 303350000000 1 ((leaves.drop 29294).take 106) 152356250000 0 = true :=
    take_step (n := 2) (t := 106) (b := 29296) rfl rfl ArealUCore.ArealUK.chunk_14647 s48
  have s46 : leavesOK ctxLitU 151662500000 0 ((leaves.drop 29292).take 108) 152356250000 0 = true :=
    take_step (n := 2) (t := 108) (b := 29294) rfl rfl ArealUCore.ArealUK.chunk_14646 s47
  have s45 : leavesOK ctxLitU 151650000000 0 ((leaves.drop 29290).take 110) 152356250000 0 = true :=
    take_step (n := 2) (t := 110) (b := 29292) rfl rfl ArealUCore.ArealUK.chunk_14645 s46
  have s44 : leavesOK ctxLitU 151637500000 0 ((leaves.drop 29288).take 112) 152356250000 0 = true :=
    take_step (n := 2) (t := 112) (b := 29290) rfl rfl ArealUCore.ArealUK.chunk_14644 s45
  have s43 : leavesOK ctxLitU 151625000000 0 ((leaves.drop 29286).take 114) 152356250000 0 = true :=
    take_step (n := 2) (t := 114) (b := 29288) rfl rfl ArealUCore.ArealUK.chunk_14643 s44
  have s42 : leavesOK ctxLitU 303225000000 1 ((leaves.drop 29284).take 116) 152356250000 0 = true :=
    take_step (n := 2) (t := 116) (b := 29286) rfl rfl ArealUCore.ArealUK.chunk_14642 s43
  have s41 : leavesOK ctxLitU 303200000000 1 ((leaves.drop 29282).take 118) 152356250000 0 = true :=
    take_step (n := 2) (t := 118) (b := 29284) rfl rfl ArealUCore.ArealUK.chunk_14641 s42
  have s40 : leavesOK ctxLitU 303175000000 1 ((leaves.drop 29280).take 120) 152356250000 0 = true :=
    take_step (n := 2) (t := 120) (b := 29282) rfl rfl ArealUCore.ArealUK.chunk_14640 s41
  have s39 : leavesOK ctxLitU 303150000000 1 ((leaves.drop 29278).take 122) 152356250000 0 = true :=
    take_step (n := 2) (t := 122) (b := 29280) rfl rfl ArealUCore.ArealUK.chunk_14639 s40
  have s38 : leavesOK ctxLitU 151562500000 0 ((leaves.drop 29276).take 124) 152356250000 0 = true :=
    take_step (n := 2) (t := 124) (b := 29278) rfl rfl ArealUCore.ArealUK.chunk_14638 s39
  have s37 : leavesOK ctxLitU 151550000000 0 ((leaves.drop 29274).take 126) 152356250000 0 = true :=
    take_step (n := 2) (t := 126) (b := 29276) rfl rfl ArealUCore.ArealUK.chunk_14637 s38
  have s36 : leavesOK ctxLitU 151537500000 0 ((leaves.drop 29272).take 128) 152356250000 0 = true :=
    take_step (n := 2) (t := 128) (b := 29274) rfl rfl ArealUCore.ArealUK.chunk_14636 s37
  have s35 : leavesOK ctxLitU 151525000000 0 ((leaves.drop 29270).take 130) 152356250000 0 = true :=
    take_step (n := 2) (t := 130) (b := 29272) rfl rfl ArealUCore.ArealUK.chunk_14635 s36
  have s34 : leavesOK ctxLitU 303025000000 1 ((leaves.drop 29268).take 132) 152356250000 0 = true :=
    take_step (n := 2) (t := 132) (b := 29270) rfl rfl ArealUCore.ArealUK.chunk_14634 s35
  have s33 : leavesOK ctxLitU 303000000000 1 ((leaves.drop 29266).take 134) 152356250000 0 = true :=
    take_step (n := 2) (t := 134) (b := 29268) rfl rfl ArealUCore.ArealUK.chunk_14633 s34
  have s32 : leavesOK ctxLitU 302975000000 1 ((leaves.drop 29264).take 136) 152356250000 0 = true :=
    take_step (n := 2) (t := 136) (b := 29266) rfl rfl ArealUCore.ArealUK.chunk_14632 s33
  have s31 : leavesOK ctxLitU 302950000000 1 ((leaves.drop 29262).take 138) 152356250000 0 = true :=
    take_step (n := 2) (t := 138) (b := 29264) rfl rfl ArealUCore.ArealUK.chunk_14631 s32
  have s30 : leavesOK ctxLitU 151462500000 0 ((leaves.drop 29260).take 140) 152356250000 0 = true :=
    take_step (n := 2) (t := 140) (b := 29262) rfl rfl ArealUCore.ArealUK.chunk_14630 s31
  have s29 : leavesOK ctxLitU 151450000000 0 ((leaves.drop 29258).take 142) 152356250000 0 = true :=
    take_step (n := 2) (t := 142) (b := 29260) rfl rfl ArealUCore.ArealUK.chunk_14629 s30
  have s28 : leavesOK ctxLitU 151437500000 0 ((leaves.drop 29256).take 144) 152356250000 0 = true :=
    take_step (n := 2) (t := 144) (b := 29258) rfl rfl ArealUCore.ArealUK.chunk_14628 s29
  have s27 : leavesOK ctxLitU 151425000000 0 ((leaves.drop 29254).take 146) 152356250000 0 = true :=
    take_step (n := 2) (t := 146) (b := 29256) rfl rfl ArealUCore.ArealUK.chunk_14627 s28
  have s26 : leavesOK ctxLitU 302825000000 1 ((leaves.drop 29252).take 148) 152356250000 0 = true :=
    take_step (n := 2) (t := 148) (b := 29254) rfl rfl ArealUCore.ArealUK.chunk_14626 s27
  have s25 : leavesOK ctxLitU 302800000000 1 ((leaves.drop 29250).take 150) 152356250000 0 = true :=
    take_step (n := 2) (t := 150) (b := 29252) rfl rfl ArealUCore.ArealUK.chunk_14625 s26
  have s24 : leavesOK ctxLitU 302762500000 1 ((leaves.drop 29248).take 152) 152356250000 0 = true :=
    take_step (n := 2) (t := 152) (b := 29250) rfl rfl ArealUCore.ArealUK.chunk_14624 s25
  have s23 : leavesOK ctxLitU 151368750000 0 ((leaves.drop 29246).take 154) 152356250000 0 = true :=
    take_step (n := 2) (t := 154) (b := 29248) rfl rfl ArealUCore.ArealUK.chunk_14623 s24
  have s22 : leavesOK ctxLitU 151356250000 0 ((leaves.drop 29244).take 156) 152356250000 0 = true :=
    take_step (n := 2) (t := 156) (b := 29246) rfl rfl ArealUCore.ArealUK.chunk_14622 s23
  have s21 : leavesOK ctxLitU 302687500000 1 ((leaves.drop 29242).take 158) 152356250000 0 = true :=
    take_step (n := 2) (t := 158) (b := 29244) rfl rfl ArealUCore.ArealUK.chunk_14621 s22
  have s20 : leavesOK ctxLitU 302662500000 1 ((leaves.drop 29240).take 160) 152356250000 0 = true :=
    take_step (n := 2) (t := 160) (b := 29242) rfl rfl ArealUCore.ArealUK.chunk_14620 s21
  have s19 : leavesOK ctxLitU 302625000000 1 ((leaves.drop 29238).take 162) 152356250000 0 = true :=
    take_step (n := 2) (t := 162) (b := 29240) rfl rfl ArealUCore.ArealUK.chunk_14619 s20
  have s18 : leavesOK ctxLitU 605200000000 2 ((leaves.drop 29236).take 164) 152356250000 0 = true :=
    take_step (n := 2) (t := 164) (b := 29238) rfl rfl ArealUCore.ArealUK.chunk_14618 s19
  have s17 : leavesOK ctxLitU 302575000000 1 ((leaves.drop 29234).take 166) 152356250000 0 = true :=
    take_step (n := 2) (t := 166) (b := 29236) rfl rfl ArealUCore.ArealUK.chunk_14617 s18
  have s16 : leavesOK ctxLitU 302550000000 1 ((leaves.drop 29232).take 168) 152356250000 0 = true :=
    take_step (n := 2) (t := 168) (b := 29234) rfl rfl ArealUCore.ArealUK.chunk_14616 s17
  have s15 : leavesOK ctxLitU 151262500000 0 ((leaves.drop 29230).take 170) 152356250000 0 = true :=
    take_step (n := 2) (t := 170) (b := 29232) rfl rfl ArealUCore.ArealUK.chunk_14615 s16
  have s14 : leavesOK ctxLitU 151250000000 0 ((leaves.drop 29228).take 172) 152356250000 0 = true :=
    take_step (n := 2) (t := 172) (b := 29230) rfl rfl ArealUCore.ArealUK.chunk_14614 s15
  have s13 : leavesOK ctxLitU 151237500000 0 ((leaves.drop 29226).take 174) 152356250000 0 = true :=
    take_step (n := 2) (t := 174) (b := 29228) rfl rfl ArealUCore.ArealUK.chunk_14613 s14
  have s12 : leavesOK ctxLitU 151225000000 0 ((leaves.drop 29224).take 176) 152356250000 0 = true :=
    take_step (n := 2) (t := 176) (b := 29226) rfl rfl ArealUCore.ArealUK.chunk_14612 s13
  have s11 : leavesOK ctxLitU 302425000000 1 ((leaves.drop 29222).take 178) 152356250000 0 = true :=
    take_step (n := 2) (t := 178) (b := 29224) rfl rfl ArealUCore.ArealUK.chunk_14611 s12
  have s10 : leavesOK ctxLitU 302387500000 1 ((leaves.drop 29220).take 180) 152356250000 0 = true :=
    take_step (n := 2) (t := 180) (b := 29222) rfl rfl ArealUCore.ArealUK.chunk_14610 s11
  have s9 : leavesOK ctxLitU 302362500000 1 ((leaves.drop 29218).take 182) 152356250000 0 = true :=
    take_step (n := 2) (t := 182) (b := 29220) rfl rfl ArealUCore.ArealUK.chunk_14609 s10
  have s8 : leavesOK ctxLitU 151168750000 0 ((leaves.drop 29216).take 184) 152356250000 0 = true :=
    take_step (n := 2) (t := 184) (b := 29218) rfl rfl ArealUCore.ArealUK.chunk_14608 s9
  have s7 : leavesOK ctxLitU 151156250000 0 ((leaves.drop 29214).take 186) 152356250000 0 = true :=
    take_step (n := 2) (t := 186) (b := 29216) rfl rfl ArealUCore.ArealUK.chunk_14607 s8
  have s6 : leavesOK ctxLitU 151143750000 0 ((leaves.drop 29212).take 188) 152356250000 0 = true :=
    take_step (n := 2) (t := 188) (b := 29214) rfl rfl ArealUCore.ArealUK.chunk_14606 s7
  have s5 : leavesOK ctxLitU 151131250000 0 ((leaves.drop 29210).take 190) 152356250000 0 = true :=
    take_step (n := 2) (t := 190) (b := 29212) rfl rfl ArealUCore.ArealUK.chunk_14605 s6
  have s4 : leavesOK ctxLitU 302237500000 1 ((leaves.drop 29208).take 192) 152356250000 0 = true :=
    take_step (n := 2) (t := 192) (b := 29210) rfl rfl ArealUCore.ArealUK.chunk_14604 s5
  have s3 : leavesOK ctxLitU 302212500000 1 ((leaves.drop 29206).take 194) 152356250000 0 = true :=
    take_step (n := 2) (t := 194) (b := 29208) rfl rfl ArealUCore.ArealUK.chunk_14603 s4
  have s2 : leavesOK ctxLitU 604375000000 2 ((leaves.drop 29204).take 196) 152356250000 0 = true :=
    take_step (n := 2) (t := 196) (b := 29206) rfl rfl ArealUCore.ArealUK.chunk_14602 s3
  have s1 : leavesOK ctxLitU 302150000000 1 ((leaves.drop 29202).take 198) 152356250000 0 = true :=
    take_step (n := 2) (t := 198) (b := 29204) rfl rfl ArealUCore.ArealUK.chunk_14601 s2
  have s0 : leavesOK ctxLitU 302125000000 1 ((leaves.drop 29200).take 200) 152356250000 0 = true :=
    take_step (n := 2) (t := 200) (b := 29202) rfl rfl ArealUCore.ArealUK.chunk_14600 s1
  exact s0

end Areal.UCert

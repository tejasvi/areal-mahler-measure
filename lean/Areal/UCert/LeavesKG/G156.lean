import ArealUK.Chunk15600
import ArealUK.Chunk15601
import ArealUK.Chunk15602
import ArealUK.Chunk15603
import ArealUK.Chunk15604
import ArealUK.Chunk15605
import ArealUK.Chunk15606
import ArealUK.Chunk15607
import ArealUK.Chunk15608
import ArealUK.Chunk15609
import ArealUK.Chunk15610
import ArealUK.Chunk15611
import ArealUK.Chunk15612
import ArealUK.Chunk15613
import ArealUK.Chunk15614
import ArealUK.Chunk15615
import ArealUK.Chunk15616
import ArealUK.Chunk15617
import ArealUK.Chunk15618
import ArealUK.Chunk15619
import ArealUK.Chunk15620
import ArealUK.Chunk15621
import ArealUK.Chunk15622
import ArealUK.Chunk15623
import ArealUK.Chunk15624
import ArealUK.Chunk15625
import ArealUK.Chunk15626
import ArealUK.Chunk15627
import ArealUK.Chunk15628
import ArealUK.Chunk15629
import ArealUK.Chunk15630
import ArealUK.Chunk15631
import ArealUK.Chunk15632
import ArealUK.Chunk15633
import ArealUK.Chunk15634
import ArealUK.Chunk15635
import ArealUK.Chunk15636
import ArealUK.Chunk15637
import ArealUK.Chunk15638
import ArealUK.Chunk15639
import ArealUK.Chunk15640
import ArealUK.Chunk15641
import ArealUK.Chunk15642
import ArealUK.Chunk15643
import ArealUK.Chunk15644
import ArealUK.Chunk15645
import ArealUK.Chunk15646
import ArealUK.Chunk15647
import ArealUK.Chunk15648
import ArealUK.Chunk15649
import ArealUK.Chunk15650
import ArealUK.Chunk15651
import ArealUK.Chunk15652
import ArealUK.Chunk15653
import ArealUK.Chunk15654
import ArealUK.Chunk15655
import ArealUK.Chunk15656
import ArealUK.Chunk15657
import ArealUK.Chunk15658
import ArealUK.Chunk15659
import ArealUK.Chunk15660
import ArealUK.Chunk15661
import ArealUK.Chunk15662
import ArealUK.Chunk15663
import ArealUK.Chunk15664
import ArealUK.Chunk15665
import ArealUK.Chunk15666
import ArealUK.Chunk15667
import ArealUK.Chunk15668
import ArealUK.Chunk15669
import ArealUK.Chunk15670
import ArealUK.Chunk15671
import ArealUK.Chunk15672
import ArealUK.Chunk15673
import ArealUK.Chunk15674
import ArealUK.Chunk15675
import ArealUK.Chunk15676
import ArealUK.Chunk15677
import ArealUK.Chunk15678
import ArealUK.Chunk15679
import ArealUK.Chunk15680
import ArealUK.Chunk15681
import ArealUK.Chunk15682
import ArealUK.Chunk15683
import ArealUK.Chunk15684
import ArealUK.Chunk15685
import ArealUK.Chunk15686
import ArealUK.Chunk15687
import ArealUK.Chunk15688
import ArealUK.Chunk15689
import ArealUK.Chunk15690
import ArealUK.Chunk15691
import ArealUK.Chunk15692
import ArealUK.Chunk15693
import ArealUK.Chunk15694
import ArealUK.Chunk15695
import ArealUK.Chunk15696
import ArealUK.Chunk15697
import ArealUK.Chunk15698
import ArealUK.Chunk15699
import Areal.UCert.LeavesKGen

/-! Group 156 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_156 : leavesOK ctxLitU 165162500000 0 ((leaves.drop 31200).take 200) 166668750000 0 = true := by
  have s99 := ArealUCore.ArealUK.chunk_15699
  have s98 : leavesOK ctxLitU 166643750000 0 ((leaves.drop 31396).take 4) 166668750000 0 = true :=
    take_step (n := 2) (t := 4) (b := 31398) rfl rfl ArealUCore.ArealUK.chunk_15698 s99
  have s97 : leavesOK ctxLitU 166631250000 0 ((leaves.drop 31394).take 6) 166668750000 0 = true :=
    take_step (n := 2) (t := 6) (b := 31396) rfl rfl ArealUCore.ArealUK.chunk_15697 s98
  have s96 : leavesOK ctxLitU 166612500000 0 ((leaves.drop 31392).take 8) 166668750000 0 = true :=
    take_step (n := 2) (t := 8) (b := 31394) rfl rfl ArealUCore.ArealUK.chunk_15696 s97
  have s95 : leavesOK ctxLitU 166587500000 0 ((leaves.drop 31390).take 10) 166668750000 0 = true :=
    take_step (n := 2) (t := 10) (b := 31392) rfl rfl ArealUCore.ArealUK.chunk_15695 s96
  have s94 : leavesOK ctxLitU 166568750000 0 ((leaves.drop 31388).take 12) 166668750000 0 = true :=
    take_step (n := 2) (t := 12) (b := 31390) rfl rfl ArealUCore.ArealUK.chunk_15694 s95
  have s93 : leavesOK ctxLitU 166556250000 0 ((leaves.drop 31386).take 14) 166668750000 0 = true :=
    take_step (n := 2) (t := 14) (b := 31388) rfl rfl ArealUCore.ArealUK.chunk_15693 s94
  have s92 : leavesOK ctxLitU 166543750000 0 ((leaves.drop 31384).take 16) 166668750000 0 = true :=
    take_step (n := 2) (t := 16) (b := 31386) rfl rfl ArealUCore.ArealUK.chunk_15692 s93
  have s91 : leavesOK ctxLitU 166531250000 0 ((leaves.drop 31382).take 18) 166668750000 0 = true :=
    take_step (n := 2) (t := 18) (b := 31384) rfl rfl ArealUCore.ArealUK.chunk_15691 s92
  have s90 : leavesOK ctxLitU 166512500000 0 ((leaves.drop 31380).take 20) 166668750000 0 = true :=
    take_step (n := 2) (t := 20) (b := 31382) rfl rfl ArealUCore.ArealUK.chunk_15690 s91
  have s89 : leavesOK ctxLitU 332987500000 1 ((leaves.drop 31378).take 22) 166668750000 0 = true :=
    take_step (n := 2) (t := 22) (b := 31380) rfl rfl ArealUCore.ArealUK.chunk_15689 s90
  have s88 : leavesOK ctxLitU 332962500000 1 ((leaves.drop 31376).take 24) 166668750000 0 = true :=
    take_step (n := 2) (t := 24) (b := 31378) rfl rfl ArealUCore.ArealUK.chunk_15688 s89
  have s87 : leavesOK ctxLitU 166468750000 0 ((leaves.drop 31374).take 26) 166668750000 0 = true :=
    take_step (n := 2) (t := 26) (b := 31376) rfl rfl ArealUCore.ArealUK.chunk_15687 s88
  have s86 : leavesOK ctxLitU 166456250000 0 ((leaves.drop 31372).take 28) 166668750000 0 = true :=
    take_step (n := 2) (t := 28) (b := 31374) rfl rfl ArealUCore.ArealUK.chunk_15686 s87
  have s85 : leavesOK ctxLitU 166443750000 0 ((leaves.drop 31370).take 30) 166668750000 0 = true :=
    take_step (n := 2) (t := 30) (b := 31372) rfl rfl ArealUCore.ArealUK.chunk_15685 s86
  have s84 : leavesOK ctxLitU 166431250000 0 ((leaves.drop 31368).take 32) 166668750000 0 = true :=
    take_step (n := 2) (t := 32) (b := 31370) rfl rfl ArealUCore.ArealUK.chunk_15684 s85
  have s83 : leavesOK ctxLitU 166412500000 0 ((leaves.drop 31366).take 34) 166668750000 0 = true :=
    take_step (n := 2) (t := 34) (b := 31368) rfl rfl ArealUCore.ArealUK.chunk_15683 s84
  have s82 : leavesOK ctxLitU 166393750000 0 ((leaves.drop 31364).take 36) 166668750000 0 = true :=
    take_step (n := 2) (t := 36) (b := 31366) rfl rfl ArealUCore.ArealUK.chunk_15682 s83
  have s81 : leavesOK ctxLitU 166381250000 0 ((leaves.drop 31362).take 38) 166668750000 0 = true :=
    take_step (n := 2) (t := 38) (b := 31364) rfl rfl ArealUCore.ArealUK.chunk_15681 s82
  have s80 : leavesOK ctxLitU 166368750000 0 ((leaves.drop 31360).take 40) 166668750000 0 = true :=
    take_step (n := 2) (t := 40) (b := 31362) rfl rfl ArealUCore.ArealUK.chunk_15680 s81
  have s79 : leavesOK ctxLitU 166356250000 0 ((leaves.drop 31358).take 42) 166668750000 0 = true :=
    take_step (n := 2) (t := 42) (b := 31360) rfl rfl ArealUCore.ArealUK.chunk_15679 s80
  have s78 : leavesOK ctxLitU 166343750000 0 ((leaves.drop 31356).take 44) 166668750000 0 = true :=
    take_step (n := 2) (t := 44) (b := 31358) rfl rfl ArealUCore.ArealUK.chunk_15678 s79
  have s77 : leavesOK ctxLitU 166331250000 0 ((leaves.drop 31354).take 46) 166668750000 0 = true :=
    take_step (n := 2) (t := 46) (b := 31356) rfl rfl ArealUCore.ArealUK.chunk_15677 s78
  have s76 : leavesOK ctxLitU 166312500000 0 ((leaves.drop 31352).take 48) 166668750000 0 = true :=
    take_step (n := 2) (t := 48) (b := 31354) rfl rfl ArealUCore.ArealUK.chunk_15676 s77
  have s75 : leavesOK ctxLitU 166287500000 0 ((leaves.drop 31350).take 50) 166668750000 0 = true :=
    take_step (n := 2) (t := 50) (b := 31352) rfl rfl ArealUCore.ArealUK.chunk_15675 s76
  have s74 : leavesOK ctxLitU 166268750000 0 ((leaves.drop 31348).take 52) 166668750000 0 = true :=
    take_step (n := 2) (t := 52) (b := 31350) rfl rfl ArealUCore.ArealUK.chunk_15674 s75
  have s73 : leavesOK ctxLitU 166256250000 0 ((leaves.drop 31346).take 54) 166668750000 0 = true :=
    take_step (n := 2) (t := 54) (b := 31348) rfl rfl ArealUCore.ArealUK.chunk_15673 s74
  have s72 : leavesOK ctxLitU 166243750000 0 ((leaves.drop 31344).take 56) 166668750000 0 = true :=
    take_step (n := 2) (t := 56) (b := 31346) rfl rfl ArealUCore.ArealUK.chunk_15672 s73
  have s71 : leavesOK ctxLitU 166231250000 0 ((leaves.drop 31342).take 58) 166668750000 0 = true :=
    take_step (n := 2) (t := 58) (b := 31344) rfl rfl ArealUCore.ArealUK.chunk_15671 s72
  have s70 : leavesOK ctxLitU 166212500000 0 ((leaves.drop 31340).take 60) 166668750000 0 = true :=
    take_step (n := 2) (t := 60) (b := 31342) rfl rfl ArealUCore.ArealUK.chunk_15670 s71
  have s69 : leavesOK ctxLitU 166187500000 0 ((leaves.drop 31338).take 62) 166668750000 0 = true :=
    take_step (n := 2) (t := 62) (b := 31340) rfl rfl ArealUCore.ArealUK.chunk_15669 s70
  have s68 : leavesOK ctxLitU 166168750000 0 ((leaves.drop 31336).take 64) 166668750000 0 = true :=
    take_step (n := 2) (t := 64) (b := 31338) rfl rfl ArealUCore.ArealUK.chunk_15668 s69
  have s67 : leavesOK ctxLitU 166156250000 0 ((leaves.drop 31334).take 66) 166668750000 0 = true :=
    take_step (n := 2) (t := 66) (b := 31336) rfl rfl ArealUCore.ArealUK.chunk_15667 s68
  have s66 : leavesOK ctxLitU 166143750000 0 ((leaves.drop 31332).take 68) 166668750000 0 = true :=
    take_step (n := 2) (t := 68) (b := 31334) rfl rfl ArealUCore.ArealUK.chunk_15666 s67
  have s65 : leavesOK ctxLitU 166131250000 0 ((leaves.drop 31330).take 70) 166668750000 0 = true :=
    take_step (n := 2) (t := 70) (b := 31332) rfl rfl ArealUCore.ArealUK.chunk_15665 s66
  have s64 : leavesOK ctxLitU 332237500000 1 ((leaves.drop 31328).take 72) 166668750000 0 = true :=
    take_step (n := 2) (t := 72) (b := 31330) rfl rfl ArealUCore.ArealUK.chunk_15664 s65
  have s63 : leavesOK ctxLitU 332212500000 1 ((leaves.drop 31326).take 74) 166668750000 0 = true :=
    take_step (n := 2) (t := 74) (b := 31328) rfl rfl ArealUCore.ArealUK.chunk_15663 s64
  have s62 : leavesOK ctxLitU 166087500000 0 ((leaves.drop 31324).take 76) 166668750000 0 = true :=
    take_step (n := 2) (t := 76) (b := 31326) rfl rfl ArealUCore.ArealUK.chunk_15662 s63
  have s61 : leavesOK ctxLitU 166068750000 0 ((leaves.drop 31322).take 78) 166668750000 0 = true :=
    take_step (n := 2) (t := 78) (b := 31324) rfl rfl ArealUCore.ArealUK.chunk_15661 s62
  have s60 : leavesOK ctxLitU 166056250000 0 ((leaves.drop 31320).take 80) 166668750000 0 = true :=
    take_step (n := 2) (t := 80) (b := 31322) rfl rfl ArealUCore.ArealUK.chunk_15660 s61
  have s59 : leavesOK ctxLitU 166043750000 0 ((leaves.drop 31318).take 82) 166668750000 0 = true :=
    take_step (n := 2) (t := 82) (b := 31320) rfl rfl ArealUCore.ArealUK.chunk_15659 s60
  have s58 : leavesOK ctxLitU 166031250000 0 ((leaves.drop 31316).take 84) 166668750000 0 = true :=
    take_step (n := 2) (t := 84) (b := 31318) rfl rfl ArealUCore.ArealUK.chunk_15658 s59
  have s57 : leavesOK ctxLitU 166012500000 0 ((leaves.drop 31314).take 86) 166668750000 0 = true :=
    take_step (n := 2) (t := 86) (b := 31316) rfl rfl ArealUCore.ArealUK.chunk_15657 s58
  have s56 : leavesOK ctxLitU 165987500000 0 ((leaves.drop 31312).take 88) 166668750000 0 = true :=
    take_step (n := 2) (t := 88) (b := 31314) rfl rfl ArealUCore.ArealUK.chunk_15656 s57
  have s55 : leavesOK ctxLitU 165968750000 0 ((leaves.drop 31310).take 90) 166668750000 0 = true :=
    take_step (n := 2) (t := 90) (b := 31312) rfl rfl ArealUCore.ArealUK.chunk_15655 s56
  have s54 : leavesOK ctxLitU 165956250000 0 ((leaves.drop 31308).take 92) 166668750000 0 = true :=
    take_step (n := 2) (t := 92) (b := 31310) rfl rfl ArealUCore.ArealUK.chunk_15654 s55
  have s53 : leavesOK ctxLitU 165943750000 0 ((leaves.drop 31306).take 94) 166668750000 0 = true :=
    take_step (n := 2) (t := 94) (b := 31308) rfl rfl ArealUCore.ArealUK.chunk_15653 s54
  have s52 : leavesOK ctxLitU 165931250000 0 ((leaves.drop 31304).take 96) 166668750000 0 = true :=
    take_step (n := 2) (t := 96) (b := 31306) rfl rfl ArealUCore.ArealUK.chunk_15652 s53
  have s51 : leavesOK ctxLitU 331837500000 1 ((leaves.drop 31302).take 98) 166668750000 0 = true :=
    take_step (n := 2) (t := 98) (b := 31304) rfl rfl ArealUCore.ArealUK.chunk_15651 s52
  have s50 : leavesOK ctxLitU 331812500000 1 ((leaves.drop 31300).take 100) 166668750000 0 = true :=
    take_step (n := 2) (t := 100) (b := 31302) rfl rfl ArealUCore.ArealUK.chunk_15650 s51
  have s49 : leavesOK ctxLitU 165887500000 0 ((leaves.drop 31298).take 102) 166668750000 0 = true :=
    take_step (n := 2) (t := 102) (b := 31300) rfl rfl ArealUCore.ArealUK.chunk_15649 s50
  have s48 : leavesOK ctxLitU 165868750000 0 ((leaves.drop 31296).take 104) 166668750000 0 = true :=
    take_step (n := 2) (t := 104) (b := 31298) rfl rfl ArealUCore.ArealUK.chunk_15648 s49
  have s47 : leavesOK ctxLitU 165856250000 0 ((leaves.drop 31294).take 106) 166668750000 0 = true :=
    take_step (n := 2) (t := 106) (b := 31296) rfl rfl ArealUCore.ArealUK.chunk_15647 s48
  have s46 : leavesOK ctxLitU 165843750000 0 ((leaves.drop 31292).take 108) 166668750000 0 = true :=
    take_step (n := 2) (t := 108) (b := 31294) rfl rfl ArealUCore.ArealUK.chunk_15646 s47
  have s45 : leavesOK ctxLitU 165831250000 0 ((leaves.drop 31290).take 110) 166668750000 0 = true :=
    take_step (n := 2) (t := 110) (b := 31292) rfl rfl ArealUCore.ArealUK.chunk_15645 s46
  have s44 : leavesOK ctxLitU 165812500000 0 ((leaves.drop 31288).take 112) 166668750000 0 = true :=
    take_step (n := 2) (t := 112) (b := 31290) rfl rfl ArealUCore.ArealUK.chunk_15644 s45
  have s43 : leavesOK ctxLitU 165787500000 0 ((leaves.drop 31286).take 114) 166668750000 0 = true :=
    take_step (n := 2) (t := 114) (b := 31288) rfl rfl ArealUCore.ArealUK.chunk_15643 s44
  have s42 : leavesOK ctxLitU 165768750000 0 ((leaves.drop 31284).take 116) 166668750000 0 = true :=
    take_step (n := 2) (t := 116) (b := 31286) rfl rfl ArealUCore.ArealUK.chunk_15642 s43
  have s41 : leavesOK ctxLitU 165756250000 0 ((leaves.drop 31282).take 118) 166668750000 0 = true :=
    take_step (n := 2) (t := 118) (b := 31284) rfl rfl ArealUCore.ArealUK.chunk_15641 s42
  have s40 : leavesOK ctxLitU 165743750000 0 ((leaves.drop 31280).take 120) 166668750000 0 = true :=
    take_step (n := 2) (t := 120) (b := 31282) rfl rfl ArealUCore.ArealUK.chunk_15640 s41
  have s39 : leavesOK ctxLitU 165731250000 0 ((leaves.drop 31278).take 122) 166668750000 0 = true :=
    take_step (n := 2) (t := 122) (b := 31280) rfl rfl ArealUCore.ArealUK.chunk_15639 s40
  have s38 : leavesOK ctxLitU 165712500000 0 ((leaves.drop 31276).take 124) 166668750000 0 = true :=
    take_step (n := 2) (t := 124) (b := 31278) rfl rfl ArealUCore.ArealUK.chunk_15638 s39
  have s37 : leavesOK ctxLitU 331387500000 1 ((leaves.drop 31274).take 126) 166668750000 0 = true :=
    take_step (n := 2) (t := 126) (b := 31276) rfl rfl ArealUCore.ArealUK.chunk_15637 s38
  have s36 : leavesOK ctxLitU 331362500000 1 ((leaves.drop 31272).take 128) 166668750000 0 = true :=
    take_step (n := 2) (t := 128) (b := 31274) rfl rfl ArealUCore.ArealUK.chunk_15636 s37
  have s35 : leavesOK ctxLitU 165668750000 0 ((leaves.drop 31270).take 130) 166668750000 0 = true :=
    take_step (n := 2) (t := 130) (b := 31272) rfl rfl ArealUCore.ArealUK.chunk_15635 s36
  have s34 : leavesOK ctxLitU 165656250000 0 ((leaves.drop 31268).take 132) 166668750000 0 = true :=
    take_step (n := 2) (t := 132) (b := 31270) rfl rfl ArealUCore.ArealUK.chunk_15634 s35
  have s33 : leavesOK ctxLitU 165643750000 0 ((leaves.drop 31266).take 134) 166668750000 0 = true :=
    take_step (n := 2) (t := 134) (b := 31268) rfl rfl ArealUCore.ArealUK.chunk_15633 s34
  have s32 : leavesOK ctxLitU 165631250000 0 ((leaves.drop 31264).take 136) 166668750000 0 = true :=
    take_step (n := 2) (t := 136) (b := 31266) rfl rfl ArealUCore.ArealUK.chunk_15632 s33
  have s31 : leavesOK ctxLitU 165618750000 0 ((leaves.drop 31262).take 138) 166668750000 0 = true :=
    take_step (n := 2) (t := 138) (b := 31264) rfl rfl ArealUCore.ArealUK.chunk_15631 s32
  have s30 : leavesOK ctxLitU 165606250000 0 ((leaves.drop 31260).take 140) 166668750000 0 = true :=
    take_step (n := 2) (t := 140) (b := 31262) rfl rfl ArealUCore.ArealUK.chunk_15630 s31
  have s29 : leavesOK ctxLitU 165593750000 0 ((leaves.drop 31258).take 142) 166668750000 0 = true :=
    take_step (n := 2) (t := 142) (b := 31260) rfl rfl ArealUCore.ArealUK.chunk_15629 s30
  have s28 : leavesOK ctxLitU 165581250000 0 ((leaves.drop 31256).take 144) 166668750000 0 = true :=
    take_step (n := 2) (t := 144) (b := 31258) rfl rfl ArealUCore.ArealUK.chunk_15628 s29
  have s27 : leavesOK ctxLitU 165568750000 0 ((leaves.drop 31254).take 146) 166668750000 0 = true :=
    take_step (n := 2) (t := 146) (b := 31256) rfl rfl ArealUCore.ArealUK.chunk_15627 s28
  have s26 : leavesOK ctxLitU 165556250000 0 ((leaves.drop 31252).take 148) 166668750000 0 = true :=
    take_step (n := 2) (t := 148) (b := 31254) rfl rfl ArealUCore.ArealUK.chunk_15626 s27
  have s25 : leavesOK ctxLitU 165543750000 0 ((leaves.drop 31250).take 150) 166668750000 0 = true :=
    take_step (n := 2) (t := 150) (b := 31252) rfl rfl ArealUCore.ArealUK.chunk_15625 s26
  have s24 : leavesOK ctxLitU 165531250000 0 ((leaves.drop 31248).take 152) 166668750000 0 = true :=
    take_step (n := 2) (t := 152) (b := 31250) rfl rfl ArealUCore.ArealUK.chunk_15624 s25
  have s23 : leavesOK ctxLitU 165512500000 0 ((leaves.drop 31246).take 154) 166668750000 0 = true :=
    take_step (n := 2) (t := 154) (b := 31248) rfl rfl ArealUCore.ArealUK.chunk_15623 s24
  have s22 : leavesOK ctxLitU 165487500000 0 ((leaves.drop 31244).take 156) 166668750000 0 = true :=
    take_step (n := 2) (t := 156) (b := 31246) rfl rfl ArealUCore.ArealUK.chunk_15622 s23
  have s21 : leavesOK ctxLitU 165468750000 0 ((leaves.drop 31242).take 158) 166668750000 0 = true :=
    take_step (n := 2) (t := 158) (b := 31244) rfl rfl ArealUCore.ArealUK.chunk_15621 s22
  have s20 : leavesOK ctxLitU 165456250000 0 ((leaves.drop 31240).take 160) 166668750000 0 = true :=
    take_step (n := 2) (t := 160) (b := 31242) rfl rfl ArealUCore.ArealUK.chunk_15620 s21
  have s19 : leavesOK ctxLitU 165443750000 0 ((leaves.drop 31238).take 162) 166668750000 0 = true :=
    take_step (n := 2) (t := 162) (b := 31240) rfl rfl ArealUCore.ArealUK.chunk_15619 s20
  have s18 : leavesOK ctxLitU 165431250000 0 ((leaves.drop 31236).take 164) 166668750000 0 = true :=
    take_step (n := 2) (t := 164) (b := 31238) rfl rfl ArealUCore.ArealUK.chunk_15618 s19
  have s17 : leavesOK ctxLitU 165412500000 0 ((leaves.drop 31234).take 166) 166668750000 0 = true :=
    take_step (n := 2) (t := 166) (b := 31236) rfl rfl ArealUCore.ArealUK.chunk_15617 s18
  have s16 : leavesOK ctxLitU 165393750000 0 ((leaves.drop 31232).take 168) 166668750000 0 = true :=
    take_step (n := 2) (t := 168) (b := 31234) rfl rfl ArealUCore.ArealUK.chunk_15616 s17
  have s15 : leavesOK ctxLitU 165381250000 0 ((leaves.drop 31230).take 170) 166668750000 0 = true :=
    take_step (n := 2) (t := 170) (b := 31232) rfl rfl ArealUCore.ArealUK.chunk_15615 s16
  have s14 : leavesOK ctxLitU 165368750000 0 ((leaves.drop 31228).take 172) 166668750000 0 = true :=
    take_step (n := 2) (t := 172) (b := 31230) rfl rfl ArealUCore.ArealUK.chunk_15614 s15
  have s13 : leavesOK ctxLitU 165356250000 0 ((leaves.drop 31226).take 174) 166668750000 0 = true :=
    take_step (n := 2) (t := 174) (b := 31228) rfl rfl ArealUCore.ArealUK.chunk_15613 s14
  have s12 : leavesOK ctxLitU 165343750000 0 ((leaves.drop 31224).take 176) 166668750000 0 = true :=
    take_step (n := 2) (t := 176) (b := 31226) rfl rfl ArealUCore.ArealUK.chunk_15612 s13
  have s11 : leavesOK ctxLitU 165331250000 0 ((leaves.drop 31222).take 178) 166668750000 0 = true :=
    take_step (n := 2) (t := 178) (b := 31224) rfl rfl ArealUCore.ArealUK.chunk_15611 s12
  have s10 : leavesOK ctxLitU 330637500000 1 ((leaves.drop 31220).take 180) 166668750000 0 = true :=
    take_step (n := 2) (t := 180) (b := 31222) rfl rfl ArealUCore.ArealUK.chunk_15610 s11
  have s9 : leavesOK ctxLitU 330612500000 1 ((leaves.drop 31218).take 182) 166668750000 0 = true :=
    take_step (n := 2) (t := 182) (b := 31220) rfl rfl ArealUCore.ArealUK.chunk_15609 s10
  have s8 : leavesOK ctxLitU 165287500000 0 ((leaves.drop 31216).take 184) 166668750000 0 = true :=
    take_step (n := 2) (t := 184) (b := 31218) rfl rfl ArealUCore.ArealUK.chunk_15608 s9
  have s7 : leavesOK ctxLitU 165268750000 0 ((leaves.drop 31214).take 186) 166668750000 0 = true :=
    take_step (n := 2) (t := 186) (b := 31216) rfl rfl ArealUCore.ArealUK.chunk_15607 s8
  have s6 : leavesOK ctxLitU 165256250000 0 ((leaves.drop 31212).take 188) 166668750000 0 = true :=
    take_step (n := 2) (t := 188) (b := 31214) rfl rfl ArealUCore.ArealUK.chunk_15606 s7
  have s5 : leavesOK ctxLitU 165243750000 0 ((leaves.drop 31210).take 190) 166668750000 0 = true :=
    take_step (n := 2) (t := 190) (b := 31212) rfl rfl ArealUCore.ArealUK.chunk_15605 s6
  have s4 : leavesOK ctxLitU 165231250000 0 ((leaves.drop 31208).take 192) 166668750000 0 = true :=
    take_step (n := 2) (t := 192) (b := 31210) rfl rfl ArealUCore.ArealUK.chunk_15604 s5
  have s3 : leavesOK ctxLitU 165212500000 0 ((leaves.drop 31206).take 194) 166668750000 0 = true :=
    take_step (n := 2) (t := 194) (b := 31208) rfl rfl ArealUCore.ArealUK.chunk_15603 s4
  have s2 : leavesOK ctxLitU 165193750000 0 ((leaves.drop 31204).take 196) 166668750000 0 = true :=
    take_step (n := 2) (t := 196) (b := 31206) rfl rfl ArealUCore.ArealUK.chunk_15602 s3
  have s1 : leavesOK ctxLitU 165181250000 0 ((leaves.drop 31202).take 198) 166668750000 0 = true :=
    take_step (n := 2) (t := 198) (b := 31204) rfl rfl ArealUCore.ArealUK.chunk_15601 s2
  have s0 : leavesOK ctxLitU 165162500000 0 ((leaves.drop 31200).take 200) 166668750000 0 = true :=
    take_step (n := 2) (t := 200) (b := 31202) rfl rfl ArealUCore.ArealUK.chunk_15600 s1
  exact s0

end Areal.UCert

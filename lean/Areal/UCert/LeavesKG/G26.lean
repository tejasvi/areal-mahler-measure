import ArealUK.Chunk2600
import ArealUK.Chunk2601
import ArealUK.Chunk2602
import ArealUK.Chunk2603
import ArealUK.Chunk2604
import ArealUK.Chunk2605
import ArealUK.Chunk2606
import ArealUK.Chunk2607
import ArealUK.Chunk2608
import ArealUK.Chunk2609
import ArealUK.Chunk2610
import ArealUK.Chunk2611
import ArealUK.Chunk2612
import ArealUK.Chunk2613
import ArealUK.Chunk2614
import ArealUK.Chunk2615
import ArealUK.Chunk2616
import ArealUK.Chunk2617
import ArealUK.Chunk2618
import ArealUK.Chunk2619
import ArealUK.Chunk2620
import ArealUK.Chunk2621
import ArealUK.Chunk2622
import ArealUK.Chunk2623
import ArealUK.Chunk2624
import ArealUK.Chunk2625
import ArealUK.Chunk2626
import ArealUK.Chunk2627
import ArealUK.Chunk2628
import ArealUK.Chunk2629
import ArealUK.Chunk2630
import ArealUK.Chunk2631
import ArealUK.Chunk2632
import ArealUK.Chunk2633
import ArealUK.Chunk2634
import ArealUK.Chunk2635
import ArealUK.Chunk2636
import ArealUK.Chunk2637
import ArealUK.Chunk2638
import ArealUK.Chunk2639
import ArealUK.Chunk2640
import ArealUK.Chunk2641
import ArealUK.Chunk2642
import ArealUK.Chunk2643
import ArealUK.Chunk2644
import ArealUK.Chunk2645
import ArealUK.Chunk2646
import ArealUK.Chunk2647
import ArealUK.Chunk2648
import ArealUK.Chunk2649
import ArealUK.Chunk2650
import ArealUK.Chunk2651
import ArealUK.Chunk2652
import ArealUK.Chunk2653
import ArealUK.Chunk2654
import ArealUK.Chunk2655
import ArealUK.Chunk2656
import ArealUK.Chunk2657
import ArealUK.Chunk2658
import ArealUK.Chunk2659
import ArealUK.Chunk2660
import ArealUK.Chunk2661
import ArealUK.Chunk2662
import ArealUK.Chunk2663
import ArealUK.Chunk2664
import ArealUK.Chunk2665
import ArealUK.Chunk2666
import ArealUK.Chunk2667
import ArealUK.Chunk2668
import ArealUK.Chunk2669
import ArealUK.Chunk2670
import ArealUK.Chunk2671
import ArealUK.Chunk2672
import ArealUK.Chunk2673
import ArealUK.Chunk2674
import ArealUK.Chunk2675
import ArealUK.Chunk2676
import ArealUK.Chunk2677
import ArealUK.Chunk2678
import ArealUK.Chunk2679
import ArealUK.Chunk2680
import ArealUK.Chunk2681
import ArealUK.Chunk2682
import ArealUK.Chunk2683
import ArealUK.Chunk2684
import ArealUK.Chunk2685
import ArealUK.Chunk2686
import ArealUK.Chunk2687
import ArealUK.Chunk2688
import ArealUK.Chunk2689
import ArealUK.Chunk2690
import ArealUK.Chunk2691
import ArealUK.Chunk2692
import ArealUK.Chunk2693
import ArealUK.Chunk2694
import ArealUK.Chunk2695
import ArealUK.Chunk2696
import ArealUK.Chunk2697
import ArealUK.Chunk2698
import ArealUK.Chunk2699
import Areal.UCert.LeavesKGen

/-! Group 26 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_26 : leavesOK ctxLitU 65043750000 2 ((leaves.drop 5200).take 200) 66518750000 2 = true := by
  have s99 := ArealUCore.ArealUK.chunk_2699
  have s98 : leavesOK ctxLitU 132987500000 3 ((leaves.drop 5396).take 4) 66518750000 2 = true :=
    take_step (n := 2) (t := 4) (b := 5398) rfl rfl ArealUCore.ArealUK.chunk_2698 s99
  have s97 : leavesOK ctxLitU 132962500000 3 ((leaves.drop 5394).take 6) 66518750000 2 = true :=
    take_step (n := 2) (t := 6) (b := 5396) rfl rfl ArealUCore.ArealUK.chunk_2697 s98
  have s96 : leavesOK ctxLitU 132937500000 3 ((leaves.drop 5392).take 8) 66518750000 2 = true :=
    take_step (n := 2) (t := 8) (b := 5394) rfl rfl ArealUCore.ArealUK.chunk_2696 s97
  have s95 : leavesOK ctxLitU 132912500000 3 ((leaves.drop 5390).take 10) 66518750000 2 = true :=
    take_step (n := 2) (t := 10) (b := 5392) rfl rfl ArealUCore.ArealUK.chunk_2695 s96
  have s94 : leavesOK ctxLitU 132887500000 3 ((leaves.drop 5388).take 12) 66518750000 2 = true :=
    take_step (n := 2) (t := 12) (b := 5390) rfl rfl ArealUCore.ArealUK.chunk_2694 s95
  have s93 : leavesOK ctxLitU 132862500000 3 ((leaves.drop 5386).take 14) 66518750000 2 = true :=
    take_step (n := 2) (t := 14) (b := 5388) rfl rfl ArealUCore.ArealUK.chunk_2693 s94
  have s92 : leavesOK ctxLitU 132837500000 3 ((leaves.drop 5384).take 16) 66518750000 2 = true :=
    take_step (n := 2) (t := 16) (b := 5386) rfl rfl ArealUCore.ArealUK.chunk_2692 s93
  have s91 : leavesOK ctxLitU 132812500000 3 ((leaves.drop 5382).take 18) 66518750000 2 = true :=
    take_step (n := 2) (t := 18) (b := 5384) rfl rfl ArealUCore.ArealUK.chunk_2691 s92
  have s90 : leavesOK ctxLitU 265575000000 4 ((leaves.drop 5380).take 20) 66518750000 2 = true :=
    take_step (n := 2) (t := 20) (b := 5382) rfl rfl ArealUCore.ArealUK.chunk_2690 s91
  have s89 : leavesOK ctxLitU 265525000000 4 ((leaves.drop 5378).take 22) 66518750000 2 = true :=
    take_step (n := 2) (t := 22) (b := 5380) rfl rfl ArealUCore.ArealUK.chunk_2689 s90
  have s88 : leavesOK ctxLitU 265475000000 4 ((leaves.drop 5376).take 24) 66518750000 2 = true :=
    take_step (n := 2) (t := 24) (b := 5378) rfl rfl ArealUCore.ArealUK.chunk_2688 s89
  have s87 : leavesOK ctxLitU 265425000000 4 ((leaves.drop 5374).take 26) 66518750000 2 = true :=
    take_step (n := 2) (t := 26) (b := 5376) rfl rfl ArealUCore.ArealUK.chunk_2687 s88
  have s86 : leavesOK ctxLitU 265375000000 4 ((leaves.drop 5372).take 28) 66518750000 2 = true :=
    take_step (n := 2) (t := 28) (b := 5374) rfl rfl ArealUCore.ArealUK.chunk_2686 s87
  have s85 : leavesOK ctxLitU 265325000000 4 ((leaves.drop 5370).take 30) 66518750000 2 = true :=
    take_step (n := 2) (t := 30) (b := 5372) rfl rfl ArealUCore.ArealUK.chunk_2685 s86
  have s84 : leavesOK ctxLitU 265275000000 4 ((leaves.drop 5368).take 32) 66518750000 2 = true :=
    take_step (n := 2) (t := 32) (b := 5370) rfl rfl ArealUCore.ArealUK.chunk_2684 s85
  have s83 : leavesOK ctxLitU 265225000000 4 ((leaves.drop 5366).take 34) 66518750000 2 = true :=
    take_step (n := 2) (t := 34) (b := 5368) rfl rfl ArealUCore.ArealUK.chunk_2683 s84
  have s82 : leavesOK ctxLitU 265175000000 4 ((leaves.drop 5364).take 36) 66518750000 2 = true :=
    take_step (n := 2) (t := 36) (b := 5366) rfl rfl ArealUCore.ArealUK.chunk_2682 s83
  have s81 : leavesOK ctxLitU 265125000000 4 ((leaves.drop 5362).take 38) 66518750000 2 = true :=
    take_step (n := 2) (t := 38) (b := 5364) rfl rfl ArealUCore.ArealUK.chunk_2681 s82
  have s80 : leavesOK ctxLitU 265075000000 4 ((leaves.drop 5360).take 40) 66518750000 2 = true :=
    take_step (n := 2) (t := 40) (b := 5362) rfl rfl ArealUCore.ArealUK.chunk_2680 s81
  have s79 : leavesOK ctxLitU 265025000000 4 ((leaves.drop 5358).take 42) 66518750000 2 = true :=
    take_step (n := 2) (t := 42) (b := 5360) rfl rfl ArealUCore.ArealUK.chunk_2679 s80
  have s78 : leavesOK ctxLitU 264975000000 4 ((leaves.drop 5356).take 44) 66518750000 2 = true :=
    take_step (n := 2) (t := 44) (b := 5358) rfl rfl ArealUCore.ArealUK.chunk_2678 s79
  have s77 : leavesOK ctxLitU 264925000000 4 ((leaves.drop 5354).take 46) 66518750000 2 = true :=
    take_step (n := 2) (t := 46) (b := 5356) rfl rfl ArealUCore.ArealUK.chunk_2677 s78
  have s76 : leavesOK ctxLitU 264875000000 4 ((leaves.drop 5352).take 48) 66518750000 2 = true :=
    take_step (n := 2) (t := 48) (b := 5354) rfl rfl ArealUCore.ArealUK.chunk_2676 s77
  have s75 : leavesOK ctxLitU 264825000000 4 ((leaves.drop 5350).take 50) 66518750000 2 = true :=
    take_step (n := 2) (t := 50) (b := 5352) rfl rfl ArealUCore.ArealUK.chunk_2675 s76
  have s74 : leavesOK ctxLitU 132387500000 3 ((leaves.drop 5348).take 52) 66518750000 2 = true :=
    take_step (n := 2) (t := 52) (b := 5350) rfl rfl ArealUCore.ArealUK.chunk_2674 s75
  have s73 : leavesOK ctxLitU 132362500000 3 ((leaves.drop 5346).take 54) 66518750000 2 = true :=
    take_step (n := 2) (t := 54) (b := 5348) rfl rfl ArealUCore.ArealUK.chunk_2673 s74
  have s72 : leavesOK ctxLitU 132337500000 3 ((leaves.drop 5344).take 56) 66518750000 2 = true :=
    take_step (n := 2) (t := 56) (b := 5346) rfl rfl ArealUCore.ArealUK.chunk_2672 s73
  have s71 : leavesOK ctxLitU 132312500000 3 ((leaves.drop 5342).take 58) 66518750000 2 = true :=
    take_step (n := 2) (t := 58) (b := 5344) rfl rfl ArealUCore.ArealUK.chunk_2671 s72
  have s70 : leavesOK ctxLitU 132287500000 3 ((leaves.drop 5340).take 60) 66518750000 2 = true :=
    take_step (n := 2) (t := 60) (b := 5342) rfl rfl ArealUCore.ArealUK.chunk_2670 s71
  have s69 : leavesOK ctxLitU 132262500000 3 ((leaves.drop 5338).take 62) 66518750000 2 = true :=
    take_step (n := 2) (t := 62) (b := 5340) rfl rfl ArealUCore.ArealUK.chunk_2669 s70
  have s68 : leavesOK ctxLitU 132237500000 3 ((leaves.drop 5336).take 64) 66518750000 2 = true :=
    take_step (n := 2) (t := 64) (b := 5338) rfl rfl ArealUCore.ArealUK.chunk_2668 s69
  have s67 : leavesOK ctxLitU 132212500000 3 ((leaves.drop 5334).take 66) 66518750000 2 = true :=
    take_step (n := 2) (t := 66) (b := 5336) rfl rfl ArealUCore.ArealUK.chunk_2667 s68
  have s66 : leavesOK ctxLitU 66093750000 2 ((leaves.drop 5332).take 68) 66518750000 2 = true :=
    take_step (n := 2) (t := 68) (b := 5334) rfl rfl ArealUCore.ArealUK.chunk_2666 s67
  have s65 : leavesOK ctxLitU 66081250000 2 ((leaves.drop 5330).take 70) 66518750000 2 = true :=
    take_step (n := 2) (t := 70) (b := 5332) rfl rfl ArealUCore.ArealUK.chunk_2665 s66
  have s64 : leavesOK ctxLitU 66068750000 2 ((leaves.drop 5328).take 72) 66518750000 2 = true :=
    take_step (n := 2) (t := 72) (b := 5330) rfl rfl ArealUCore.ArealUK.chunk_2664 s65
  have s63 : leavesOK ctxLitU 132125000000 3 ((leaves.drop 5326).take 74) 66518750000 2 = true :=
    take_step (n := 2) (t := 74) (b := 5328) rfl rfl ArealUCore.ArealUK.chunk_2663 s64
  have s62 : leavesOK ctxLitU 132106250000 3 ((leaves.drop 5324).take 76) 66518750000 2 = true :=
    take_step (n := 2) (t := 76) (b := 5326) rfl rfl ArealUCore.ArealUK.chunk_2662 s63
  have s61 : leavesOK ctxLitU 66043750000 2 ((leaves.drop 5322).take 78) 66518750000 2 = true :=
    take_step (n := 2) (t := 78) (b := 5324) rfl rfl ArealUCore.ArealUK.chunk_2661 s62
  have s60 : leavesOK ctxLitU 33012500000 1 ((leaves.drop 5320).take 80) 66518750000 2 = true :=
    take_step (n := 2) (t := 80) (b := 5322) rfl rfl ArealUCore.ArealUK.chunk_2660 s61
  have s59 : leavesOK ctxLitU 16493750000 0 ((leaves.drop 5318).take 82) 66518750000 2 = true :=
    take_step (n := 2) (t := 82) (b := 5320) rfl rfl ArealUCore.ArealUK.chunk_2659 s60
  have s58 : leavesOK ctxLitU 16481250000 0 ((leaves.drop 5316).take 84) 66518750000 2 = true :=
    take_step (n := 2) (t := 84) (b := 5318) rfl rfl ArealUCore.ArealUK.chunk_2658 s59
  have s57 : leavesOK ctxLitU 67487516197114 12 ((leaves.drop 5314).take 86) 66518750000 2 = true :=
    take_step (n := 2) (t := 86) (b := 5316) rfl rfl ArealUCore.ArealUK.chunk_2657 s58
  have s56 : leavesOK ctxLitU 16468750000 0 ((leaves.drop 5312).take 88) 66518750000 2 = true :=
    take_step (n := 2) (t := 88) (b := 5314) rfl rfl ArealUCore.ArealUK.chunk_2656 s57
  have s55 : leavesOK ctxLitU 16456250000 0 ((leaves.drop 5310).take 90) 66518750000 2 = true :=
    take_step (n := 2) (t := 90) (b := 5312) rfl rfl ArealUCore.ArealUK.chunk_2655 s56
  have s54 : leavesOK ctxLitU 32893750000 1 ((leaves.drop 5308).take 92) 66518750000 2 = true :=
    take_step (n := 2) (t := 92) (b := 5310) rfl rfl ArealUCore.ArealUK.chunk_2654 s55
  have s53 : leavesOK ctxLitU 65775000000 2 ((leaves.drop 5306).take 94) 66518750000 2 = true :=
    take_step (n := 2) (t := 94) (b := 5308) rfl rfl ArealUCore.ArealUK.chunk_2653 s54
  have s52 : leavesOK ctxLitU 131537500000 3 ((leaves.drop 5304).take 96) 66518750000 2 = true :=
    take_step (n := 2) (t := 96) (b := 5306) rfl rfl ArealUCore.ArealUK.chunk_2652 s53
  have s51 : leavesOK ctxLitU 65756250000 2 ((leaves.drop 5302).take 98) 66518750000 2 = true :=
    take_step (n := 2) (t := 98) (b := 5304) rfl rfl ArealUCore.ArealUK.chunk_2651 s52
  have s50 : leavesOK ctxLitU 65743750000 2 ((leaves.drop 5300).take 100) 66518750000 2 = true :=
    take_step (n := 2) (t := 100) (b := 5302) rfl rfl ArealUCore.ArealUK.chunk_2650 s51
  have s49 : leavesOK ctxLitU 65731250000 2 ((leaves.drop 5298).take 102) 66518750000 2 = true :=
    take_step (n := 2) (t := 102) (b := 5300) rfl rfl ArealUCore.ArealUK.chunk_2649 s50
  have s48 : leavesOK ctxLitU 65718750000 2 ((leaves.drop 5296).take 104) 66518750000 2 = true :=
    take_step (n := 2) (t := 104) (b := 5298) rfl rfl ArealUCore.ArealUK.chunk_2648 s49
  have s47 : leavesOK ctxLitU 65706250000 2 ((leaves.drop 5294).take 106) 66518750000 2 = true :=
    take_step (n := 2) (t := 106) (b := 5296) rfl rfl ArealUCore.ArealUK.chunk_2647 s48
  have s46 : leavesOK ctxLitU 131387500000 3 ((leaves.drop 5292).take 108) 66518750000 2 = true :=
    take_step (n := 2) (t := 108) (b := 5294) rfl rfl ArealUCore.ArealUK.chunk_2646 s47
  have s45 : leavesOK ctxLitU 131362500000 3 ((leaves.drop 5290).take 110) 66518750000 2 = true :=
    take_step (n := 2) (t := 110) (b := 5292) rfl rfl ArealUCore.ArealUK.chunk_2645 s46
  have s44 : leavesOK ctxLitU 131337500000 3 ((leaves.drop 5288).take 112) 66518750000 2 = true :=
    take_step (n := 2) (t := 112) (b := 5290) rfl rfl ArealUCore.ArealUK.chunk_2644 s45
  have s43 : leavesOK ctxLitU 131312500000 3 ((leaves.drop 5286).take 114) 66518750000 2 = true :=
    take_step (n := 2) (t := 114) (b := 5288) rfl rfl ArealUCore.ArealUK.chunk_2643 s44
  have s42 : leavesOK ctxLitU 131287500000 3 ((leaves.drop 5284).take 116) 66518750000 2 = true :=
    take_step (n := 2) (t := 116) (b := 5286) rfl rfl ArealUCore.ArealUK.chunk_2642 s43
  have s41 : leavesOK ctxLitU 131262500000 3 ((leaves.drop 5282).take 118) 66518750000 2 = true :=
    take_step (n := 2) (t := 118) (b := 5284) rfl rfl ArealUCore.ArealUK.chunk_2641 s42
  have s40 : leavesOK ctxLitU 131237500000 3 ((leaves.drop 5280).take 120) 66518750000 2 = true :=
    take_step (n := 2) (t := 120) (b := 5282) rfl rfl ArealUCore.ArealUK.chunk_2640 s41
  have s39 : leavesOK ctxLitU 131212500000 3 ((leaves.drop 5278).take 122) 66518750000 2 = true :=
    take_step (n := 2) (t := 122) (b := 5280) rfl rfl ArealUCore.ArealUK.chunk_2639 s40
  have s38 : leavesOK ctxLitU 131187500000 3 ((leaves.drop 5276).take 124) 66518750000 2 = true :=
    take_step (n := 2) (t := 124) (b := 5278) rfl rfl ArealUCore.ArealUK.chunk_2638 s39
  have s37 : leavesOK ctxLitU 131162500000 3 ((leaves.drop 5274).take 126) 66518750000 2 = true :=
    take_step (n := 2) (t := 126) (b := 5276) rfl rfl ArealUCore.ArealUK.chunk_2637 s38
  have s36 : leavesOK ctxLitU 131137500000 3 ((leaves.drop 5272).take 128) 66518750000 2 = true :=
    take_step (n := 2) (t := 128) (b := 5274) rfl rfl ArealUCore.ArealUK.chunk_2636 s37
  have s35 : leavesOK ctxLitU 131112500000 3 ((leaves.drop 5270).take 130) 66518750000 2 = true :=
    take_step (n := 2) (t := 130) (b := 5272) rfl rfl ArealUCore.ArealUK.chunk_2635 s36
  have s34 : leavesOK ctxLitU 131087500000 3 ((leaves.drop 5268).take 132) 66518750000 2 = true :=
    take_step (n := 2) (t := 132) (b := 5270) rfl rfl ArealUCore.ArealUK.chunk_2634 s35
  have s33 : leavesOK ctxLitU 131062500000 3 ((leaves.drop 5266).take 134) 66518750000 2 = true :=
    take_step (n := 2) (t := 134) (b := 5268) rfl rfl ArealUCore.ArealUK.chunk_2633 s34
  have s32 : leavesOK ctxLitU 131037500000 3 ((leaves.drop 5264).take 136) 66518750000 2 = true :=
    take_step (n := 2) (t := 136) (b := 5266) rfl rfl ArealUCore.ArealUK.chunk_2632 s33
  have s31 : leavesOK ctxLitU 131012500000 3 ((leaves.drop 5262).take 138) 66518750000 2 = true :=
    take_step (n := 2) (t := 138) (b := 5264) rfl rfl ArealUCore.ArealUK.chunk_2631 s32
  have s30 : leavesOK ctxLitU 65493750000 2 ((leaves.drop 5260).take 140) 66518750000 2 = true :=
    take_step (n := 2) (t := 140) (b := 5262) rfl rfl ArealUCore.ArealUK.chunk_2630 s31
  have s29 : leavesOK ctxLitU 130968750000 3 ((leaves.drop 5258).take 142) 66518750000 2 = true :=
    take_step (n := 2) (t := 142) (b := 5260) rfl rfl ArealUCore.ArealUK.chunk_2629 s30
  have s28 : leavesOK ctxLitU 130956250000 3 ((leaves.drop 5256).take 144) 66518750000 2 = true :=
    take_step (n := 2) (t := 144) (b := 5258) rfl rfl ArealUCore.ArealUK.chunk_2628 s29
  have s27 : leavesOK ctxLitU 130943750000 3 ((leaves.drop 5254).take 146) 66518750000 2 = true :=
    take_step (n := 2) (t := 146) (b := 5256) rfl rfl ArealUCore.ArealUK.chunk_2627 s28
  have s26 : leavesOK ctxLitU 65462500000 2 ((leaves.drop 5252).take 148) 66518750000 2 = true :=
    take_step (n := 2) (t := 148) (b := 5254) rfl rfl ArealUCore.ArealUK.chunk_2626 s27
  have s25 : leavesOK ctxLitU 65450000000 2 ((leaves.drop 5250).take 150) 66518750000 2 = true :=
    take_step (n := 2) (t := 150) (b := 5252) rfl rfl ArealUCore.ArealUK.chunk_2625 s26
  have s24 : leavesOK ctxLitU 65437500000 2 ((leaves.drop 5248).take 152) 66518750000 2 = true :=
    take_step (n := 2) (t := 152) (b := 5250) rfl rfl ArealUCore.ArealUK.chunk_2624 s25
  have s23 : leavesOK ctxLitU 65425000000 2 ((leaves.drop 5246).take 154) 66518750000 2 = true :=
    take_step (n := 2) (t := 154) (b := 5248) rfl rfl ArealUCore.ArealUK.chunk_2623 s24
  have s22 : leavesOK ctxLitU 130831250000 3 ((leaves.drop 5244).take 156) 66518750000 2 = true :=
    take_step (n := 2) (t := 156) (b := 5246) rfl rfl ArealUCore.ArealUK.chunk_2622 s23
  have s21 : leavesOK ctxLitU 130818750000 3 ((leaves.drop 5242).take 158) 66518750000 2 = true :=
    take_step (n := 2) (t := 158) (b := 5244) rfl rfl ArealUCore.ArealUK.chunk_2621 s22
  have s20 : leavesOK ctxLitU 65400000000 2 ((leaves.drop 5240).take 160) 66518750000 2 = true :=
    take_step (n := 2) (t := 160) (b := 5242) rfl rfl ArealUCore.ArealUK.chunk_2620 s21
  have s19 : leavesOK ctxLitU 130787500000 3 ((leaves.drop 5238).take 162) 66518750000 2 = true :=
    take_step (n := 2) (t := 162) (b := 5240) rfl rfl ArealUCore.ArealUK.chunk_2619 s20
  have s18 : leavesOK ctxLitU 130775000000 3 ((leaves.drop 5236).take 164) 66518750000 2 = true :=
    take_step (n := 2) (t := 164) (b := 5238) rfl rfl ArealUCore.ArealUK.chunk_2618 s19
  have s17 : leavesOK ctxLitU 65375000000 2 ((leaves.drop 5234).take 166) 66518750000 2 = true :=
    take_step (n := 2) (t := 166) (b := 5236) rfl rfl ArealUCore.ArealUK.chunk_2617 s18
  have s16 : leavesOK ctxLitU 130737500000 3 ((leaves.drop 5232).take 168) 66518750000 2 = true :=
    take_step (n := 2) (t := 168) (b := 5234) rfl rfl ArealUCore.ArealUK.chunk_2616 s17
  have s15 : leavesOK ctxLitU 130725000000 3 ((leaves.drop 5230).take 170) 66518750000 2 = true :=
    take_step (n := 2) (t := 170) (b := 5232) rfl rfl ArealUCore.ArealUK.chunk_2615 s16
  have s14 : leavesOK ctxLitU 130706250000 3 ((leaves.drop 5228).take 172) 66518750000 2 = true :=
    take_step (n := 2) (t := 172) (b := 5230) rfl rfl ArealUCore.ArealUK.chunk_2614 s15
  have s13 : leavesOK ctxLitU 65343750000 2 ((leaves.drop 5226).take 174) 66518750000 2 = true :=
    take_step (n := 2) (t := 174) (b := 5228) rfl rfl ArealUCore.ArealUK.chunk_2613 s14
  have s12 : leavesOK ctxLitU 32662500000 1 ((leaves.drop 5224).take 176) 66518750000 2 = true :=
    take_step (n := 2) (t := 176) (b := 5226) rfl rfl ArealUCore.ArealUK.chunk_2612 s13
  have s11 : leavesOK ctxLitU 66855569961573 12 ((leaves.drop 5222).take 178) 66518750000 2 = true :=
    take_step (n := 2) (t := 178) (b := 5224) rfl rfl ArealUCore.ArealUK.chunk_2611 s12
  have s10 : leavesOK ctxLitU 66841600000000 12 ((leaves.drop 5220).take 180) 66518750000 2 = true :=
    take_step (n := 2) (t := 180) (b := 5222) rfl rfl ArealUCore.ArealUK.chunk_2610 s11
  have s9 : leavesOK ctxLitU 16306250000 0 ((leaves.drop 5218).take 182) 66518750000 2 = true :=
    take_step (n := 2) (t := 182) (b := 5220) rfl rfl ArealUCore.ArealUK.chunk_2609 s10
  have s8 : leavesOK ctxLitU 16293750000 0 ((leaves.drop 5216).take 184) 66518750000 2 = true :=
    take_step (n := 2) (t := 184) (b := 5218) rfl rfl ArealUCore.ArealUK.chunk_2608 s9
  have s7 : leavesOK ctxLitU 66732922948606 12 ((leaves.drop 5214).take 186) 66518750000 2 = true :=
    take_step (n := 2) (t := 186) (b := 5216) rfl rfl ArealUCore.ArealUK.chunk_2607 s8
  have s6 : leavesOK ctxLitU 16281250000 0 ((leaves.drop 5212).take 188) 66518750000 2 = true :=
    take_step (n := 2) (t := 188) (b := 5214) rfl rfl ArealUCore.ArealUK.chunk_2606 s7
  have s5 : leavesOK ctxLitU 32543750000 1 ((leaves.drop 5210).take 190) 66518750000 2 = true :=
    take_step (n := 2) (t := 190) (b := 5212) rfl rfl ArealUCore.ArealUK.chunk_2605 s6
  have s4 : leavesOK ctxLitU 65075000000 2 ((leaves.drop 5208).take 192) 66518750000 2 = true :=
    take_step (n := 2) (t := 192) (b := 5210) rfl rfl ArealUCore.ArealUK.chunk_2604 s5
  have s3 : leavesOK ctxLitU 130137500000 3 ((leaves.drop 5206).take 194) 66518750000 2 = true :=
    take_step (n := 2) (t := 194) (b := 5208) rfl rfl ArealUCore.ArealUK.chunk_2603 s4
  have s2 : leavesOK ctxLitU 130125000000 3 ((leaves.drop 5204).take 196) 66518750000 2 = true :=
    take_step (n := 2) (t := 196) (b := 5206) rfl rfl ArealUCore.ArealUK.chunk_2602 s3
  have s1 : leavesOK ctxLitU 130112500000 3 ((leaves.drop 5202).take 198) 66518750000 2 = true :=
    take_step (n := 2) (t := 198) (b := 5204) rfl rfl ArealUCore.ArealUK.chunk_2601 s2
  have s0 : leavesOK ctxLitU 65043750000 2 ((leaves.drop 5200).take 200) 66518750000 2 = true :=
    take_step (n := 2) (t := 200) (b := 5202) rfl rfl ArealUCore.ArealUK.chunk_2600 s1
  exact s0

end Areal.UCert

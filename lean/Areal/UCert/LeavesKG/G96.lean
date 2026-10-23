import ArealUK.Chunk9600
import ArealUK.Chunk9601
import ArealUK.Chunk9602
import ArealUK.Chunk9603
import ArealUK.Chunk9604
import ArealUK.Chunk9605
import ArealUK.Chunk9606
import ArealUK.Chunk9607
import ArealUK.Chunk9608
import ArealUK.Chunk9609
import ArealUK.Chunk9610
import ArealUK.Chunk9611
import ArealUK.Chunk9612
import ArealUK.Chunk9613
import ArealUK.Chunk9614
import ArealUK.Chunk9615
import ArealUK.Chunk9616
import ArealUK.Chunk9617
import ArealUK.Chunk9618
import ArealUK.Chunk9619
import ArealUK.Chunk9620
import ArealUK.Chunk9621
import ArealUK.Chunk9622
import ArealUK.Chunk9623
import ArealUK.Chunk9624
import ArealUK.Chunk9625
import ArealUK.Chunk9626
import ArealUK.Chunk9627
import ArealUK.Chunk9628
import ArealUK.Chunk9629
import ArealUK.Chunk9630
import ArealUK.Chunk9631
import ArealUK.Chunk9632
import ArealUK.Chunk9633
import ArealUK.Chunk9634
import ArealUK.Chunk9635
import ArealUK.Chunk9636
import ArealUK.Chunk9637
import ArealUK.Chunk9638
import ArealUK.Chunk9639
import ArealUK.Chunk9640
import ArealUK.Chunk9641
import ArealUK.Chunk9642
import ArealUK.Chunk9643
import ArealUK.Chunk9644
import ArealUK.Chunk9645
import ArealUK.Chunk9646
import ArealUK.Chunk9647
import ArealUK.Chunk9648
import ArealUK.Chunk9649
import ArealUK.Chunk9650
import ArealUK.Chunk9651
import ArealUK.Chunk9652
import ArealUK.Chunk9653
import ArealUK.Chunk9654
import ArealUK.Chunk9655
import ArealUK.Chunk9656
import ArealUK.Chunk9657
import ArealUK.Chunk9658
import ArealUK.Chunk9659
import ArealUK.Chunk9660
import ArealUK.Chunk9661
import ArealUK.Chunk9662
import ArealUK.Chunk9663
import ArealUK.Chunk9664
import ArealUK.Chunk9665
import ArealUK.Chunk9666
import ArealUK.Chunk9667
import ArealUK.Chunk9668
import ArealUK.Chunk9669
import ArealUK.Chunk9670
import ArealUK.Chunk9671
import ArealUK.Chunk9672
import ArealUK.Chunk9673
import ArealUK.Chunk9674
import ArealUK.Chunk9675
import ArealUK.Chunk9676
import ArealUK.Chunk9677
import ArealUK.Chunk9678
import ArealUK.Chunk9679
import ArealUK.Chunk9680
import ArealUK.Chunk9681
import ArealUK.Chunk9682
import ArealUK.Chunk9683
import ArealUK.Chunk9684
import ArealUK.Chunk9685
import ArealUK.Chunk9686
import ArealUK.Chunk9687
import ArealUK.Chunk9688
import ArealUK.Chunk9689
import ArealUK.Chunk9690
import ArealUK.Chunk9691
import ArealUK.Chunk9692
import ArealUK.Chunk9693
import ArealUK.Chunk9694
import ArealUK.Chunk9695
import ArealUK.Chunk9696
import ArealUK.Chunk9697
import ArealUK.Chunk9698
import ArealUK.Chunk9699
import Areal.UCert.LeavesKGen

/-! Group 96 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_96 : leavesOK ctxLitU 334875000000 2 ((leaves.drop 19200).take 200) 84850000000 0 = true := by
  have s99 := ArealUCore.ArealUK.chunk_9699
  have s98 : leavesOK ctxLitU 84825000000 0 ((leaves.drop 19396).take 4) 84850000000 0 = true :=
    take_step (n := 2) (t := 4) (b := 19398) rfl rfl ArealUCore.ArealUK.chunk_9698 s99
  have s97 : leavesOK ctxLitU 339287500000 2 ((leaves.drop 19394).take 6) 84850000000 0 = true :=
    take_step (n := 2) (t := 6) (b := 19396) rfl rfl ArealUCore.ArealUK.chunk_9697 s98
  have s96 : leavesOK ctxLitU 339268750000 2 ((leaves.drop 19392).take 8) 84850000000 0 = true :=
    take_step (n := 2) (t := 8) (b := 19394) rfl rfl ArealUCore.ArealUK.chunk_9696 s97
  have s95 : leavesOK ctxLitU 169625000000 1 ((leaves.drop 19390).take 10) 84850000000 0 = true :=
    take_step (n := 2) (t := 10) (b := 19392) rfl rfl ArealUCore.ArealUK.chunk_9695 s96
  have s94 : leavesOK ctxLitU 169612500000 1 ((leaves.drop 19388).take 12) 84850000000 0 = true :=
    take_step (n := 2) (t := 12) (b := 19390) rfl rfl ArealUCore.ArealUK.chunk_9694 s95
  have s93 : leavesOK ctxLitU 339212500000 2 ((leaves.drop 19386).take 14) 84850000000 0 = true :=
    take_step (n := 2) (t := 14) (b := 19388) rfl rfl ArealUCore.ArealUK.chunk_9693 s94
  have s92 : leavesOK ctxLitU 339187500000 2 ((leaves.drop 19384).take 16) 84850000000 0 = true :=
    take_step (n := 2) (t := 16) (b := 19386) rfl rfl ArealUCore.ArealUK.chunk_9692 s93
  have s91 : leavesOK ctxLitU 339162500000 2 ((leaves.drop 19382).take 18) 84850000000 0 = true :=
    take_step (n := 2) (t := 18) (b := 19384) rfl rfl ArealUCore.ArealUK.chunk_9691 s92
  have s90 : leavesOK ctxLitU 339137500000 2 ((leaves.drop 19380).take 20) 84850000000 0 = true :=
    take_step (n := 2) (t := 20) (b := 19382) rfl rfl ArealUCore.ArealUK.chunk_9690 s91
  have s89 : leavesOK ctxLitU 169550000000 1 ((leaves.drop 19378).take 22) 84850000000 0 = true :=
    take_step (n := 2) (t := 22) (b := 19380) rfl rfl ArealUCore.ArealUK.chunk_9689 s90
  have s88 : leavesOK ctxLitU 339050000000 2 ((leaves.drop 19376).take 24) 84850000000 0 = true :=
    take_step (n := 2) (t := 24) (b := 19378) rfl rfl ArealUCore.ArealUK.chunk_9688 s89
  have s87 : leavesOK ctxLitU 339000000000 2 ((leaves.drop 19374).take 26) 84850000000 0 = true :=
    take_step (n := 2) (t := 26) (b := 19376) rfl rfl ArealUCore.ArealUK.chunk_9687 s88
  have s86 : leavesOK ctxLitU 338950000000 2 ((leaves.drop 19372).take 28) 84850000000 0 = true :=
    take_step (n := 2) (t := 28) (b := 19374) rfl rfl ArealUCore.ArealUK.chunk_9686 s87
  have s85 : leavesOK ctxLitU 677850000000 3 ((leaves.drop 19370).take 30) 84850000000 0 = true :=
    take_step (n := 2) (t := 30) (b := 19372) rfl rfl ArealUCore.ArealUK.chunk_9685 s86
  have s84 : leavesOK ctxLitU 677800000000 3 ((leaves.drop 19368).take 32) 84850000000 0 = true :=
    take_step (n := 2) (t := 32) (b := 19370) rfl rfl ArealUCore.ArealUK.chunk_9684 s85
  have s83 : leavesOK ctxLitU 677750000000 3 ((leaves.drop 19366).take 34) 84850000000 0 = true :=
    take_step (n := 2) (t := 34) (b := 19368) rfl rfl ArealUCore.ArealUK.chunk_9683 s84
  have s82 : leavesOK ctxLitU 677700000000 3 ((leaves.drop 19364).take 36) 84850000000 0 = true :=
    take_step (n := 2) (t := 36) (b := 19366) rfl rfl ArealUCore.ArealUK.chunk_9682 s83
  have s81 : leavesOK ctxLitU 677650000000 3 ((leaves.drop 19362).take 38) 84850000000 0 = true :=
    take_step (n := 2) (t := 38) (b := 19364) rfl rfl ArealUCore.ArealUK.chunk_9681 s82
  have s80 : leavesOK ctxLitU 677600000000 3 ((leaves.drop 19360).take 40) 84850000000 0 = true :=
    take_step (n := 2) (t := 40) (b := 19362) rfl rfl ArealUCore.ArealUK.chunk_9680 s81
  have s79 : leavesOK ctxLitU 677525000000 3 ((leaves.drop 19358).take 42) 84850000000 0 = true :=
    take_step (n := 2) (t := 42) (b := 19360) rfl rfl ArealUCore.ArealUK.chunk_9679 s80
  have s78 : leavesOK ctxLitU 677475000000 3 ((leaves.drop 19356).take 44) 84850000000 0 = true :=
    take_step (n := 2) (t := 44) (b := 19358) rfl rfl ArealUCore.ArealUK.chunk_9678 s79
  have s77 : leavesOK ctxLitU 338700000000 2 ((leaves.drop 19354).take 46) 84850000000 0 = true :=
    take_step (n := 2) (t := 46) (b := 19356) rfl rfl ArealUCore.ArealUK.chunk_9677 s78
  have s76 : leavesOK ctxLitU 338650000000 2 ((leaves.drop 19352).take 48) 84850000000 0 = true :=
    take_step (n := 2) (t := 48) (b := 19354) rfl rfl ArealUCore.ArealUK.chunk_9676 s77
  have s75 : leavesOK ctxLitU 338600000000 2 ((leaves.drop 19350).take 50) 84850000000 0 = true :=
    take_step (n := 2) (t := 50) (b := 19352) rfl rfl ArealUCore.ArealUK.chunk_9675 s76
  have s74 : leavesOK ctxLitU 338550000000 2 ((leaves.drop 19348).take 52) 84850000000 0 = true :=
    take_step (n := 2) (t := 52) (b := 19350) rfl rfl ArealUCore.ArealUK.chunk_9674 s75
  have s73 : leavesOK ctxLitU 338500000000 2 ((leaves.drop 19346).take 54) 84850000000 0 = true :=
    take_step (n := 2) (t := 54) (b := 19348) rfl rfl ArealUCore.ArealUK.chunk_9673 s74
  have s72 : leavesOK ctxLitU 338450000000 2 ((leaves.drop 19344).take 56) 84850000000 0 = true :=
    take_step (n := 2) (t := 56) (b := 19346) rfl rfl ArealUCore.ArealUK.chunk_9672 s73
  have s71 : leavesOK ctxLitU 338400000000 2 ((leaves.drop 19342).take 58) 84850000000 0 = true :=
    take_step (n := 2) (t := 58) (b := 19344) rfl rfl ArealUCore.ArealUK.chunk_9671 s72
  have s70 : leavesOK ctxLitU 338350000000 2 ((leaves.drop 19340).take 60) 84850000000 0 = true :=
    take_step (n := 2) (t := 60) (b := 19342) rfl rfl ArealUCore.ArealUK.chunk_9670 s71
  have s69 : leavesOK ctxLitU 676625000000 3 ((leaves.drop 19338).take 62) 84850000000 0 = true :=
    take_step (n := 2) (t := 62) (b := 19340) rfl rfl ArealUCore.ArealUK.chunk_9669 s70
  have s68 : leavesOK ctxLitU 338275000000 2 ((leaves.drop 19336).take 64) 84850000000 0 = true :=
    take_step (n := 2) (t := 64) (b := 19338) rfl rfl ArealUCore.ArealUK.chunk_9668 s69
  have s67 : leavesOK ctxLitU 338225000000 2 ((leaves.drop 19334).take 66) 84850000000 0 = true :=
    take_step (n := 2) (t := 66) (b := 19336) rfl rfl ArealUCore.ArealUK.chunk_9667 s68
  have s66 : leavesOK ctxLitU 338175000000 2 ((leaves.drop 19332).take 68) 84850000000 0 = true :=
    take_step (n := 2) (t := 68) (b := 19334) rfl rfl ArealUCore.ArealUK.chunk_9666 s67
  have s65 : leavesOK ctxLitU 338125000000 2 ((leaves.drop 19330).take 70) 84850000000 0 = true :=
    take_step (n := 2) (t := 70) (b := 19332) rfl rfl ArealUCore.ArealUK.chunk_9665 s66
  have s64 : leavesOK ctxLitU 338075000000 2 ((leaves.drop 19328).take 72) 84850000000 0 = true :=
    take_step (n := 2) (t := 72) (b := 19330) rfl rfl ArealUCore.ArealUK.chunk_9664 s65
  have s63 : leavesOK ctxLitU 338025000000 2 ((leaves.drop 19326).take 74) 84850000000 0 = true :=
    take_step (n := 2) (t := 74) (b := 19328) rfl rfl ArealUCore.ArealUK.chunk_9663 s64
  have s62 : leavesOK ctxLitU 337975000000 2 ((leaves.drop 19324).take 76) 84850000000 0 = true :=
    take_step (n := 2) (t := 76) (b := 19326) rfl rfl ArealUCore.ArealUK.chunk_9662 s63
  have s61 : leavesOK ctxLitU 337925000000 2 ((leaves.drop 19322).take 78) 84850000000 0 = true :=
    take_step (n := 2) (t := 78) (b := 19324) rfl rfl ArealUCore.ArealUK.chunk_9661 s62
  have s60 : leavesOK ctxLitU 337875000000 2 ((leaves.drop 19320).take 80) 84850000000 0 = true :=
    take_step (n := 2) (t := 80) (b := 19322) rfl rfl ArealUCore.ArealUK.chunk_9660 s61
  have s59 : leavesOK ctxLitU 337825000000 2 ((leaves.drop 19318).take 82) 84850000000 0 = true :=
    take_step (n := 2) (t := 82) (b := 19320) rfl rfl ArealUCore.ArealUK.chunk_9659 s60
  have s58 : leavesOK ctxLitU 337775000000 2 ((leaves.drop 19316).take 84) 84850000000 0 = true :=
    take_step (n := 2) (t := 84) (b := 19318) rfl rfl ArealUCore.ArealUK.chunk_9658 s59
  have s57 : leavesOK ctxLitU 337725000000 2 ((leaves.drop 19314).take 86) 84850000000 0 = true :=
    take_step (n := 2) (t := 86) (b := 19316) rfl rfl ArealUCore.ArealUK.chunk_9657 s58
  have s56 : leavesOK ctxLitU 337675000000 2 ((leaves.drop 19312).take 88) 84850000000 0 = true :=
    take_step (n := 2) (t := 88) (b := 19314) rfl rfl ArealUCore.ArealUK.chunk_9656 s57
  have s55 : leavesOK ctxLitU 337625000000 2 ((leaves.drop 19310).take 90) 84850000000 0 = true :=
    take_step (n := 2) (t := 90) (b := 19312) rfl rfl ArealUCore.ArealUK.chunk_9655 s56
  have s54 : leavesOK ctxLitU 337575000000 2 ((leaves.drop 19308).take 92) 84850000000 0 = true :=
    take_step (n := 2) (t := 92) (b := 19310) rfl rfl ArealUCore.ArealUK.chunk_9654 s55
  have s53 : leavesOK ctxLitU 337525000000 2 ((leaves.drop 19306).take 94) 84850000000 0 = true :=
    take_step (n := 2) (t := 94) (b := 19308) rfl rfl ArealUCore.ArealUK.chunk_9653 s54
  have s52 : leavesOK ctxLitU 337475000000 2 ((leaves.drop 19304).take 96) 84850000000 0 = true :=
    take_step (n := 2) (t := 96) (b := 19306) rfl rfl ArealUCore.ArealUK.chunk_9652 s53
  have s51 : leavesOK ctxLitU 337425000000 2 ((leaves.drop 19302).take 98) 84850000000 0 = true :=
    take_step (n := 2) (t := 98) (b := 19304) rfl rfl ArealUCore.ArealUK.chunk_9651 s52
  have s50 : leavesOK ctxLitU 337375000000 2 ((leaves.drop 19300).take 100) 84850000000 0 = true :=
    take_step (n := 2) (t := 100) (b := 19302) rfl rfl ArealUCore.ArealUK.chunk_9650 s51
  have s49 : leavesOK ctxLitU 337325000000 2 ((leaves.drop 19298).take 102) 84850000000 0 = true :=
    take_step (n := 2) (t := 102) (b := 19300) rfl rfl ArealUCore.ArealUK.chunk_9649 s50
  have s48 : leavesOK ctxLitU 337275000000 2 ((leaves.drop 19296).take 104) 84850000000 0 = true :=
    take_step (n := 2) (t := 104) (b := 19298) rfl rfl ArealUCore.ArealUK.chunk_9648 s49
  have s47 : leavesOK ctxLitU 337225000000 2 ((leaves.drop 19294).take 106) 84850000000 0 = true :=
    take_step (n := 2) (t := 106) (b := 19296) rfl rfl ArealUCore.ArealUK.chunk_9647 s48
  have s46 : leavesOK ctxLitU 337175000000 2 ((leaves.drop 19292).take 108) 84850000000 0 = true :=
    take_step (n := 2) (t := 108) (b := 19294) rfl rfl ArealUCore.ArealUK.chunk_9646 s47
  have s45 : leavesOK ctxLitU 337125000000 2 ((leaves.drop 19290).take 110) 84850000000 0 = true :=
    take_step (n := 2) (t := 110) (b := 19292) rfl rfl ArealUCore.ArealUK.chunk_9645 s46
  have s44 : leavesOK ctxLitU 337075000000 2 ((leaves.drop 19288).take 112) 84850000000 0 = true :=
    take_step (n := 2) (t := 112) (b := 19290) rfl rfl ArealUCore.ArealUK.chunk_9644 s45
  have s43 : leavesOK ctxLitU 337025000000 2 ((leaves.drop 19286).take 114) 84850000000 0 = true :=
    take_step (n := 2) (t := 114) (b := 19288) rfl rfl ArealUCore.ArealUK.chunk_9643 s44
  have s42 : leavesOK ctxLitU 336975000000 2 ((leaves.drop 19284).take 116) 84850000000 0 = true :=
    take_step (n := 2) (t := 116) (b := 19286) rfl rfl ArealUCore.ArealUK.chunk_9642 s43
  have s41 : leavesOK ctxLitU 336925000000 2 ((leaves.drop 19282).take 118) 84850000000 0 = true :=
    take_step (n := 2) (t := 118) (b := 19284) rfl rfl ArealUCore.ArealUK.chunk_9641 s42
  have s40 : leavesOK ctxLitU 336875000000 2 ((leaves.drop 19280).take 120) 84850000000 0 = true :=
    take_step (n := 2) (t := 120) (b := 19282) rfl rfl ArealUCore.ArealUK.chunk_9640 s41
  have s39 : leavesOK ctxLitU 336825000000 2 ((leaves.drop 19278).take 122) 84850000000 0 = true :=
    take_step (n := 2) (t := 122) (b := 19280) rfl rfl ArealUCore.ArealUK.chunk_9639 s40
  have s38 : leavesOK ctxLitU 336775000000 2 ((leaves.drop 19276).take 124) 84850000000 0 = true :=
    take_step (n := 2) (t := 124) (b := 19278) rfl rfl ArealUCore.ArealUK.chunk_9638 s39
  have s37 : leavesOK ctxLitU 336725000000 2 ((leaves.drop 19274).take 126) 84850000000 0 = true :=
    take_step (n := 2) (t := 126) (b := 19276) rfl rfl ArealUCore.ArealUK.chunk_9637 s38
  have s36 : leavesOK ctxLitU 336675000000 2 ((leaves.drop 19272).take 128) 84850000000 0 = true :=
    take_step (n := 2) (t := 128) (b := 19274) rfl rfl ArealUCore.ArealUK.chunk_9636 s37
  have s35 : leavesOK ctxLitU 336625000000 2 ((leaves.drop 19270).take 130) 84850000000 0 = true :=
    take_step (n := 2) (t := 130) (b := 19272) rfl rfl ArealUCore.ArealUK.chunk_9635 s36
  have s34 : leavesOK ctxLitU 336575000000 2 ((leaves.drop 19268).take 132) 84850000000 0 = true :=
    take_step (n := 2) (t := 132) (b := 19270) rfl rfl ArealUCore.ArealUK.chunk_9634 s35
  have s33 : leavesOK ctxLitU 336525000000 2 ((leaves.drop 19266).take 134) 84850000000 0 = true :=
    take_step (n := 2) (t := 134) (b := 19268) rfl rfl ArealUCore.ArealUK.chunk_9633 s34
  have s32 : leavesOK ctxLitU 336475000000 2 ((leaves.drop 19264).take 136) 84850000000 0 = true :=
    take_step (n := 2) (t := 136) (b := 19266) rfl rfl ArealUCore.ArealUK.chunk_9632 s33
  have s31 : leavesOK ctxLitU 336425000000 2 ((leaves.drop 19262).take 138) 84850000000 0 = true :=
    take_step (n := 2) (t := 138) (b := 19264) rfl rfl ArealUCore.ArealUK.chunk_9631 s32
  have s30 : leavesOK ctxLitU 336375000000 2 ((leaves.drop 19260).take 140) 84850000000 0 = true :=
    take_step (n := 2) (t := 140) (b := 19262) rfl rfl ArealUCore.ArealUK.chunk_9630 s31
  have s29 : leavesOK ctxLitU 336325000000 2 ((leaves.drop 19258).take 142) 84850000000 0 = true :=
    take_step (n := 2) (t := 142) (b := 19260) rfl rfl ArealUCore.ArealUK.chunk_9629 s30
  have s28 : leavesOK ctxLitU 336275000000 2 ((leaves.drop 19256).take 144) 84850000000 0 = true :=
    take_step (n := 2) (t := 144) (b := 19258) rfl rfl ArealUCore.ArealUK.chunk_9628 s29
  have s27 : leavesOK ctxLitU 336225000000 2 ((leaves.drop 19254).take 146) 84850000000 0 = true :=
    take_step (n := 2) (t := 146) (b := 19256) rfl rfl ArealUCore.ArealUK.chunk_9627 s28
  have s26 : leavesOK ctxLitU 336175000000 2 ((leaves.drop 19252).take 148) 84850000000 0 = true :=
    take_step (n := 2) (t := 148) (b := 19254) rfl rfl ArealUCore.ArealUK.chunk_9626 s27
  have s25 : leavesOK ctxLitU 336125000000 2 ((leaves.drop 19250).take 150) 84850000000 0 = true :=
    take_step (n := 2) (t := 150) (b := 19252) rfl rfl ArealUCore.ArealUK.chunk_9625 s26
  have s24 : leavesOK ctxLitU 336075000000 2 ((leaves.drop 19248).take 152) 84850000000 0 = true :=
    take_step (n := 2) (t := 152) (b := 19250) rfl rfl ArealUCore.ArealUK.chunk_9624 s25
  have s23 : leavesOK ctxLitU 336025000000 2 ((leaves.drop 19246).take 154) 84850000000 0 = true :=
    take_step (n := 2) (t := 154) (b := 19248) rfl rfl ArealUCore.ArealUK.chunk_9623 s24
  have s22 : leavesOK ctxLitU 335975000000 2 ((leaves.drop 19244).take 156) 84850000000 0 = true :=
    take_step (n := 2) (t := 156) (b := 19246) rfl rfl ArealUCore.ArealUK.chunk_9622 s23
  have s21 : leavesOK ctxLitU 335925000000 2 ((leaves.drop 19242).take 158) 84850000000 0 = true :=
    take_step (n := 2) (t := 158) (b := 19244) rfl rfl ArealUCore.ArealUK.chunk_9621 s22
  have s20 : leavesOK ctxLitU 335875000000 2 ((leaves.drop 19240).take 160) 84850000000 0 = true :=
    take_step (n := 2) (t := 160) (b := 19242) rfl rfl ArealUCore.ArealUK.chunk_9620 s21
  have s19 : leavesOK ctxLitU 335825000000 2 ((leaves.drop 19238).take 162) 84850000000 0 = true :=
    take_step (n := 2) (t := 162) (b := 19240) rfl rfl ArealUCore.ArealUK.chunk_9619 s20
  have s18 : leavesOK ctxLitU 335775000000 2 ((leaves.drop 19236).take 164) 84850000000 0 = true :=
    take_step (n := 2) (t := 164) (b := 19238) rfl rfl ArealUCore.ArealUK.chunk_9618 s19
  have s17 : leavesOK ctxLitU 335725000000 2 ((leaves.drop 19234).take 166) 84850000000 0 = true :=
    take_step (n := 2) (t := 166) (b := 19236) rfl rfl ArealUCore.ArealUK.chunk_9617 s18
  have s16 : leavesOK ctxLitU 335675000000 2 ((leaves.drop 19232).take 168) 84850000000 0 = true :=
    take_step (n := 2) (t := 168) (b := 19234) rfl rfl ArealUCore.ArealUK.chunk_9616 s17
  have s15 : leavesOK ctxLitU 335625000000 2 ((leaves.drop 19230).take 170) 84850000000 0 = true :=
    take_step (n := 2) (t := 170) (b := 19232) rfl rfl ArealUCore.ArealUK.chunk_9615 s16
  have s14 : leavesOK ctxLitU 335575000000 2 ((leaves.drop 19228).take 172) 84850000000 0 = true :=
    take_step (n := 2) (t := 172) (b := 19230) rfl rfl ArealUCore.ArealUK.chunk_9614 s15
  have s13 : leavesOK ctxLitU 335525000000 2 ((leaves.drop 19226).take 174) 84850000000 0 = true :=
    take_step (n := 2) (t := 174) (b := 19228) rfl rfl ArealUCore.ArealUK.chunk_9613 s14
  have s12 : leavesOK ctxLitU 335475000000 2 ((leaves.drop 19224).take 176) 84850000000 0 = true :=
    take_step (n := 2) (t := 176) (b := 19226) rfl rfl ArealUCore.ArealUK.chunk_9612 s13
  have s11 : leavesOK ctxLitU 335425000000 2 ((leaves.drop 19222).take 178) 84850000000 0 = true :=
    take_step (n := 2) (t := 178) (b := 19224) rfl rfl ArealUCore.ArealUK.chunk_9611 s12
  have s10 : leavesOK ctxLitU 335375000000 2 ((leaves.drop 19220).take 180) 84850000000 0 = true :=
    take_step (n := 2) (t := 180) (b := 19222) rfl rfl ArealUCore.ArealUK.chunk_9610 s11
  have s9 : leavesOK ctxLitU 335325000000 2 ((leaves.drop 19218).take 182) 84850000000 0 = true :=
    take_step (n := 2) (t := 182) (b := 19220) rfl rfl ArealUCore.ArealUK.chunk_9609 s10
  have s8 : leavesOK ctxLitU 335275000000 2 ((leaves.drop 19216).take 184) 84850000000 0 = true :=
    take_step (n := 2) (t := 184) (b := 19218) rfl rfl ArealUCore.ArealUK.chunk_9608 s9
  have s7 : leavesOK ctxLitU 335225000000 2 ((leaves.drop 19214).take 186) 84850000000 0 = true :=
    take_step (n := 2) (t := 186) (b := 19216) rfl rfl ArealUCore.ArealUK.chunk_9607 s8
  have s6 : leavesOK ctxLitU 335175000000 2 ((leaves.drop 19212).take 188) 84850000000 0 = true :=
    take_step (n := 2) (t := 188) (b := 19214) rfl rfl ArealUCore.ArealUK.chunk_9606 s7
  have s5 : leavesOK ctxLitU 335125000000 2 ((leaves.drop 19210).take 190) 84850000000 0 = true :=
    take_step (n := 2) (t := 190) (b := 19212) rfl rfl ArealUCore.ArealUK.chunk_9605 s6
  have s4 : leavesOK ctxLitU 335075000000 2 ((leaves.drop 19208).take 192) 84850000000 0 = true :=
    take_step (n := 2) (t := 192) (b := 19210) rfl rfl ArealUCore.ArealUK.chunk_9604 s5
  have s3 : leavesOK ctxLitU 335025000000 2 ((leaves.drop 19206).take 194) 84850000000 0 = true :=
    take_step (n := 2) (t := 194) (b := 19208) rfl rfl ArealUCore.ArealUK.chunk_9603 s4
  have s2 : leavesOK ctxLitU 334975000000 2 ((leaves.drop 19204).take 196) 84850000000 0 = true :=
    take_step (n := 2) (t := 196) (b := 19206) rfl rfl ArealUCore.ArealUK.chunk_9602 s3
  have s1 : leavesOK ctxLitU 334925000000 2 ((leaves.drop 19202).take 198) 84850000000 0 = true :=
    take_step (n := 2) (t := 198) (b := 19204) rfl rfl ArealUCore.ArealUK.chunk_9601 s2
  have s0 : leavesOK ctxLitU 334875000000 2 ((leaves.drop 19200).take 200) 84850000000 0 = true :=
    take_step (n := 2) (t := 200) (b := 19202) rfl rfl ArealUCore.ArealUK.chunk_9600 s1
  exact s0

end Areal.UCert

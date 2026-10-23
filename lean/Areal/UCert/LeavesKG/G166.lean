import ArealUK.Chunk16600
import ArealUK.Chunk16601
import ArealUK.Chunk16602
import ArealUK.Chunk16603
import ArealUK.Chunk16604
import ArealUK.Chunk16605
import ArealUK.Chunk16606
import ArealUK.Chunk16607
import ArealUK.Chunk16608
import ArealUK.Chunk16609
import ArealUK.Chunk16610
import ArealUK.Chunk16611
import ArealUK.Chunk16612
import ArealUK.Chunk16613
import ArealUK.Chunk16614
import ArealUK.Chunk16615
import ArealUK.Chunk16616
import ArealUK.Chunk16617
import ArealUK.Chunk16618
import ArealUK.Chunk16619
import ArealUK.Chunk16620
import ArealUK.Chunk16621
import ArealUK.Chunk16622
import ArealUK.Chunk16623
import ArealUK.Chunk16624
import ArealUK.Chunk16625
import ArealUK.Chunk16626
import ArealUK.Chunk16627
import ArealUK.Chunk16628
import ArealUK.Chunk16629
import ArealUK.Chunk16630
import ArealUK.Chunk16631
import ArealUK.Chunk16632
import ArealUK.Chunk16633
import ArealUK.Chunk16634
import ArealUK.Chunk16635
import ArealUK.Chunk16636
import ArealUK.Chunk16637
import ArealUK.Chunk16638
import ArealUK.Chunk16639
import ArealUK.Chunk16640
import ArealUK.Chunk16641
import ArealUK.Chunk16642
import ArealUK.Chunk16643
import ArealUK.Chunk16644
import ArealUK.Chunk16645
import ArealUK.Chunk16646
import ArealUK.Chunk16647
import ArealUK.Chunk16648
import ArealUK.Chunk16649
import ArealUK.Chunk16650
import ArealUK.Chunk16651
import ArealUK.Chunk16652
import ArealUK.Chunk16653
import ArealUK.Chunk16654
import ArealUK.Chunk16655
import ArealUK.Chunk16656
import ArealUK.Chunk16657
import ArealUK.Chunk16658
import ArealUK.Chunk16659
import ArealUK.Chunk16660
import ArealUK.Chunk16661
import ArealUK.Chunk16662
import ArealUK.Chunk16663
import ArealUK.Chunk16664
import ArealUK.Chunk16665
import ArealUK.Chunk16666
import ArealUK.Chunk16667
import ArealUK.Chunk16668
import ArealUK.Chunk16669
import ArealUK.Chunk16670
import ArealUK.Chunk16671
import ArealUK.Chunk16672
import ArealUK.Chunk16673
import ArealUK.Chunk16674
import ArealUK.Chunk16675
import ArealUK.Chunk16676
import ArealUK.Chunk16677
import ArealUK.Chunk16678
import ArealUK.Chunk16679
import ArealUK.Chunk16680
import ArealUK.Chunk16681
import ArealUK.Chunk16682
import ArealUK.Chunk16683
import ArealUK.Chunk16684
import ArealUK.Chunk16685
import ArealUK.Chunk16686
import ArealUK.Chunk16687
import ArealUK.Chunk16688
import ArealUK.Chunk16689
import ArealUK.Chunk16690
import ArealUK.Chunk16691
import ArealUK.Chunk16692
import ArealUK.Chunk16693
import ArealUK.Chunk16694
import ArealUK.Chunk16695
import ArealUK.Chunk16696
import ArealUK.Chunk16697
import ArealUK.Chunk16698
import ArealUK.Chunk16699
import Areal.UCert.LeavesKGen

/-! Group 166 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_166 : leavesOK ctxLitU 193300000000 0 ((leaves.drop 33200).take 200) 198300000000 0 = true := by
  have s99 := ArealUCore.ArealUK.chunk_16699
  have s98 : leavesOK ctxLitU 198200000000 0 ((leaves.drop 33396).take 4) 198300000000 0 = true :=
    take_step (n := 2) (t := 4) (b := 33398) rfl rfl ArealUCore.ArealUK.chunk_16698 s99
  have s97 : leavesOK ctxLitU 198150000000 0 ((leaves.drop 33394).take 6) 198300000000 0 = true :=
    take_step (n := 2) (t := 6) (b := 33396) rfl rfl ArealUCore.ArealUK.chunk_16697 s98
  have s96 : leavesOK ctxLitU 198100000000 0 ((leaves.drop 33392).take 8) 198300000000 0 = true :=
    take_step (n := 2) (t := 8) (b := 33394) rfl rfl ArealUCore.ArealUK.chunk_16696 s97
  have s95 : leavesOK ctxLitU 198050000000 0 ((leaves.drop 33390).take 10) 198300000000 0 = true :=
    take_step (n := 2) (t := 10) (b := 33392) rfl rfl ArealUCore.ArealUK.chunk_16695 s96
  have s94 : leavesOK ctxLitU 198000000000 0 ((leaves.drop 33388).take 12) 198300000000 0 = true :=
    take_step (n := 2) (t := 12) (b := 33390) rfl rfl ArealUCore.ArealUK.chunk_16694 s95
  have s93 : leavesOK ctxLitU 197950000000 0 ((leaves.drop 33386).take 14) 198300000000 0 = true :=
    take_step (n := 2) (t := 14) (b := 33388) rfl rfl ArealUCore.ArealUK.chunk_16693 s94
  have s92 : leavesOK ctxLitU 197900000000 0 ((leaves.drop 33384).take 16) 198300000000 0 = true :=
    take_step (n := 2) (t := 16) (b := 33386) rfl rfl ArealUCore.ArealUK.chunk_16692 s93
  have s91 : leavesOK ctxLitU 197850000000 0 ((leaves.drop 33382).take 18) 198300000000 0 = true :=
    take_step (n := 2) (t := 18) (b := 33384) rfl rfl ArealUCore.ArealUK.chunk_16691 s92
  have s90 : leavesOK ctxLitU 197800000000 0 ((leaves.drop 33380).take 20) 198300000000 0 = true :=
    take_step (n := 2) (t := 20) (b := 33382) rfl rfl ArealUCore.ArealUK.chunk_16690 s91
  have s89 : leavesOK ctxLitU 197750000000 0 ((leaves.drop 33378).take 22) 198300000000 0 = true :=
    take_step (n := 2) (t := 22) (b := 33380) rfl rfl ArealUCore.ArealUK.chunk_16689 s90
  have s88 : leavesOK ctxLitU 197700000000 0 ((leaves.drop 33376).take 24) 198300000000 0 = true :=
    take_step (n := 2) (t := 24) (b := 33378) rfl rfl ArealUCore.ArealUK.chunk_16688 s89
  have s87 : leavesOK ctxLitU 197650000000 0 ((leaves.drop 33374).take 26) 198300000000 0 = true :=
    take_step (n := 2) (t := 26) (b := 33376) rfl rfl ArealUCore.ArealUK.chunk_16687 s88
  have s86 : leavesOK ctxLitU 197600000000 0 ((leaves.drop 33372).take 28) 198300000000 0 = true :=
    take_step (n := 2) (t := 28) (b := 33374) rfl rfl ArealUCore.ArealUK.chunk_16686 s87
  have s85 : leavesOK ctxLitU 197550000000 0 ((leaves.drop 33370).take 30) 198300000000 0 = true :=
    take_step (n := 2) (t := 30) (b := 33372) rfl rfl ArealUCore.ArealUK.chunk_16685 s86
  have s84 : leavesOK ctxLitU 197500000000 0 ((leaves.drop 33368).take 32) 198300000000 0 = true :=
    take_step (n := 2) (t := 32) (b := 33370) rfl rfl ArealUCore.ArealUK.chunk_16684 s85
  have s83 : leavesOK ctxLitU 197450000000 0 ((leaves.drop 33366).take 34) 198300000000 0 = true :=
    take_step (n := 2) (t := 34) (b := 33368) rfl rfl ArealUCore.ArealUK.chunk_16683 s84
  have s82 : leavesOK ctxLitU 197400000000 0 ((leaves.drop 33364).take 36) 198300000000 0 = true :=
    take_step (n := 2) (t := 36) (b := 33366) rfl rfl ArealUCore.ArealUK.chunk_16682 s83
  have s81 : leavesOK ctxLitU 197350000000 0 ((leaves.drop 33362).take 38) 198300000000 0 = true :=
    take_step (n := 2) (t := 38) (b := 33364) rfl rfl ArealUCore.ArealUK.chunk_16681 s82
  have s80 : leavesOK ctxLitU 197300000000 0 ((leaves.drop 33360).take 40) 198300000000 0 = true :=
    take_step (n := 2) (t := 40) (b := 33362) rfl rfl ArealUCore.ArealUK.chunk_16680 s81
  have s79 : leavesOK ctxLitU 197250000000 0 ((leaves.drop 33358).take 42) 198300000000 0 = true :=
    take_step (n := 2) (t := 42) (b := 33360) rfl rfl ArealUCore.ArealUK.chunk_16679 s80
  have s78 : leavesOK ctxLitU 197200000000 0 ((leaves.drop 33356).take 44) 198300000000 0 = true :=
    take_step (n := 2) (t := 44) (b := 33358) rfl rfl ArealUCore.ArealUK.chunk_16678 s79
  have s77 : leavesOK ctxLitU 197150000000 0 ((leaves.drop 33354).take 46) 198300000000 0 = true :=
    take_step (n := 2) (t := 46) (b := 33356) rfl rfl ArealUCore.ArealUK.chunk_16677 s78
  have s76 : leavesOK ctxLitU 197100000000 0 ((leaves.drop 33352).take 48) 198300000000 0 = true :=
    take_step (n := 2) (t := 48) (b := 33354) rfl rfl ArealUCore.ArealUK.chunk_16676 s77
  have s75 : leavesOK ctxLitU 197050000000 0 ((leaves.drop 33350).take 50) 198300000000 0 = true :=
    take_step (n := 2) (t := 50) (b := 33352) rfl rfl ArealUCore.ArealUK.chunk_16675 s76
  have s74 : leavesOK ctxLitU 197000000000 0 ((leaves.drop 33348).take 52) 198300000000 0 = true :=
    take_step (n := 2) (t := 52) (b := 33350) rfl rfl ArealUCore.ArealUK.chunk_16674 s75
  have s73 : leavesOK ctxLitU 196950000000 0 ((leaves.drop 33346).take 54) 198300000000 0 = true :=
    take_step (n := 2) (t := 54) (b := 33348) rfl rfl ArealUCore.ArealUK.chunk_16673 s74
  have s72 : leavesOK ctxLitU 196900000000 0 ((leaves.drop 33344).take 56) 198300000000 0 = true :=
    take_step (n := 2) (t := 56) (b := 33346) rfl rfl ArealUCore.ArealUK.chunk_16672 s73
  have s71 : leavesOK ctxLitU 196850000000 0 ((leaves.drop 33342).take 58) 198300000000 0 = true :=
    take_step (n := 2) (t := 58) (b := 33344) rfl rfl ArealUCore.ArealUK.chunk_16671 s72
  have s70 : leavesOK ctxLitU 196800000000 0 ((leaves.drop 33340).take 60) 198300000000 0 = true :=
    take_step (n := 2) (t := 60) (b := 33342) rfl rfl ArealUCore.ArealUK.chunk_16670 s71
  have s69 : leavesOK ctxLitU 196750000000 0 ((leaves.drop 33338).take 62) 198300000000 0 = true :=
    take_step (n := 2) (t := 62) (b := 33340) rfl rfl ArealUCore.ArealUK.chunk_16669 s70
  have s68 : leavesOK ctxLitU 196700000000 0 ((leaves.drop 33336).take 64) 198300000000 0 = true :=
    take_step (n := 2) (t := 64) (b := 33338) rfl rfl ArealUCore.ArealUK.chunk_16668 s69
  have s67 : leavesOK ctxLitU 196650000000 0 ((leaves.drop 33334).take 66) 198300000000 0 = true :=
    take_step (n := 2) (t := 66) (b := 33336) rfl rfl ArealUCore.ArealUK.chunk_16667 s68
  have s66 : leavesOK ctxLitU 196600000000 0 ((leaves.drop 33332).take 68) 198300000000 0 = true :=
    take_step (n := 2) (t := 68) (b := 33334) rfl rfl ArealUCore.ArealUK.chunk_16666 s67
  have s65 : leavesOK ctxLitU 196550000000 0 ((leaves.drop 33330).take 70) 198300000000 0 = true :=
    take_step (n := 2) (t := 70) (b := 33332) rfl rfl ArealUCore.ArealUK.chunk_16665 s66
  have s64 : leavesOK ctxLitU 196500000000 0 ((leaves.drop 33328).take 72) 198300000000 0 = true :=
    take_step (n := 2) (t := 72) (b := 33330) rfl rfl ArealUCore.ArealUK.chunk_16664 s65
  have s63 : leavesOK ctxLitU 196450000000 0 ((leaves.drop 33326).take 74) 198300000000 0 = true :=
    take_step (n := 2) (t := 74) (b := 33328) rfl rfl ArealUCore.ArealUK.chunk_16663 s64
  have s62 : leavesOK ctxLitU 196400000000 0 ((leaves.drop 33324).take 76) 198300000000 0 = true :=
    take_step (n := 2) (t := 76) (b := 33326) rfl rfl ArealUCore.ArealUK.chunk_16662 s63
  have s61 : leavesOK ctxLitU 196350000000 0 ((leaves.drop 33322).take 78) 198300000000 0 = true :=
    take_step (n := 2) (t := 78) (b := 33324) rfl rfl ArealUCore.ArealUK.chunk_16661 s62
  have s60 : leavesOK ctxLitU 196300000000 0 ((leaves.drop 33320).take 80) 198300000000 0 = true :=
    take_step (n := 2) (t := 80) (b := 33322) rfl rfl ArealUCore.ArealUK.chunk_16660 s61
  have s59 : leavesOK ctxLitU 196250000000 0 ((leaves.drop 33318).take 82) 198300000000 0 = true :=
    take_step (n := 2) (t := 82) (b := 33320) rfl rfl ArealUCore.ArealUK.chunk_16659 s60
  have s58 : leavesOK ctxLitU 196200000000 0 ((leaves.drop 33316).take 84) 198300000000 0 = true :=
    take_step (n := 2) (t := 84) (b := 33318) rfl rfl ArealUCore.ArealUK.chunk_16658 s59
  have s57 : leavesOK ctxLitU 196150000000 0 ((leaves.drop 33314).take 86) 198300000000 0 = true :=
    take_step (n := 2) (t := 86) (b := 33316) rfl rfl ArealUCore.ArealUK.chunk_16657 s58
  have s56 : leavesOK ctxLitU 196100000000 0 ((leaves.drop 33312).take 88) 198300000000 0 = true :=
    take_step (n := 2) (t := 88) (b := 33314) rfl rfl ArealUCore.ArealUK.chunk_16656 s57
  have s55 : leavesOK ctxLitU 196050000000 0 ((leaves.drop 33310).take 90) 198300000000 0 = true :=
    take_step (n := 2) (t := 90) (b := 33312) rfl rfl ArealUCore.ArealUK.chunk_16655 s56
  have s54 : leavesOK ctxLitU 196000000000 0 ((leaves.drop 33308).take 92) 198300000000 0 = true :=
    take_step (n := 2) (t := 92) (b := 33310) rfl rfl ArealUCore.ArealUK.chunk_16654 s55
  have s53 : leavesOK ctxLitU 195950000000 0 ((leaves.drop 33306).take 94) 198300000000 0 = true :=
    take_step (n := 2) (t := 94) (b := 33308) rfl rfl ArealUCore.ArealUK.chunk_16653 s54
  have s52 : leavesOK ctxLitU 195900000000 0 ((leaves.drop 33304).take 96) 198300000000 0 = true :=
    take_step (n := 2) (t := 96) (b := 33306) rfl rfl ArealUCore.ArealUK.chunk_16652 s53
  have s51 : leavesOK ctxLitU 195850000000 0 ((leaves.drop 33302).take 98) 198300000000 0 = true :=
    take_step (n := 2) (t := 98) (b := 33304) rfl rfl ArealUCore.ArealUK.chunk_16651 s52
  have s50 : leavesOK ctxLitU 195800000000 0 ((leaves.drop 33300).take 100) 198300000000 0 = true :=
    take_step (n := 2) (t := 100) (b := 33302) rfl rfl ArealUCore.ArealUK.chunk_16650 s51
  have s49 : leavesOK ctxLitU 195750000000 0 ((leaves.drop 33298).take 102) 198300000000 0 = true :=
    take_step (n := 2) (t := 102) (b := 33300) rfl rfl ArealUCore.ArealUK.chunk_16649 s50
  have s48 : leavesOK ctxLitU 195700000000 0 ((leaves.drop 33296).take 104) 198300000000 0 = true :=
    take_step (n := 2) (t := 104) (b := 33298) rfl rfl ArealUCore.ArealUK.chunk_16648 s49
  have s47 : leavesOK ctxLitU 195650000000 0 ((leaves.drop 33294).take 106) 198300000000 0 = true :=
    take_step (n := 2) (t := 106) (b := 33296) rfl rfl ArealUCore.ArealUK.chunk_16647 s48
  have s46 : leavesOK ctxLitU 195600000000 0 ((leaves.drop 33292).take 108) 198300000000 0 = true :=
    take_step (n := 2) (t := 108) (b := 33294) rfl rfl ArealUCore.ArealUK.chunk_16646 s47
  have s45 : leavesOK ctxLitU 195550000000 0 ((leaves.drop 33290).take 110) 198300000000 0 = true :=
    take_step (n := 2) (t := 110) (b := 33292) rfl rfl ArealUCore.ArealUK.chunk_16645 s46
  have s44 : leavesOK ctxLitU 195500000000 0 ((leaves.drop 33288).take 112) 198300000000 0 = true :=
    take_step (n := 2) (t := 112) (b := 33290) rfl rfl ArealUCore.ArealUK.chunk_16644 s45
  have s43 : leavesOK ctxLitU 195450000000 0 ((leaves.drop 33286).take 114) 198300000000 0 = true :=
    take_step (n := 2) (t := 114) (b := 33288) rfl rfl ArealUCore.ArealUK.chunk_16643 s44
  have s42 : leavesOK ctxLitU 195400000000 0 ((leaves.drop 33284).take 116) 198300000000 0 = true :=
    take_step (n := 2) (t := 116) (b := 33286) rfl rfl ArealUCore.ArealUK.chunk_16642 s43
  have s41 : leavesOK ctxLitU 195350000000 0 ((leaves.drop 33282).take 118) 198300000000 0 = true :=
    take_step (n := 2) (t := 118) (b := 33284) rfl rfl ArealUCore.ArealUK.chunk_16641 s42
  have s40 : leavesOK ctxLitU 195300000000 0 ((leaves.drop 33280).take 120) 198300000000 0 = true :=
    take_step (n := 2) (t := 120) (b := 33282) rfl rfl ArealUCore.ArealUK.chunk_16640 s41
  have s39 : leavesOK ctxLitU 195250000000 0 ((leaves.drop 33278).take 122) 198300000000 0 = true :=
    take_step (n := 2) (t := 122) (b := 33280) rfl rfl ArealUCore.ArealUK.chunk_16639 s40
  have s38 : leavesOK ctxLitU 195200000000 0 ((leaves.drop 33276).take 124) 198300000000 0 = true :=
    take_step (n := 2) (t := 124) (b := 33278) rfl rfl ArealUCore.ArealUK.chunk_16638 s39
  have s37 : leavesOK ctxLitU 195150000000 0 ((leaves.drop 33274).take 126) 198300000000 0 = true :=
    take_step (n := 2) (t := 126) (b := 33276) rfl rfl ArealUCore.ArealUK.chunk_16637 s38
  have s36 : leavesOK ctxLitU 195100000000 0 ((leaves.drop 33272).take 128) 198300000000 0 = true :=
    take_step (n := 2) (t := 128) (b := 33274) rfl rfl ArealUCore.ArealUK.chunk_16636 s37
  have s35 : leavesOK ctxLitU 195050000000 0 ((leaves.drop 33270).take 130) 198300000000 0 = true :=
    take_step (n := 2) (t := 130) (b := 33272) rfl rfl ArealUCore.ArealUK.chunk_16635 s36
  have s34 : leavesOK ctxLitU 195000000000 0 ((leaves.drop 33268).take 132) 198300000000 0 = true :=
    take_step (n := 2) (t := 132) (b := 33270) rfl rfl ArealUCore.ArealUK.chunk_16634 s35
  have s33 : leavesOK ctxLitU 194950000000 0 ((leaves.drop 33266).take 134) 198300000000 0 = true :=
    take_step (n := 2) (t := 134) (b := 33268) rfl rfl ArealUCore.ArealUK.chunk_16633 s34
  have s32 : leavesOK ctxLitU 194900000000 0 ((leaves.drop 33264).take 136) 198300000000 0 = true :=
    take_step (n := 2) (t := 136) (b := 33266) rfl rfl ArealUCore.ArealUK.chunk_16632 s33
  have s31 : leavesOK ctxLitU 194850000000 0 ((leaves.drop 33262).take 138) 198300000000 0 = true :=
    take_step (n := 2) (t := 138) (b := 33264) rfl rfl ArealUCore.ArealUK.chunk_16631 s32
  have s30 : leavesOK ctxLitU 194800000000 0 ((leaves.drop 33260).take 140) 198300000000 0 = true :=
    take_step (n := 2) (t := 140) (b := 33262) rfl rfl ArealUCore.ArealUK.chunk_16630 s31
  have s29 : leavesOK ctxLitU 194750000000 0 ((leaves.drop 33258).take 142) 198300000000 0 = true :=
    take_step (n := 2) (t := 142) (b := 33260) rfl rfl ArealUCore.ArealUK.chunk_16629 s30
  have s28 : leavesOK ctxLitU 194700000000 0 ((leaves.drop 33256).take 144) 198300000000 0 = true :=
    take_step (n := 2) (t := 144) (b := 33258) rfl rfl ArealUCore.ArealUK.chunk_16628 s29
  have s27 : leavesOK ctxLitU 194650000000 0 ((leaves.drop 33254).take 146) 198300000000 0 = true :=
    take_step (n := 2) (t := 146) (b := 33256) rfl rfl ArealUCore.ArealUK.chunk_16627 s28
  have s26 : leavesOK ctxLitU 194600000000 0 ((leaves.drop 33252).take 148) 198300000000 0 = true :=
    take_step (n := 2) (t := 148) (b := 33254) rfl rfl ArealUCore.ArealUK.chunk_16626 s27
  have s25 : leavesOK ctxLitU 194550000000 0 ((leaves.drop 33250).take 150) 198300000000 0 = true :=
    take_step (n := 2) (t := 150) (b := 33252) rfl rfl ArealUCore.ArealUK.chunk_16625 s26
  have s24 : leavesOK ctxLitU 194500000000 0 ((leaves.drop 33248).take 152) 198300000000 0 = true :=
    take_step (n := 2) (t := 152) (b := 33250) rfl rfl ArealUCore.ArealUK.chunk_16624 s25
  have s23 : leavesOK ctxLitU 194450000000 0 ((leaves.drop 33246).take 154) 198300000000 0 = true :=
    take_step (n := 2) (t := 154) (b := 33248) rfl rfl ArealUCore.ArealUK.chunk_16623 s24
  have s22 : leavesOK ctxLitU 194400000000 0 ((leaves.drop 33244).take 156) 198300000000 0 = true :=
    take_step (n := 2) (t := 156) (b := 33246) rfl rfl ArealUCore.ArealUK.chunk_16622 s23
  have s21 : leavesOK ctxLitU 194350000000 0 ((leaves.drop 33242).take 158) 198300000000 0 = true :=
    take_step (n := 2) (t := 158) (b := 33244) rfl rfl ArealUCore.ArealUK.chunk_16621 s22
  have s20 : leavesOK ctxLitU 194300000000 0 ((leaves.drop 33240).take 160) 198300000000 0 = true :=
    take_step (n := 2) (t := 160) (b := 33242) rfl rfl ArealUCore.ArealUK.chunk_16620 s21
  have s19 : leavesOK ctxLitU 194250000000 0 ((leaves.drop 33238).take 162) 198300000000 0 = true :=
    take_step (n := 2) (t := 162) (b := 33240) rfl rfl ArealUCore.ArealUK.chunk_16619 s20
  have s18 : leavesOK ctxLitU 194200000000 0 ((leaves.drop 33236).take 164) 198300000000 0 = true :=
    take_step (n := 2) (t := 164) (b := 33238) rfl rfl ArealUCore.ArealUK.chunk_16618 s19
  have s17 : leavesOK ctxLitU 194150000000 0 ((leaves.drop 33234).take 166) 198300000000 0 = true :=
    take_step (n := 2) (t := 166) (b := 33236) rfl rfl ArealUCore.ArealUK.chunk_16617 s18
  have s16 : leavesOK ctxLitU 194100000000 0 ((leaves.drop 33232).take 168) 198300000000 0 = true :=
    take_step (n := 2) (t := 168) (b := 33234) rfl rfl ArealUCore.ArealUK.chunk_16616 s17
  have s15 : leavesOK ctxLitU 194050000000 0 ((leaves.drop 33230).take 170) 198300000000 0 = true :=
    take_step (n := 2) (t := 170) (b := 33232) rfl rfl ArealUCore.ArealUK.chunk_16615 s16
  have s14 : leavesOK ctxLitU 194000000000 0 ((leaves.drop 33228).take 172) 198300000000 0 = true :=
    take_step (n := 2) (t := 172) (b := 33230) rfl rfl ArealUCore.ArealUK.chunk_16614 s15
  have s13 : leavesOK ctxLitU 193950000000 0 ((leaves.drop 33226).take 174) 198300000000 0 = true :=
    take_step (n := 2) (t := 174) (b := 33228) rfl rfl ArealUCore.ArealUK.chunk_16613 s14
  have s12 : leavesOK ctxLitU 193900000000 0 ((leaves.drop 33224).take 176) 198300000000 0 = true :=
    take_step (n := 2) (t := 176) (b := 33226) rfl rfl ArealUCore.ArealUK.chunk_16612 s13
  have s11 : leavesOK ctxLitU 193850000000 0 ((leaves.drop 33222).take 178) 198300000000 0 = true :=
    take_step (n := 2) (t := 178) (b := 33224) rfl rfl ArealUCore.ArealUK.chunk_16611 s12
  have s10 : leavesOK ctxLitU 193800000000 0 ((leaves.drop 33220).take 180) 198300000000 0 = true :=
    take_step (n := 2) (t := 180) (b := 33222) rfl rfl ArealUCore.ArealUK.chunk_16610 s11
  have s9 : leavesOK ctxLitU 193750000000 0 ((leaves.drop 33218).take 182) 198300000000 0 = true :=
    take_step (n := 2) (t := 182) (b := 33220) rfl rfl ArealUCore.ArealUK.chunk_16609 s10
  have s8 : leavesOK ctxLitU 193700000000 0 ((leaves.drop 33216).take 184) 198300000000 0 = true :=
    take_step (n := 2) (t := 184) (b := 33218) rfl rfl ArealUCore.ArealUK.chunk_16608 s9
  have s7 : leavesOK ctxLitU 193650000000 0 ((leaves.drop 33214).take 186) 198300000000 0 = true :=
    take_step (n := 2) (t := 186) (b := 33216) rfl rfl ArealUCore.ArealUK.chunk_16607 s8
  have s6 : leavesOK ctxLitU 193600000000 0 ((leaves.drop 33212).take 188) 198300000000 0 = true :=
    take_step (n := 2) (t := 188) (b := 33214) rfl rfl ArealUCore.ArealUK.chunk_16606 s7
  have s5 : leavesOK ctxLitU 193550000000 0 ((leaves.drop 33210).take 190) 198300000000 0 = true :=
    take_step (n := 2) (t := 190) (b := 33212) rfl rfl ArealUCore.ArealUK.chunk_16605 s6
  have s4 : leavesOK ctxLitU 193500000000 0 ((leaves.drop 33208).take 192) 198300000000 0 = true :=
    take_step (n := 2) (t := 192) (b := 33210) rfl rfl ArealUCore.ArealUK.chunk_16604 s5
  have s3 : leavesOK ctxLitU 193450000000 0 ((leaves.drop 33206).take 194) 198300000000 0 = true :=
    take_step (n := 2) (t := 194) (b := 33208) rfl rfl ArealUCore.ArealUK.chunk_16603 s4
  have s2 : leavesOK ctxLitU 193400000000 0 ((leaves.drop 33204).take 196) 198300000000 0 = true :=
    take_step (n := 2) (t := 196) (b := 33206) rfl rfl ArealUCore.ArealUK.chunk_16602 s3
  have s1 : leavesOK ctxLitU 193350000000 0 ((leaves.drop 33202).take 198) 198300000000 0 = true :=
    take_step (n := 2) (t := 198) (b := 33204) rfl rfl ArealUCore.ArealUK.chunk_16601 s2
  have s0 : leavesOK ctxLitU 193300000000 0 ((leaves.drop 33200).take 200) 198300000000 0 = true :=
    take_step (n := 2) (t := 200) (b := 33202) rfl rfl ArealUCore.ArealUK.chunk_16600 s1
  exact s0

end Areal.UCert

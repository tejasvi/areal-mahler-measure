import ArealUK.Chunk10600
import ArealUK.Chunk10601
import ArealUK.Chunk10602
import ArealUK.Chunk10603
import ArealUK.Chunk10604
import ArealUK.Chunk10605
import ArealUK.Chunk10606
import ArealUK.Chunk10607
import ArealUK.Chunk10608
import ArealUK.Chunk10609
import ArealUK.Chunk10610
import ArealUK.Chunk10611
import ArealUK.Chunk10612
import ArealUK.Chunk10613
import ArealUK.Chunk10614
import ArealUK.Chunk10615
import ArealUK.Chunk10616
import ArealUK.Chunk10617
import ArealUK.Chunk10618
import ArealUK.Chunk10619
import ArealUK.Chunk10620
import ArealUK.Chunk10621
import ArealUK.Chunk10622
import ArealUK.Chunk10623
import ArealUK.Chunk10624
import ArealUK.Chunk10625
import ArealUK.Chunk10626
import ArealUK.Chunk10627
import ArealUK.Chunk10628
import ArealUK.Chunk10629
import ArealUK.Chunk10630
import ArealUK.Chunk10631
import ArealUK.Chunk10632
import ArealUK.Chunk10633
import ArealUK.Chunk10634
import ArealUK.Chunk10635
import ArealUK.Chunk10636
import ArealUK.Chunk10637
import ArealUK.Chunk10638
import ArealUK.Chunk10639
import ArealUK.Chunk10640
import ArealUK.Chunk10641
import ArealUK.Chunk10642
import ArealUK.Chunk10643
import ArealUK.Chunk10644
import ArealUK.Chunk10645
import ArealUK.Chunk10646
import ArealUK.Chunk10647
import ArealUK.Chunk10648
import ArealUK.Chunk10649
import ArealUK.Chunk10650
import ArealUK.Chunk10651
import ArealUK.Chunk10652
import ArealUK.Chunk10653
import ArealUK.Chunk10654
import ArealUK.Chunk10655
import ArealUK.Chunk10656
import ArealUK.Chunk10657
import ArealUK.Chunk10658
import ArealUK.Chunk10659
import ArealUK.Chunk10660
import ArealUK.Chunk10661
import ArealUK.Chunk10662
import ArealUK.Chunk10663
import ArealUK.Chunk10664
import ArealUK.Chunk10665
import ArealUK.Chunk10666
import ArealUK.Chunk10667
import ArealUK.Chunk10668
import ArealUK.Chunk10669
import ArealUK.Chunk10670
import ArealUK.Chunk10671
import ArealUK.Chunk10672
import ArealUK.Chunk10673
import ArealUK.Chunk10674
import ArealUK.Chunk10675
import ArealUK.Chunk10676
import ArealUK.Chunk10677
import ArealUK.Chunk10678
import ArealUK.Chunk10679
import ArealUK.Chunk10680
import ArealUK.Chunk10681
import ArealUK.Chunk10682
import ArealUK.Chunk10683
import ArealUK.Chunk10684
import ArealUK.Chunk10685
import ArealUK.Chunk10686
import ArealUK.Chunk10687
import ArealUK.Chunk10688
import ArealUK.Chunk10689
import ArealUK.Chunk10690
import ArealUK.Chunk10691
import ArealUK.Chunk10692
import ArealUK.Chunk10693
import ArealUK.Chunk10694
import ArealUK.Chunk10695
import ArealUK.Chunk10696
import ArealUK.Chunk10697
import ArealUK.Chunk10698
import ArealUK.Chunk10699
import Areal.UCert.LeavesKGen

/-! Group 106 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_106 : leavesOK ctxLitU 387150000000 2 ((leaves.drop 21200).take 200) 392150000000 2 = true := by
  have s99 := ArealUCore.ArealUK.chunk_10699
  have s98 : leavesOK ctxLitU 392050000000 2 ((leaves.drop 21396).take 4) 392150000000 2 = true :=
    take_step (n := 2) (t := 4) (b := 21398) rfl rfl ArealUCore.ArealUK.chunk_10698 s99
  have s97 : leavesOK ctxLitU 392000000000 2 ((leaves.drop 21394).take 6) 392150000000 2 = true :=
    take_step (n := 2) (t := 6) (b := 21396) rfl rfl ArealUCore.ArealUK.chunk_10697 s98
  have s96 : leavesOK ctxLitU 391950000000 2 ((leaves.drop 21392).take 8) 392150000000 2 = true :=
    take_step (n := 2) (t := 8) (b := 21394) rfl rfl ArealUCore.ArealUK.chunk_10696 s97
  have s95 : leavesOK ctxLitU 391900000000 2 ((leaves.drop 21390).take 10) 392150000000 2 = true :=
    take_step (n := 2) (t := 10) (b := 21392) rfl rfl ArealUCore.ArealUK.chunk_10695 s96
  have s94 : leavesOK ctxLitU 391850000000 2 ((leaves.drop 21388).take 12) 392150000000 2 = true :=
    take_step (n := 2) (t := 12) (b := 21390) rfl rfl ArealUCore.ArealUK.chunk_10694 s95
  have s93 : leavesOK ctxLitU 391800000000 2 ((leaves.drop 21386).take 14) 392150000000 2 = true :=
    take_step (n := 2) (t := 14) (b := 21388) rfl rfl ArealUCore.ArealUK.chunk_10693 s94
  have s92 : leavesOK ctxLitU 391750000000 2 ((leaves.drop 21384).take 16) 392150000000 2 = true :=
    take_step (n := 2) (t := 16) (b := 21386) rfl rfl ArealUCore.ArealUK.chunk_10692 s93
  have s91 : leavesOK ctxLitU 391700000000 2 ((leaves.drop 21382).take 18) 392150000000 2 = true :=
    take_step (n := 2) (t := 18) (b := 21384) rfl rfl ArealUCore.ArealUK.chunk_10691 s92
  have s90 : leavesOK ctxLitU 391650000000 2 ((leaves.drop 21380).take 20) 392150000000 2 = true :=
    take_step (n := 2) (t := 20) (b := 21382) rfl rfl ArealUCore.ArealUK.chunk_10690 s91
  have s89 : leavesOK ctxLitU 391600000000 2 ((leaves.drop 21378).take 22) 392150000000 2 = true :=
    take_step (n := 2) (t := 22) (b := 21380) rfl rfl ArealUCore.ArealUK.chunk_10689 s90
  have s88 : leavesOK ctxLitU 391550000000 2 ((leaves.drop 21376).take 24) 392150000000 2 = true :=
    take_step (n := 2) (t := 24) (b := 21378) rfl rfl ArealUCore.ArealUK.chunk_10688 s89
  have s87 : leavesOK ctxLitU 391500000000 2 ((leaves.drop 21374).take 26) 392150000000 2 = true :=
    take_step (n := 2) (t := 26) (b := 21376) rfl rfl ArealUCore.ArealUK.chunk_10687 s88
  have s86 : leavesOK ctxLitU 391450000000 2 ((leaves.drop 21372).take 28) 392150000000 2 = true :=
    take_step (n := 2) (t := 28) (b := 21374) rfl rfl ArealUCore.ArealUK.chunk_10686 s87
  have s85 : leavesOK ctxLitU 391400000000 2 ((leaves.drop 21370).take 30) 392150000000 2 = true :=
    take_step (n := 2) (t := 30) (b := 21372) rfl rfl ArealUCore.ArealUK.chunk_10685 s86
  have s84 : leavesOK ctxLitU 391350000000 2 ((leaves.drop 21368).take 32) 392150000000 2 = true :=
    take_step (n := 2) (t := 32) (b := 21370) rfl rfl ArealUCore.ArealUK.chunk_10684 s85
  have s83 : leavesOK ctxLitU 391300000000 2 ((leaves.drop 21366).take 34) 392150000000 2 = true :=
    take_step (n := 2) (t := 34) (b := 21368) rfl rfl ArealUCore.ArealUK.chunk_10683 s84
  have s82 : leavesOK ctxLitU 391250000000 2 ((leaves.drop 21364).take 36) 392150000000 2 = true :=
    take_step (n := 2) (t := 36) (b := 21366) rfl rfl ArealUCore.ArealUK.chunk_10682 s83
  have s81 : leavesOK ctxLitU 391200000000 2 ((leaves.drop 21362).take 38) 392150000000 2 = true :=
    take_step (n := 2) (t := 38) (b := 21364) rfl rfl ArealUCore.ArealUK.chunk_10681 s82
  have s80 : leavesOK ctxLitU 391150000000 2 ((leaves.drop 21360).take 40) 392150000000 2 = true :=
    take_step (n := 2) (t := 40) (b := 21362) rfl rfl ArealUCore.ArealUK.chunk_10680 s81
  have s79 : leavesOK ctxLitU 391100000000 2 ((leaves.drop 21358).take 42) 392150000000 2 = true :=
    take_step (n := 2) (t := 42) (b := 21360) rfl rfl ArealUCore.ArealUK.chunk_10679 s80
  have s78 : leavesOK ctxLitU 391050000000 2 ((leaves.drop 21356).take 44) 392150000000 2 = true :=
    take_step (n := 2) (t := 44) (b := 21358) rfl rfl ArealUCore.ArealUK.chunk_10678 s79
  have s77 : leavesOK ctxLitU 391000000000 2 ((leaves.drop 21354).take 46) 392150000000 2 = true :=
    take_step (n := 2) (t := 46) (b := 21356) rfl rfl ArealUCore.ArealUK.chunk_10677 s78
  have s76 : leavesOK ctxLitU 390950000000 2 ((leaves.drop 21352).take 48) 392150000000 2 = true :=
    take_step (n := 2) (t := 48) (b := 21354) rfl rfl ArealUCore.ArealUK.chunk_10676 s77
  have s75 : leavesOK ctxLitU 390900000000 2 ((leaves.drop 21350).take 50) 392150000000 2 = true :=
    take_step (n := 2) (t := 50) (b := 21352) rfl rfl ArealUCore.ArealUK.chunk_10675 s76
  have s74 : leavesOK ctxLitU 390850000000 2 ((leaves.drop 21348).take 52) 392150000000 2 = true :=
    take_step (n := 2) (t := 52) (b := 21350) rfl rfl ArealUCore.ArealUK.chunk_10674 s75
  have s73 : leavesOK ctxLitU 390800000000 2 ((leaves.drop 21346).take 54) 392150000000 2 = true :=
    take_step (n := 2) (t := 54) (b := 21348) rfl rfl ArealUCore.ArealUK.chunk_10673 s74
  have s72 : leavesOK ctxLitU 390750000000 2 ((leaves.drop 21344).take 56) 392150000000 2 = true :=
    take_step (n := 2) (t := 56) (b := 21346) rfl rfl ArealUCore.ArealUK.chunk_10672 s73
  have s71 : leavesOK ctxLitU 390700000000 2 ((leaves.drop 21342).take 58) 392150000000 2 = true :=
    take_step (n := 2) (t := 58) (b := 21344) rfl rfl ArealUCore.ArealUK.chunk_10671 s72
  have s70 : leavesOK ctxLitU 390650000000 2 ((leaves.drop 21340).take 60) 392150000000 2 = true :=
    take_step (n := 2) (t := 60) (b := 21342) rfl rfl ArealUCore.ArealUK.chunk_10670 s71
  have s69 : leavesOK ctxLitU 390600000000 2 ((leaves.drop 21338).take 62) 392150000000 2 = true :=
    take_step (n := 2) (t := 62) (b := 21340) rfl rfl ArealUCore.ArealUK.chunk_10669 s70
  have s68 : leavesOK ctxLitU 390550000000 2 ((leaves.drop 21336).take 64) 392150000000 2 = true :=
    take_step (n := 2) (t := 64) (b := 21338) rfl rfl ArealUCore.ArealUK.chunk_10668 s69
  have s67 : leavesOK ctxLitU 390500000000 2 ((leaves.drop 21334).take 66) 392150000000 2 = true :=
    take_step (n := 2) (t := 66) (b := 21336) rfl rfl ArealUCore.ArealUK.chunk_10667 s68
  have s66 : leavesOK ctxLitU 390450000000 2 ((leaves.drop 21332).take 68) 392150000000 2 = true :=
    take_step (n := 2) (t := 68) (b := 21334) rfl rfl ArealUCore.ArealUK.chunk_10666 s67
  have s65 : leavesOK ctxLitU 390400000000 2 ((leaves.drop 21330).take 70) 392150000000 2 = true :=
    take_step (n := 2) (t := 70) (b := 21332) rfl rfl ArealUCore.ArealUK.chunk_10665 s66
  have s64 : leavesOK ctxLitU 390350000000 2 ((leaves.drop 21328).take 72) 392150000000 2 = true :=
    take_step (n := 2) (t := 72) (b := 21330) rfl rfl ArealUCore.ArealUK.chunk_10664 s65
  have s63 : leavesOK ctxLitU 390300000000 2 ((leaves.drop 21326).take 74) 392150000000 2 = true :=
    take_step (n := 2) (t := 74) (b := 21328) rfl rfl ArealUCore.ArealUK.chunk_10663 s64
  have s62 : leavesOK ctxLitU 390250000000 2 ((leaves.drop 21324).take 76) 392150000000 2 = true :=
    take_step (n := 2) (t := 76) (b := 21326) rfl rfl ArealUCore.ArealUK.chunk_10662 s63
  have s61 : leavesOK ctxLitU 390200000000 2 ((leaves.drop 21322).take 78) 392150000000 2 = true :=
    take_step (n := 2) (t := 78) (b := 21324) rfl rfl ArealUCore.ArealUK.chunk_10661 s62
  have s60 : leavesOK ctxLitU 390150000000 2 ((leaves.drop 21320).take 80) 392150000000 2 = true :=
    take_step (n := 2) (t := 80) (b := 21322) rfl rfl ArealUCore.ArealUK.chunk_10660 s61
  have s59 : leavesOK ctxLitU 390100000000 2 ((leaves.drop 21318).take 82) 392150000000 2 = true :=
    take_step (n := 2) (t := 82) (b := 21320) rfl rfl ArealUCore.ArealUK.chunk_10659 s60
  have s58 : leavesOK ctxLitU 390050000000 2 ((leaves.drop 21316).take 84) 392150000000 2 = true :=
    take_step (n := 2) (t := 84) (b := 21318) rfl rfl ArealUCore.ArealUK.chunk_10658 s59
  have s57 : leavesOK ctxLitU 390000000000 2 ((leaves.drop 21314).take 86) 392150000000 2 = true :=
    take_step (n := 2) (t := 86) (b := 21316) rfl rfl ArealUCore.ArealUK.chunk_10657 s58
  have s56 : leavesOK ctxLitU 389950000000 2 ((leaves.drop 21312).take 88) 392150000000 2 = true :=
    take_step (n := 2) (t := 88) (b := 21314) rfl rfl ArealUCore.ArealUK.chunk_10656 s57
  have s55 : leavesOK ctxLitU 389900000000 2 ((leaves.drop 21310).take 90) 392150000000 2 = true :=
    take_step (n := 2) (t := 90) (b := 21312) rfl rfl ArealUCore.ArealUK.chunk_10655 s56
  have s54 : leavesOK ctxLitU 389850000000 2 ((leaves.drop 21308).take 92) 392150000000 2 = true :=
    take_step (n := 2) (t := 92) (b := 21310) rfl rfl ArealUCore.ArealUK.chunk_10654 s55
  have s53 : leavesOK ctxLitU 389800000000 2 ((leaves.drop 21306).take 94) 392150000000 2 = true :=
    take_step (n := 2) (t := 94) (b := 21308) rfl rfl ArealUCore.ArealUK.chunk_10653 s54
  have s52 : leavesOK ctxLitU 389750000000 2 ((leaves.drop 21304).take 96) 392150000000 2 = true :=
    take_step (n := 2) (t := 96) (b := 21306) rfl rfl ArealUCore.ArealUK.chunk_10652 s53
  have s51 : leavesOK ctxLitU 389700000000 2 ((leaves.drop 21302).take 98) 392150000000 2 = true :=
    take_step (n := 2) (t := 98) (b := 21304) rfl rfl ArealUCore.ArealUK.chunk_10651 s52
  have s50 : leavesOK ctxLitU 389650000000 2 ((leaves.drop 21300).take 100) 392150000000 2 = true :=
    take_step (n := 2) (t := 100) (b := 21302) rfl rfl ArealUCore.ArealUK.chunk_10650 s51
  have s49 : leavesOK ctxLitU 389600000000 2 ((leaves.drop 21298).take 102) 392150000000 2 = true :=
    take_step (n := 2) (t := 102) (b := 21300) rfl rfl ArealUCore.ArealUK.chunk_10649 s50
  have s48 : leavesOK ctxLitU 389550000000 2 ((leaves.drop 21296).take 104) 392150000000 2 = true :=
    take_step (n := 2) (t := 104) (b := 21298) rfl rfl ArealUCore.ArealUK.chunk_10648 s49
  have s47 : leavesOK ctxLitU 389500000000 2 ((leaves.drop 21294).take 106) 392150000000 2 = true :=
    take_step (n := 2) (t := 106) (b := 21296) rfl rfl ArealUCore.ArealUK.chunk_10647 s48
  have s46 : leavesOK ctxLitU 389450000000 2 ((leaves.drop 21292).take 108) 392150000000 2 = true :=
    take_step (n := 2) (t := 108) (b := 21294) rfl rfl ArealUCore.ArealUK.chunk_10646 s47
  have s45 : leavesOK ctxLitU 389400000000 2 ((leaves.drop 21290).take 110) 392150000000 2 = true :=
    take_step (n := 2) (t := 110) (b := 21292) rfl rfl ArealUCore.ArealUK.chunk_10645 s46
  have s44 : leavesOK ctxLitU 389350000000 2 ((leaves.drop 21288).take 112) 392150000000 2 = true :=
    take_step (n := 2) (t := 112) (b := 21290) rfl rfl ArealUCore.ArealUK.chunk_10644 s45
  have s43 : leavesOK ctxLitU 389300000000 2 ((leaves.drop 21286).take 114) 392150000000 2 = true :=
    take_step (n := 2) (t := 114) (b := 21288) rfl rfl ArealUCore.ArealUK.chunk_10643 s44
  have s42 : leavesOK ctxLitU 389250000000 2 ((leaves.drop 21284).take 116) 392150000000 2 = true :=
    take_step (n := 2) (t := 116) (b := 21286) rfl rfl ArealUCore.ArealUK.chunk_10642 s43
  have s41 : leavesOK ctxLitU 389200000000 2 ((leaves.drop 21282).take 118) 392150000000 2 = true :=
    take_step (n := 2) (t := 118) (b := 21284) rfl rfl ArealUCore.ArealUK.chunk_10641 s42
  have s40 : leavesOK ctxLitU 389150000000 2 ((leaves.drop 21280).take 120) 392150000000 2 = true :=
    take_step (n := 2) (t := 120) (b := 21282) rfl rfl ArealUCore.ArealUK.chunk_10640 s41
  have s39 : leavesOK ctxLitU 389100000000 2 ((leaves.drop 21278).take 122) 392150000000 2 = true :=
    take_step (n := 2) (t := 122) (b := 21280) rfl rfl ArealUCore.ArealUK.chunk_10639 s40
  have s38 : leavesOK ctxLitU 389050000000 2 ((leaves.drop 21276).take 124) 392150000000 2 = true :=
    take_step (n := 2) (t := 124) (b := 21278) rfl rfl ArealUCore.ArealUK.chunk_10638 s39
  have s37 : leavesOK ctxLitU 389000000000 2 ((leaves.drop 21274).take 126) 392150000000 2 = true :=
    take_step (n := 2) (t := 126) (b := 21276) rfl rfl ArealUCore.ArealUK.chunk_10637 s38
  have s36 : leavesOK ctxLitU 388950000000 2 ((leaves.drop 21272).take 128) 392150000000 2 = true :=
    take_step (n := 2) (t := 128) (b := 21274) rfl rfl ArealUCore.ArealUK.chunk_10636 s37
  have s35 : leavesOK ctxLitU 388900000000 2 ((leaves.drop 21270).take 130) 392150000000 2 = true :=
    take_step (n := 2) (t := 130) (b := 21272) rfl rfl ArealUCore.ArealUK.chunk_10635 s36
  have s34 : leavesOK ctxLitU 388850000000 2 ((leaves.drop 21268).take 132) 392150000000 2 = true :=
    take_step (n := 2) (t := 132) (b := 21270) rfl rfl ArealUCore.ArealUK.chunk_10634 s35
  have s33 : leavesOK ctxLitU 388800000000 2 ((leaves.drop 21266).take 134) 392150000000 2 = true :=
    take_step (n := 2) (t := 134) (b := 21268) rfl rfl ArealUCore.ArealUK.chunk_10633 s34
  have s32 : leavesOK ctxLitU 388750000000 2 ((leaves.drop 21264).take 136) 392150000000 2 = true :=
    take_step (n := 2) (t := 136) (b := 21266) rfl rfl ArealUCore.ArealUK.chunk_10632 s33
  have s31 : leavesOK ctxLitU 388700000000 2 ((leaves.drop 21262).take 138) 392150000000 2 = true :=
    take_step (n := 2) (t := 138) (b := 21264) rfl rfl ArealUCore.ArealUK.chunk_10631 s32
  have s30 : leavesOK ctxLitU 388650000000 2 ((leaves.drop 21260).take 140) 392150000000 2 = true :=
    take_step (n := 2) (t := 140) (b := 21262) rfl rfl ArealUCore.ArealUK.chunk_10630 s31
  have s29 : leavesOK ctxLitU 388600000000 2 ((leaves.drop 21258).take 142) 392150000000 2 = true :=
    take_step (n := 2) (t := 142) (b := 21260) rfl rfl ArealUCore.ArealUK.chunk_10629 s30
  have s28 : leavesOK ctxLitU 388550000000 2 ((leaves.drop 21256).take 144) 392150000000 2 = true :=
    take_step (n := 2) (t := 144) (b := 21258) rfl rfl ArealUCore.ArealUK.chunk_10628 s29
  have s27 : leavesOK ctxLitU 388500000000 2 ((leaves.drop 21254).take 146) 392150000000 2 = true :=
    take_step (n := 2) (t := 146) (b := 21256) rfl rfl ArealUCore.ArealUK.chunk_10627 s28
  have s26 : leavesOK ctxLitU 388450000000 2 ((leaves.drop 21252).take 148) 392150000000 2 = true :=
    take_step (n := 2) (t := 148) (b := 21254) rfl rfl ArealUCore.ArealUK.chunk_10626 s27
  have s25 : leavesOK ctxLitU 388400000000 2 ((leaves.drop 21250).take 150) 392150000000 2 = true :=
    take_step (n := 2) (t := 150) (b := 21252) rfl rfl ArealUCore.ArealUK.chunk_10625 s26
  have s24 : leavesOK ctxLitU 388350000000 2 ((leaves.drop 21248).take 152) 392150000000 2 = true :=
    take_step (n := 2) (t := 152) (b := 21250) rfl rfl ArealUCore.ArealUK.chunk_10624 s25
  have s23 : leavesOK ctxLitU 388300000000 2 ((leaves.drop 21246).take 154) 392150000000 2 = true :=
    take_step (n := 2) (t := 154) (b := 21248) rfl rfl ArealUCore.ArealUK.chunk_10623 s24
  have s22 : leavesOK ctxLitU 388250000000 2 ((leaves.drop 21244).take 156) 392150000000 2 = true :=
    take_step (n := 2) (t := 156) (b := 21246) rfl rfl ArealUCore.ArealUK.chunk_10622 s23
  have s21 : leavesOK ctxLitU 388200000000 2 ((leaves.drop 21242).take 158) 392150000000 2 = true :=
    take_step (n := 2) (t := 158) (b := 21244) rfl rfl ArealUCore.ArealUK.chunk_10621 s22
  have s20 : leavesOK ctxLitU 388150000000 2 ((leaves.drop 21240).take 160) 392150000000 2 = true :=
    take_step (n := 2) (t := 160) (b := 21242) rfl rfl ArealUCore.ArealUK.chunk_10620 s21
  have s19 : leavesOK ctxLitU 388100000000 2 ((leaves.drop 21238).take 162) 392150000000 2 = true :=
    take_step (n := 2) (t := 162) (b := 21240) rfl rfl ArealUCore.ArealUK.chunk_10619 s20
  have s18 : leavesOK ctxLitU 388050000000 2 ((leaves.drop 21236).take 164) 392150000000 2 = true :=
    take_step (n := 2) (t := 164) (b := 21238) rfl rfl ArealUCore.ArealUK.chunk_10618 s19
  have s17 : leavesOK ctxLitU 388000000000 2 ((leaves.drop 21234).take 166) 392150000000 2 = true :=
    take_step (n := 2) (t := 166) (b := 21236) rfl rfl ArealUCore.ArealUK.chunk_10617 s18
  have s16 : leavesOK ctxLitU 387950000000 2 ((leaves.drop 21232).take 168) 392150000000 2 = true :=
    take_step (n := 2) (t := 168) (b := 21234) rfl rfl ArealUCore.ArealUK.chunk_10616 s17
  have s15 : leavesOK ctxLitU 387900000000 2 ((leaves.drop 21230).take 170) 392150000000 2 = true :=
    take_step (n := 2) (t := 170) (b := 21232) rfl rfl ArealUCore.ArealUK.chunk_10615 s16
  have s14 : leavesOK ctxLitU 387850000000 2 ((leaves.drop 21228).take 172) 392150000000 2 = true :=
    take_step (n := 2) (t := 172) (b := 21230) rfl rfl ArealUCore.ArealUK.chunk_10614 s15
  have s13 : leavesOK ctxLitU 387800000000 2 ((leaves.drop 21226).take 174) 392150000000 2 = true :=
    take_step (n := 2) (t := 174) (b := 21228) rfl rfl ArealUCore.ArealUK.chunk_10613 s14
  have s12 : leavesOK ctxLitU 387750000000 2 ((leaves.drop 21224).take 176) 392150000000 2 = true :=
    take_step (n := 2) (t := 176) (b := 21226) rfl rfl ArealUCore.ArealUK.chunk_10612 s13
  have s11 : leavesOK ctxLitU 387700000000 2 ((leaves.drop 21222).take 178) 392150000000 2 = true :=
    take_step (n := 2) (t := 178) (b := 21224) rfl rfl ArealUCore.ArealUK.chunk_10611 s12
  have s10 : leavesOK ctxLitU 387650000000 2 ((leaves.drop 21220).take 180) 392150000000 2 = true :=
    take_step (n := 2) (t := 180) (b := 21222) rfl rfl ArealUCore.ArealUK.chunk_10610 s11
  have s9 : leavesOK ctxLitU 387600000000 2 ((leaves.drop 21218).take 182) 392150000000 2 = true :=
    take_step (n := 2) (t := 182) (b := 21220) rfl rfl ArealUCore.ArealUK.chunk_10609 s10
  have s8 : leavesOK ctxLitU 387550000000 2 ((leaves.drop 21216).take 184) 392150000000 2 = true :=
    take_step (n := 2) (t := 184) (b := 21218) rfl rfl ArealUCore.ArealUK.chunk_10608 s9
  have s7 : leavesOK ctxLitU 387500000000 2 ((leaves.drop 21214).take 186) 392150000000 2 = true :=
    take_step (n := 2) (t := 186) (b := 21216) rfl rfl ArealUCore.ArealUK.chunk_10607 s8
  have s6 : leavesOK ctxLitU 387450000000 2 ((leaves.drop 21212).take 188) 392150000000 2 = true :=
    take_step (n := 2) (t := 188) (b := 21214) rfl rfl ArealUCore.ArealUK.chunk_10606 s7
  have s5 : leavesOK ctxLitU 387400000000 2 ((leaves.drop 21210).take 190) 392150000000 2 = true :=
    take_step (n := 2) (t := 190) (b := 21212) rfl rfl ArealUCore.ArealUK.chunk_10605 s6
  have s4 : leavesOK ctxLitU 387350000000 2 ((leaves.drop 21208).take 192) 392150000000 2 = true :=
    take_step (n := 2) (t := 192) (b := 21210) rfl rfl ArealUCore.ArealUK.chunk_10604 s5
  have s3 : leavesOK ctxLitU 387300000000 2 ((leaves.drop 21206).take 194) 392150000000 2 = true :=
    take_step (n := 2) (t := 194) (b := 21208) rfl rfl ArealUCore.ArealUK.chunk_10603 s4
  have s2 : leavesOK ctxLitU 387250000000 2 ((leaves.drop 21204).take 196) 392150000000 2 = true :=
    take_step (n := 2) (t := 196) (b := 21206) rfl rfl ArealUCore.ArealUK.chunk_10602 s3
  have s1 : leavesOK ctxLitU 387200000000 2 ((leaves.drop 21202).take 198) 392150000000 2 = true :=
    take_step (n := 2) (t := 198) (b := 21204) rfl rfl ArealUCore.ArealUK.chunk_10601 s2
  have s0 : leavesOK ctxLitU 387150000000 2 ((leaves.drop 21200).take 200) 392150000000 2 = true :=
    take_step (n := 2) (t := 200) (b := 21202) rfl rfl ArealUCore.ArealUK.chunk_10600 s1
  exact s0

end Areal.UCert

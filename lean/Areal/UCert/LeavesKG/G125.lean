import ArealUK.Chunk12500
import ArealUK.Chunk12501
import ArealUK.Chunk12502
import ArealUK.Chunk12503
import ArealUK.Chunk12504
import ArealUK.Chunk12505
import ArealUK.Chunk12506
import ArealUK.Chunk12507
import ArealUK.Chunk12508
import ArealUK.Chunk12509
import ArealUK.Chunk12510
import ArealUK.Chunk12511
import ArealUK.Chunk12512
import ArealUK.Chunk12513
import ArealUK.Chunk12514
import ArealUK.Chunk12515
import ArealUK.Chunk12516
import ArealUK.Chunk12517
import ArealUK.Chunk12518
import ArealUK.Chunk12519
import ArealUK.Chunk12520
import ArealUK.Chunk12521
import ArealUK.Chunk12522
import ArealUK.Chunk12523
import ArealUK.Chunk12524
import ArealUK.Chunk12525
import ArealUK.Chunk12526
import ArealUK.Chunk12527
import ArealUK.Chunk12528
import ArealUK.Chunk12529
import ArealUK.Chunk12530
import ArealUK.Chunk12531
import ArealUK.Chunk12532
import ArealUK.Chunk12533
import ArealUK.Chunk12534
import ArealUK.Chunk12535
import ArealUK.Chunk12536
import ArealUK.Chunk12537
import ArealUK.Chunk12538
import ArealUK.Chunk12539
import ArealUK.Chunk12540
import ArealUK.Chunk12541
import ArealUK.Chunk12542
import ArealUK.Chunk12543
import ArealUK.Chunk12544
import ArealUK.Chunk12545
import ArealUK.Chunk12546
import ArealUK.Chunk12547
import ArealUK.Chunk12548
import ArealUK.Chunk12549
import ArealUK.Chunk12550
import ArealUK.Chunk12551
import ArealUK.Chunk12552
import ArealUK.Chunk12553
import ArealUK.Chunk12554
import ArealUK.Chunk12555
import ArealUK.Chunk12556
import ArealUK.Chunk12557
import ArealUK.Chunk12558
import ArealUK.Chunk12559
import ArealUK.Chunk12560
import ArealUK.Chunk12561
import ArealUK.Chunk12562
import ArealUK.Chunk12563
import ArealUK.Chunk12564
import ArealUK.Chunk12565
import ArealUK.Chunk12566
import ArealUK.Chunk12567
import ArealUK.Chunk12568
import ArealUK.Chunk12569
import ArealUK.Chunk12570
import ArealUK.Chunk12571
import ArealUK.Chunk12572
import ArealUK.Chunk12573
import ArealUK.Chunk12574
import ArealUK.Chunk12575
import ArealUK.Chunk12576
import ArealUK.Chunk12577
import ArealUK.Chunk12578
import ArealUK.Chunk12579
import ArealUK.Chunk12580
import ArealUK.Chunk12581
import ArealUK.Chunk12582
import ArealUK.Chunk12583
import ArealUK.Chunk12584
import ArealUK.Chunk12585
import ArealUK.Chunk12586
import ArealUK.Chunk12587
import ArealUK.Chunk12588
import ArealUK.Chunk12589
import ArealUK.Chunk12590
import ArealUK.Chunk12591
import ArealUK.Chunk12592
import ArealUK.Chunk12593
import ArealUK.Chunk12594
import ArealUK.Chunk12595
import ArealUK.Chunk12596
import ArealUK.Chunk12597
import ArealUK.Chunk12598
import ArealUK.Chunk12599
import Areal.UCert.LeavesKGen

/-! Group 125 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_125 : leavesOK ctxLitU 505125000000 2 ((leaves.drop 25000).take 200) 510075000000 2 = true := by
  have s99 := ArealUCore.ArealUK.chunk_12599
  have s98 : leavesOK ctxLitU 509975000000 2 ((leaves.drop 25196).take 4) 510075000000 2 = true :=
    take_step (n := 2) (t := 4) (b := 25198) rfl rfl ArealUCore.ArealUK.chunk_12598 s99
  have s97 : leavesOK ctxLitU 509925000000 2 ((leaves.drop 25194).take 6) 510075000000 2 = true :=
    take_step (n := 2) (t := 6) (b := 25196) rfl rfl ArealUCore.ArealUK.chunk_12597 s98
  have s96 : leavesOK ctxLitU 509875000000 2 ((leaves.drop 25192).take 8) 510075000000 2 = true :=
    take_step (n := 2) (t := 8) (b := 25194) rfl rfl ArealUCore.ArealUK.chunk_12596 s97
  have s95 : leavesOK ctxLitU 509825000000 2 ((leaves.drop 25190).take 10) 510075000000 2 = true :=
    take_step (n := 2) (t := 10) (b := 25192) rfl rfl ArealUCore.ArealUK.chunk_12595 s96
  have s94 : leavesOK ctxLitU 509775000000 2 ((leaves.drop 25188).take 12) 510075000000 2 = true :=
    take_step (n := 2) (t := 12) (b := 25190) rfl rfl ArealUCore.ArealUK.chunk_12594 s95
  have s93 : leavesOK ctxLitU 509725000000 2 ((leaves.drop 25186).take 14) 510075000000 2 = true :=
    take_step (n := 2) (t := 14) (b := 25188) rfl rfl ArealUCore.ArealUK.chunk_12593 s94
  have s92 : leavesOK ctxLitU 509675000000 2 ((leaves.drop 25184).take 16) 510075000000 2 = true :=
    take_step (n := 2) (t := 16) (b := 25186) rfl rfl ArealUCore.ArealUK.chunk_12592 s93
  have s91 : leavesOK ctxLitU 509625000000 2 ((leaves.drop 25182).take 18) 510075000000 2 = true :=
    take_step (n := 2) (t := 18) (b := 25184) rfl rfl ArealUCore.ArealUK.chunk_12591 s92
  have s90 : leavesOK ctxLitU 509575000000 2 ((leaves.drop 25180).take 20) 510075000000 2 = true :=
    take_step (n := 2) (t := 20) (b := 25182) rfl rfl ArealUCore.ArealUK.chunk_12590 s91
  have s89 : leavesOK ctxLitU 509525000000 2 ((leaves.drop 25178).take 22) 510075000000 2 = true :=
    take_step (n := 2) (t := 22) (b := 25180) rfl rfl ArealUCore.ArealUK.chunk_12589 s90
  have s88 : leavesOK ctxLitU 509475000000 2 ((leaves.drop 25176).take 24) 510075000000 2 = true :=
    take_step (n := 2) (t := 24) (b := 25178) rfl rfl ArealUCore.ArealUK.chunk_12588 s89
  have s87 : leavesOK ctxLitU 509425000000 2 ((leaves.drop 25174).take 26) 510075000000 2 = true :=
    take_step (n := 2) (t := 26) (b := 25176) rfl rfl ArealUCore.ArealUK.chunk_12587 s88
  have s86 : leavesOK ctxLitU 509375000000 2 ((leaves.drop 25172).take 28) 510075000000 2 = true :=
    take_step (n := 2) (t := 28) (b := 25174) rfl rfl ArealUCore.ArealUK.chunk_12586 s87
  have s85 : leavesOK ctxLitU 509325000000 2 ((leaves.drop 25170).take 30) 510075000000 2 = true :=
    take_step (n := 2) (t := 30) (b := 25172) rfl rfl ArealUCore.ArealUK.chunk_12585 s86
  have s84 : leavesOK ctxLitU 509275000000 2 ((leaves.drop 25168).take 32) 510075000000 2 = true :=
    take_step (n := 2) (t := 32) (b := 25170) rfl rfl ArealUCore.ArealUK.chunk_12584 s85
  have s83 : leavesOK ctxLitU 509225000000 2 ((leaves.drop 25166).take 34) 510075000000 2 = true :=
    take_step (n := 2) (t := 34) (b := 25168) rfl rfl ArealUCore.ArealUK.chunk_12583 s84
  have s82 : leavesOK ctxLitU 509175000000 2 ((leaves.drop 25164).take 36) 510075000000 2 = true :=
    take_step (n := 2) (t := 36) (b := 25166) rfl rfl ArealUCore.ArealUK.chunk_12582 s83
  have s81 : leavesOK ctxLitU 509125000000 2 ((leaves.drop 25162).take 38) 510075000000 2 = true :=
    take_step (n := 2) (t := 38) (b := 25164) rfl rfl ArealUCore.ArealUK.chunk_12581 s82
  have s80 : leavesOK ctxLitU 509075000000 2 ((leaves.drop 25160).take 40) 510075000000 2 = true :=
    take_step (n := 2) (t := 40) (b := 25162) rfl rfl ArealUCore.ArealUK.chunk_12580 s81
  have s79 : leavesOK ctxLitU 509025000000 2 ((leaves.drop 25158).take 42) 510075000000 2 = true :=
    take_step (n := 2) (t := 42) (b := 25160) rfl rfl ArealUCore.ArealUK.chunk_12579 s80
  have s78 : leavesOK ctxLitU 508975000000 2 ((leaves.drop 25156).take 44) 510075000000 2 = true :=
    take_step (n := 2) (t := 44) (b := 25158) rfl rfl ArealUCore.ArealUK.chunk_12578 s79
  have s77 : leavesOK ctxLitU 508925000000 2 ((leaves.drop 25154).take 46) 510075000000 2 = true :=
    take_step (n := 2) (t := 46) (b := 25156) rfl rfl ArealUCore.ArealUK.chunk_12577 s78
  have s76 : leavesOK ctxLitU 508875000000 2 ((leaves.drop 25152).take 48) 510075000000 2 = true :=
    take_step (n := 2) (t := 48) (b := 25154) rfl rfl ArealUCore.ArealUK.chunk_12576 s77
  have s75 : leavesOK ctxLitU 508825000000 2 ((leaves.drop 25150).take 50) 510075000000 2 = true :=
    take_step (n := 2) (t := 50) (b := 25152) rfl rfl ArealUCore.ArealUK.chunk_12575 s76
  have s74 : leavesOK ctxLitU 508775000000 2 ((leaves.drop 25148).take 52) 510075000000 2 = true :=
    take_step (n := 2) (t := 52) (b := 25150) rfl rfl ArealUCore.ArealUK.chunk_12574 s75
  have s73 : leavesOK ctxLitU 508725000000 2 ((leaves.drop 25146).take 54) 510075000000 2 = true :=
    take_step (n := 2) (t := 54) (b := 25148) rfl rfl ArealUCore.ArealUK.chunk_12573 s74
  have s72 : leavesOK ctxLitU 508675000000 2 ((leaves.drop 25144).take 56) 510075000000 2 = true :=
    take_step (n := 2) (t := 56) (b := 25146) rfl rfl ArealUCore.ArealUK.chunk_12572 s73
  have s71 : leavesOK ctxLitU 508625000000 2 ((leaves.drop 25142).take 58) 510075000000 2 = true :=
    take_step (n := 2) (t := 58) (b := 25144) rfl rfl ArealUCore.ArealUK.chunk_12571 s72
  have s70 : leavesOK ctxLitU 508575000000 2 ((leaves.drop 25140).take 60) 510075000000 2 = true :=
    take_step (n := 2) (t := 60) (b := 25142) rfl rfl ArealUCore.ArealUK.chunk_12570 s71
  have s69 : leavesOK ctxLitU 508525000000 2 ((leaves.drop 25138).take 62) 510075000000 2 = true :=
    take_step (n := 2) (t := 62) (b := 25140) rfl rfl ArealUCore.ArealUK.chunk_12569 s70
  have s68 : leavesOK ctxLitU 508475000000 2 ((leaves.drop 25136).take 64) 510075000000 2 = true :=
    take_step (n := 2) (t := 64) (b := 25138) rfl rfl ArealUCore.ArealUK.chunk_12568 s69
  have s67 : leavesOK ctxLitU 508425000000 2 ((leaves.drop 25134).take 66) 510075000000 2 = true :=
    take_step (n := 2) (t := 66) (b := 25136) rfl rfl ArealUCore.ArealUK.chunk_12567 s68
  have s66 : leavesOK ctxLitU 508375000000 2 ((leaves.drop 25132).take 68) 510075000000 2 = true :=
    take_step (n := 2) (t := 68) (b := 25134) rfl rfl ArealUCore.ArealUK.chunk_12566 s67
  have s65 : leavesOK ctxLitU 508325000000 2 ((leaves.drop 25130).take 70) 510075000000 2 = true :=
    take_step (n := 2) (t := 70) (b := 25132) rfl rfl ArealUCore.ArealUK.chunk_12565 s66
  have s64 : leavesOK ctxLitU 508275000000 2 ((leaves.drop 25128).take 72) 510075000000 2 = true :=
    take_step (n := 2) (t := 72) (b := 25130) rfl rfl ArealUCore.ArealUK.chunk_12564 s65
  have s63 : leavesOK ctxLitU 508225000000 2 ((leaves.drop 25126).take 74) 510075000000 2 = true :=
    take_step (n := 2) (t := 74) (b := 25128) rfl rfl ArealUCore.ArealUK.chunk_12563 s64
  have s62 : leavesOK ctxLitU 508175000000 2 ((leaves.drop 25124).take 76) 510075000000 2 = true :=
    take_step (n := 2) (t := 76) (b := 25126) rfl rfl ArealUCore.ArealUK.chunk_12562 s63
  have s61 : leavesOK ctxLitU 508125000000 2 ((leaves.drop 25122).take 78) 510075000000 2 = true :=
    take_step (n := 2) (t := 78) (b := 25124) rfl rfl ArealUCore.ArealUK.chunk_12561 s62
  have s60 : leavesOK ctxLitU 508075000000 2 ((leaves.drop 25120).take 80) 510075000000 2 = true :=
    take_step (n := 2) (t := 80) (b := 25122) rfl rfl ArealUCore.ArealUK.chunk_12560 s61
  have s59 : leavesOK ctxLitU 508025000000 2 ((leaves.drop 25118).take 82) 510075000000 2 = true :=
    take_step (n := 2) (t := 82) (b := 25120) rfl rfl ArealUCore.ArealUK.chunk_12559 s60
  have s58 : leavesOK ctxLitU 507975000000 2 ((leaves.drop 25116).take 84) 510075000000 2 = true :=
    take_step (n := 2) (t := 84) (b := 25118) rfl rfl ArealUCore.ArealUK.chunk_12558 s59
  have s57 : leavesOK ctxLitU 507925000000 2 ((leaves.drop 25114).take 86) 510075000000 2 = true :=
    take_step (n := 2) (t := 86) (b := 25116) rfl rfl ArealUCore.ArealUK.chunk_12557 s58
  have s56 : leavesOK ctxLitU 507875000000 2 ((leaves.drop 25112).take 88) 510075000000 2 = true :=
    take_step (n := 2) (t := 88) (b := 25114) rfl rfl ArealUCore.ArealUK.chunk_12556 s57
  have s55 : leavesOK ctxLitU 507825000000 2 ((leaves.drop 25110).take 90) 510075000000 2 = true :=
    take_step (n := 2) (t := 90) (b := 25112) rfl rfl ArealUCore.ArealUK.chunk_12555 s56
  have s54 : leavesOK ctxLitU 507775000000 2 ((leaves.drop 25108).take 92) 510075000000 2 = true :=
    take_step (n := 2) (t := 92) (b := 25110) rfl rfl ArealUCore.ArealUK.chunk_12554 s55
  have s53 : leavesOK ctxLitU 507725000000 2 ((leaves.drop 25106).take 94) 510075000000 2 = true :=
    take_step (n := 2) (t := 94) (b := 25108) rfl rfl ArealUCore.ArealUK.chunk_12553 s54
  have s52 : leavesOK ctxLitU 507675000000 2 ((leaves.drop 25104).take 96) 510075000000 2 = true :=
    take_step (n := 2) (t := 96) (b := 25106) rfl rfl ArealUCore.ArealUK.chunk_12552 s53
  have s51 : leavesOK ctxLitU 507625000000 2 ((leaves.drop 25102).take 98) 510075000000 2 = true :=
    take_step (n := 2) (t := 98) (b := 25104) rfl rfl ArealUCore.ArealUK.chunk_12551 s52
  have s50 : leavesOK ctxLitU 507575000000 2 ((leaves.drop 25100).take 100) 510075000000 2 = true :=
    take_step (n := 2) (t := 100) (b := 25102) rfl rfl ArealUCore.ArealUK.chunk_12550 s51
  have s49 : leavesOK ctxLitU 507525000000 2 ((leaves.drop 25098).take 102) 510075000000 2 = true :=
    take_step (n := 2) (t := 102) (b := 25100) rfl rfl ArealUCore.ArealUK.chunk_12549 s50
  have s48 : leavesOK ctxLitU 507475000000 2 ((leaves.drop 25096).take 104) 510075000000 2 = true :=
    take_step (n := 2) (t := 104) (b := 25098) rfl rfl ArealUCore.ArealUK.chunk_12548 s49
  have s47 : leavesOK ctxLitU 507425000000 2 ((leaves.drop 25094).take 106) 510075000000 2 = true :=
    take_step (n := 2) (t := 106) (b := 25096) rfl rfl ArealUCore.ArealUK.chunk_12547 s48
  have s46 : leavesOK ctxLitU 507375000000 2 ((leaves.drop 25092).take 108) 510075000000 2 = true :=
    take_step (n := 2) (t := 108) (b := 25094) rfl rfl ArealUCore.ArealUK.chunk_12546 s47
  have s45 : leavesOK ctxLitU 507325000000 2 ((leaves.drop 25090).take 110) 510075000000 2 = true :=
    take_step (n := 2) (t := 110) (b := 25092) rfl rfl ArealUCore.ArealUK.chunk_12545 s46
  have s44 : leavesOK ctxLitU 507275000000 2 ((leaves.drop 25088).take 112) 510075000000 2 = true :=
    take_step (n := 2) (t := 112) (b := 25090) rfl rfl ArealUCore.ArealUK.chunk_12544 s45
  have s43 : leavesOK ctxLitU 507225000000 2 ((leaves.drop 25086).take 114) 510075000000 2 = true :=
    take_step (n := 2) (t := 114) (b := 25088) rfl rfl ArealUCore.ArealUK.chunk_12543 s44
  have s42 : leavesOK ctxLitU 507175000000 2 ((leaves.drop 25084).take 116) 510075000000 2 = true :=
    take_step (n := 2) (t := 116) (b := 25086) rfl rfl ArealUCore.ArealUK.chunk_12542 s43
  have s41 : leavesOK ctxLitU 507125000000 2 ((leaves.drop 25082).take 118) 510075000000 2 = true :=
    take_step (n := 2) (t := 118) (b := 25084) rfl rfl ArealUCore.ArealUK.chunk_12541 s42
  have s40 : leavesOK ctxLitU 507075000000 2 ((leaves.drop 25080).take 120) 510075000000 2 = true :=
    take_step (n := 2) (t := 120) (b := 25082) rfl rfl ArealUCore.ArealUK.chunk_12540 s41
  have s39 : leavesOK ctxLitU 507025000000 2 ((leaves.drop 25078).take 122) 510075000000 2 = true :=
    take_step (n := 2) (t := 122) (b := 25080) rfl rfl ArealUCore.ArealUK.chunk_12539 s40
  have s38 : leavesOK ctxLitU 506975000000 2 ((leaves.drop 25076).take 124) 510075000000 2 = true :=
    take_step (n := 2) (t := 124) (b := 25078) rfl rfl ArealUCore.ArealUK.chunk_12538 s39
  have s37 : leavesOK ctxLitU 506925000000 2 ((leaves.drop 25074).take 126) 510075000000 2 = true :=
    take_step (n := 2) (t := 126) (b := 25076) rfl rfl ArealUCore.ArealUK.chunk_12537 s38
  have s36 : leavesOK ctxLitU 506875000000 2 ((leaves.drop 25072).take 128) 510075000000 2 = true :=
    take_step (n := 2) (t := 128) (b := 25074) rfl rfl ArealUCore.ArealUK.chunk_12536 s37
  have s35 : leavesOK ctxLitU 506825000000 2 ((leaves.drop 25070).take 130) 510075000000 2 = true :=
    take_step (n := 2) (t := 130) (b := 25072) rfl rfl ArealUCore.ArealUK.chunk_12535 s36
  have s34 : leavesOK ctxLitU 506775000000 2 ((leaves.drop 25068).take 132) 510075000000 2 = true :=
    take_step (n := 2) (t := 132) (b := 25070) rfl rfl ArealUCore.ArealUK.chunk_12534 s35
  have s33 : leavesOK ctxLitU 506725000000 2 ((leaves.drop 25066).take 134) 510075000000 2 = true :=
    take_step (n := 2) (t := 134) (b := 25068) rfl rfl ArealUCore.ArealUK.chunk_12533 s34
  have s32 : leavesOK ctxLitU 506675000000 2 ((leaves.drop 25064).take 136) 510075000000 2 = true :=
    take_step (n := 2) (t := 136) (b := 25066) rfl rfl ArealUCore.ArealUK.chunk_12532 s33
  have s31 : leavesOK ctxLitU 506625000000 2 ((leaves.drop 25062).take 138) 510075000000 2 = true :=
    take_step (n := 2) (t := 138) (b := 25064) rfl rfl ArealUCore.ArealUK.chunk_12531 s32
  have s30 : leavesOK ctxLitU 506575000000 2 ((leaves.drop 25060).take 140) 510075000000 2 = true :=
    take_step (n := 2) (t := 140) (b := 25062) rfl rfl ArealUCore.ArealUK.chunk_12530 s31
  have s29 : leavesOK ctxLitU 506525000000 2 ((leaves.drop 25058).take 142) 510075000000 2 = true :=
    take_step (n := 2) (t := 142) (b := 25060) rfl rfl ArealUCore.ArealUK.chunk_12529 s30
  have s28 : leavesOK ctxLitU 506475000000 2 ((leaves.drop 25056).take 144) 510075000000 2 = true :=
    take_step (n := 2) (t := 144) (b := 25058) rfl rfl ArealUCore.ArealUK.chunk_12528 s29
  have s27 : leavesOK ctxLitU 506425000000 2 ((leaves.drop 25054).take 146) 510075000000 2 = true :=
    take_step (n := 2) (t := 146) (b := 25056) rfl rfl ArealUCore.ArealUK.chunk_12527 s28
  have s26 : leavesOK ctxLitU 506375000000 2 ((leaves.drop 25052).take 148) 510075000000 2 = true :=
    take_step (n := 2) (t := 148) (b := 25054) rfl rfl ArealUCore.ArealUK.chunk_12526 s27
  have s25 : leavesOK ctxLitU 506325000000 2 ((leaves.drop 25050).take 150) 510075000000 2 = true :=
    take_step (n := 2) (t := 150) (b := 25052) rfl rfl ArealUCore.ArealUK.chunk_12525 s26
  have s24 : leavesOK ctxLitU 506275000000 2 ((leaves.drop 25048).take 152) 510075000000 2 = true :=
    take_step (n := 2) (t := 152) (b := 25050) rfl rfl ArealUCore.ArealUK.chunk_12524 s25
  have s23 : leavesOK ctxLitU 506225000000 2 ((leaves.drop 25046).take 154) 510075000000 2 = true :=
    take_step (n := 2) (t := 154) (b := 25048) rfl rfl ArealUCore.ArealUK.chunk_12523 s24
  have s22 : leavesOK ctxLitU 506175000000 2 ((leaves.drop 25044).take 156) 510075000000 2 = true :=
    take_step (n := 2) (t := 156) (b := 25046) rfl rfl ArealUCore.ArealUK.chunk_12522 s23
  have s21 : leavesOK ctxLitU 506125000000 2 ((leaves.drop 25042).take 158) 510075000000 2 = true :=
    take_step (n := 2) (t := 158) (b := 25044) rfl rfl ArealUCore.ArealUK.chunk_12521 s22
  have s20 : leavesOK ctxLitU 506075000000 2 ((leaves.drop 25040).take 160) 510075000000 2 = true :=
    take_step (n := 2) (t := 160) (b := 25042) rfl rfl ArealUCore.ArealUK.chunk_12520 s21
  have s19 : leavesOK ctxLitU 506025000000 2 ((leaves.drop 25038).take 162) 510075000000 2 = true :=
    take_step (n := 2) (t := 162) (b := 25040) rfl rfl ArealUCore.ArealUK.chunk_12519 s20
  have s18 : leavesOK ctxLitU 505975000000 2 ((leaves.drop 25036).take 164) 510075000000 2 = true :=
    take_step (n := 2) (t := 164) (b := 25038) rfl rfl ArealUCore.ArealUK.chunk_12518 s19
  have s17 : leavesOK ctxLitU 505925000000 2 ((leaves.drop 25034).take 166) 510075000000 2 = true :=
    take_step (n := 2) (t := 166) (b := 25036) rfl rfl ArealUCore.ArealUK.chunk_12517 s18
  have s16 : leavesOK ctxLitU 505875000000 2 ((leaves.drop 25032).take 168) 510075000000 2 = true :=
    take_step (n := 2) (t := 168) (b := 25034) rfl rfl ArealUCore.ArealUK.chunk_12516 s17
  have s15 : leavesOK ctxLitU 505825000000 2 ((leaves.drop 25030).take 170) 510075000000 2 = true :=
    take_step (n := 2) (t := 170) (b := 25032) rfl rfl ArealUCore.ArealUK.chunk_12515 s16
  have s14 : leavesOK ctxLitU 1011600000000 3 ((leaves.drop 25028).take 172) 510075000000 2 = true :=
    take_step (n := 2) (t := 172) (b := 25030) rfl rfl ArealUCore.ArealUK.chunk_12514 s15
  have s13 : leavesOK ctxLitU 1011550000000 3 ((leaves.drop 25026).take 174) 510075000000 2 = true :=
    take_step (n := 2) (t := 174) (b := 25028) rfl rfl ArealUCore.ArealUK.chunk_12513 s14
  have s12 : leavesOK ctxLitU 505725000000 2 ((leaves.drop 25024).take 176) 510075000000 2 = true :=
    take_step (n := 2) (t := 176) (b := 25026) rfl rfl ArealUCore.ArealUK.chunk_12512 s13
  have s11 : leavesOK ctxLitU 505675000000 2 ((leaves.drop 25022).take 178) 510075000000 2 = true :=
    take_step (n := 2) (t := 178) (b := 25024) rfl rfl ArealUCore.ArealUK.chunk_12511 s12
  have s10 : leavesOK ctxLitU 505625000000 2 ((leaves.drop 25020).take 180) 510075000000 2 = true :=
    take_step (n := 2) (t := 180) (b := 25022) rfl rfl ArealUCore.ArealUK.chunk_12510 s11
  have s9 : leavesOK ctxLitU 505575000000 2 ((leaves.drop 25018).take 182) 510075000000 2 = true :=
    take_step (n := 2) (t := 182) (b := 25020) rfl rfl ArealUCore.ArealUK.chunk_12509 s10
  have s8 : leavesOK ctxLitU 505525000000 2 ((leaves.drop 25016).take 184) 510075000000 2 = true :=
    take_step (n := 2) (t := 184) (b := 25018) rfl rfl ArealUCore.ArealUK.chunk_12508 s9
  have s7 : leavesOK ctxLitU 252737500000 1 ((leaves.drop 25014).take 186) 510075000000 2 = true :=
    take_step (n := 2) (t := 186) (b := 25016) rfl rfl ArealUCore.ArealUK.chunk_12507 s8
  have s6 : leavesOK ctxLitU 126350000000 0 ((leaves.drop 25012).take 188) 510075000000 2 = true :=
    take_step (n := 2) (t := 188) (b := 25014) rfl rfl ArealUCore.ArealUK.chunk_12506 s7
  have s5 : leavesOK ctxLitU 126337500000 0 ((leaves.drop 25010).take 190) 510075000000 2 = true :=
    take_step (n := 2) (t := 190) (b := 25012) rfl rfl ArealUCore.ArealUK.chunk_12505 s6
  have s4 : leavesOK ctxLitU 252662500000 1 ((leaves.drop 25008).take 192) 510075000000 2 = true :=
    take_step (n := 2) (t := 192) (b := 25010) rfl rfl ArealUCore.ArealUK.chunk_12504 s5
  have s3 : leavesOK ctxLitU 252637500000 1 ((leaves.drop 25006).take 194) 510075000000 2 = true :=
    take_step (n := 2) (t := 194) (b := 25008) rfl rfl ArealUCore.ArealUK.chunk_12503 s4
  have s2 : leavesOK ctxLitU 252612500000 1 ((leaves.drop 25004).take 196) 510075000000 2 = true :=
    take_step (n := 2) (t := 196) (b := 25006) rfl rfl ArealUCore.ArealUK.chunk_12502 s3
  have s1 : leavesOK ctxLitU 505175000000 2 ((leaves.drop 25002).take 198) 510075000000 2 = true :=
    take_step (n := 2) (t := 198) (b := 25004) rfl rfl ArealUCore.ArealUK.chunk_12501 s2
  have s0 : leavesOK ctxLitU 505125000000 2 ((leaves.drop 25000).take 200) 510075000000 2 = true :=
    take_step (n := 2) (t := 200) (b := 25002) rfl rfl ArealUCore.ArealUK.chunk_12500 s1
  exact s0

end Areal.UCert

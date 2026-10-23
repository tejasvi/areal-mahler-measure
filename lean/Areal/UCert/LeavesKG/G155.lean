import ArealUK.Chunk15500
import ArealUK.Chunk15501
import ArealUK.Chunk15502
import ArealUK.Chunk15503
import ArealUK.Chunk15504
import ArealUK.Chunk15505
import ArealUK.Chunk15506
import ArealUK.Chunk15507
import ArealUK.Chunk15508
import ArealUK.Chunk15509
import ArealUK.Chunk15510
import ArealUK.Chunk15511
import ArealUK.Chunk15512
import ArealUK.Chunk15513
import ArealUK.Chunk15514
import ArealUK.Chunk15515
import ArealUK.Chunk15516
import ArealUK.Chunk15517
import ArealUK.Chunk15518
import ArealUK.Chunk15519
import ArealUK.Chunk15520
import ArealUK.Chunk15521
import ArealUK.Chunk15522
import ArealUK.Chunk15523
import ArealUK.Chunk15524
import ArealUK.Chunk15525
import ArealUK.Chunk15526
import ArealUK.Chunk15527
import ArealUK.Chunk15528
import ArealUK.Chunk15529
import ArealUK.Chunk15530
import ArealUK.Chunk15531
import ArealUK.Chunk15532
import ArealUK.Chunk15533
import ArealUK.Chunk15534
import ArealUK.Chunk15535
import ArealUK.Chunk15536
import ArealUK.Chunk15537
import ArealUK.Chunk15538
import ArealUK.Chunk15539
import ArealUK.Chunk15540
import ArealUK.Chunk15541
import ArealUK.Chunk15542
import ArealUK.Chunk15543
import ArealUK.Chunk15544
import ArealUK.Chunk15545
import ArealUK.Chunk15546
import ArealUK.Chunk15547
import ArealUK.Chunk15548
import ArealUK.Chunk15549
import ArealUK.Chunk15550
import ArealUK.Chunk15551
import ArealUK.Chunk15552
import ArealUK.Chunk15553
import ArealUK.Chunk15554
import ArealUK.Chunk15555
import ArealUK.Chunk15556
import ArealUK.Chunk15557
import ArealUK.Chunk15558
import ArealUK.Chunk15559
import ArealUK.Chunk15560
import ArealUK.Chunk15561
import ArealUK.Chunk15562
import ArealUK.Chunk15563
import ArealUK.Chunk15564
import ArealUK.Chunk15565
import ArealUK.Chunk15566
import ArealUK.Chunk15567
import ArealUK.Chunk15568
import ArealUK.Chunk15569
import ArealUK.Chunk15570
import ArealUK.Chunk15571
import ArealUK.Chunk15572
import ArealUK.Chunk15573
import ArealUK.Chunk15574
import ArealUK.Chunk15575
import ArealUK.Chunk15576
import ArealUK.Chunk15577
import ArealUK.Chunk15578
import ArealUK.Chunk15579
import ArealUK.Chunk15580
import ArealUK.Chunk15581
import ArealUK.Chunk15582
import ArealUK.Chunk15583
import ArealUK.Chunk15584
import ArealUK.Chunk15585
import ArealUK.Chunk15586
import ArealUK.Chunk15587
import ArealUK.Chunk15588
import ArealUK.Chunk15589
import ArealUK.Chunk15590
import ArealUK.Chunk15591
import ArealUK.Chunk15592
import ArealUK.Chunk15593
import ArealUK.Chunk15594
import ArealUK.Chunk15595
import ArealUK.Chunk15596
import ArealUK.Chunk15597
import ArealUK.Chunk15598
import ArealUK.Chunk15599
import Areal.UCert.LeavesKGen

/-! Group 155 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_155 : leavesOK ctxLitU 163650000000 0 ((leaves.drop 31000).take 200) 165162500000 0 = true := by
  have s99 := ArealUCore.ArealUK.chunk_15599
  have s98 : leavesOK ctxLitU 165131250000 0 ((leaves.drop 31196).take 4) 165162500000 0 = true :=
    take_step (n := 2) (t := 4) (b := 31198) rfl rfl ArealUCore.ArealUK.chunk_15598 s99
  have s97 : leavesOK ctxLitU 165118750000 0 ((leaves.drop 31194).take 6) 165162500000 0 = true :=
    take_step (n := 2) (t := 6) (b := 31196) rfl rfl ArealUCore.ArealUK.chunk_15597 s98
  have s96 : leavesOK ctxLitU 165106250000 0 ((leaves.drop 31192).take 8) 165162500000 0 = true :=
    take_step (n := 2) (t := 8) (b := 31194) rfl rfl ArealUCore.ArealUK.chunk_15596 s97
  have s95 : leavesOK ctxLitU 165087500000 0 ((leaves.drop 31190).take 10) 165162500000 0 = true :=
    take_step (n := 2) (t := 10) (b := 31192) rfl rfl ArealUCore.ArealUK.chunk_15595 s96
  have s94 : leavesOK ctxLitU 165068750000 0 ((leaves.drop 31188).take 12) 165162500000 0 = true :=
    take_step (n := 2) (t := 12) (b := 31190) rfl rfl ArealUCore.ArealUK.chunk_15594 s95
  have s93 : leavesOK ctxLitU 165056250000 0 ((leaves.drop 31186).take 14) 165162500000 0 = true :=
    take_step (n := 2) (t := 14) (b := 31188) rfl rfl ArealUCore.ArealUK.chunk_15593 s94
  have s92 : leavesOK ctxLitU 165043750000 0 ((leaves.drop 31184).take 16) 165162500000 0 = true :=
    take_step (n := 2) (t := 16) (b := 31186) rfl rfl ArealUCore.ArealUK.chunk_15592 s93
  have s91 : leavesOK ctxLitU 165031250000 0 ((leaves.drop 31182).take 18) 165162500000 0 = true :=
    take_step (n := 2) (t := 18) (b := 31184) rfl rfl ArealUCore.ArealUK.chunk_15591 s92
  have s90 : leavesOK ctxLitU 165018750000 0 ((leaves.drop 31180).take 20) 165162500000 0 = true :=
    take_step (n := 2) (t := 20) (b := 31182) rfl rfl ArealUCore.ArealUK.chunk_15590 s91
  have s89 : leavesOK ctxLitU 165006250000 0 ((leaves.drop 31178).take 22) 165162500000 0 = true :=
    take_step (n := 2) (t := 22) (b := 31180) rfl rfl ArealUCore.ArealUK.chunk_15589 s90
  have s88 : leavesOK ctxLitU 164993750000 0 ((leaves.drop 31176).take 24) 165162500000 0 = true :=
    take_step (n := 2) (t := 24) (b := 31178) rfl rfl ArealUCore.ArealUK.chunk_15588 s89
  have s87 : leavesOK ctxLitU 164981250000 0 ((leaves.drop 31174).take 26) 165162500000 0 = true :=
    take_step (n := 2) (t := 26) (b := 31176) rfl rfl ArealUCore.ArealUK.chunk_15587 s88
  have s86 : leavesOK ctxLitU 164968750000 0 ((leaves.drop 31172).take 28) 165162500000 0 = true :=
    take_step (n := 2) (t := 28) (b := 31174) rfl rfl ArealUCore.ArealUK.chunk_15586 s87
  have s85 : leavesOK ctxLitU 164956250000 0 ((leaves.drop 31170).take 30) 165162500000 0 = true :=
    take_step (n := 2) (t := 30) (b := 31172) rfl rfl ArealUCore.ArealUK.chunk_15585 s86
  have s84 : leavesOK ctxLitU 164943750000 0 ((leaves.drop 31168).take 32) 165162500000 0 = true :=
    take_step (n := 2) (t := 32) (b := 31170) rfl rfl ArealUCore.ArealUK.chunk_15584 s85
  have s83 : leavesOK ctxLitU 164931250000 0 ((leaves.drop 31166).take 34) 165162500000 0 = true :=
    take_step (n := 2) (t := 34) (b := 31168) rfl rfl ArealUCore.ArealUK.chunk_15583 s84
  have s82 : leavesOK ctxLitU 164918750000 0 ((leaves.drop 31164).take 36) 165162500000 0 = true :=
    take_step (n := 2) (t := 36) (b := 31166) rfl rfl ArealUCore.ArealUK.chunk_15582 s83
  have s81 : leavesOK ctxLitU 164906250000 0 ((leaves.drop 31162).take 38) 165162500000 0 = true :=
    take_step (n := 2) (t := 38) (b := 31164) rfl rfl ArealUCore.ArealUK.chunk_15581 s82
  have s80 : leavesOK ctxLitU 164887500000 0 ((leaves.drop 31160).take 40) 165162500000 0 = true :=
    take_step (n := 2) (t := 40) (b := 31162) rfl rfl ArealUCore.ArealUK.chunk_15580 s81
  have s79 : leavesOK ctxLitU 164868750000 0 ((leaves.drop 31158).take 42) 165162500000 0 = true :=
    take_step (n := 2) (t := 42) (b := 31160) rfl rfl ArealUCore.ArealUK.chunk_15579 s80
  have s78 : leavesOK ctxLitU 164856250000 0 ((leaves.drop 31156).take 44) 165162500000 0 = true :=
    take_step (n := 2) (t := 44) (b := 31158) rfl rfl ArealUCore.ArealUK.chunk_15578 s79
  have s77 : leavesOK ctxLitU 164843750000 0 ((leaves.drop 31154).take 46) 165162500000 0 = true :=
    take_step (n := 2) (t := 46) (b := 31156) rfl rfl ArealUCore.ArealUK.chunk_15577 s78
  have s76 : leavesOK ctxLitU 164831250000 0 ((leaves.drop 31152).take 48) 165162500000 0 = true :=
    take_step (n := 2) (t := 48) (b := 31154) rfl rfl ArealUCore.ArealUK.chunk_15576 s77
  have s75 : leavesOK ctxLitU 164818750000 0 ((leaves.drop 31150).take 50) 165162500000 0 = true :=
    take_step (n := 2) (t := 50) (b := 31152) rfl rfl ArealUCore.ArealUK.chunk_15575 s76
  have s74 : leavesOK ctxLitU 164806250000 0 ((leaves.drop 31148).take 52) 165162500000 0 = true :=
    take_step (n := 2) (t := 52) (b := 31150) rfl rfl ArealUCore.ArealUK.chunk_15574 s75
  have s73 : leavesOK ctxLitU 164793750000 0 ((leaves.drop 31146).take 54) 165162500000 0 = true :=
    take_step (n := 2) (t := 54) (b := 31148) rfl rfl ArealUCore.ArealUK.chunk_15573 s74
  have s72 : leavesOK ctxLitU 164781250000 0 ((leaves.drop 31144).take 56) 165162500000 0 = true :=
    take_step (n := 2) (t := 56) (b := 31146) rfl rfl ArealUCore.ArealUK.chunk_15572 s73
  have s71 : leavesOK ctxLitU 164768750000 0 ((leaves.drop 31142).take 58) 165162500000 0 = true :=
    take_step (n := 2) (t := 58) (b := 31144) rfl rfl ArealUCore.ArealUK.chunk_15571 s72
  have s70 : leavesOK ctxLitU 164756250000 0 ((leaves.drop 31140).take 60) 165162500000 0 = true :=
    take_step (n := 2) (t := 60) (b := 31142) rfl rfl ArealUCore.ArealUK.chunk_15570 s71
  have s69 : leavesOK ctxLitU 164743750000 0 ((leaves.drop 31138).take 62) 165162500000 0 = true :=
    take_step (n := 2) (t := 62) (b := 31140) rfl rfl ArealUCore.ArealUK.chunk_15569 s70
  have s68 : leavesOK ctxLitU 164731250000 0 ((leaves.drop 31136).take 64) 165162500000 0 = true :=
    take_step (n := 2) (t := 64) (b := 31138) rfl rfl ArealUCore.ArealUK.chunk_15568 s69
  have s67 : leavesOK ctxLitU 164712500000 0 ((leaves.drop 31134).take 66) 165162500000 0 = true :=
    take_step (n := 2) (t := 66) (b := 31136) rfl rfl ArealUCore.ArealUK.chunk_15567 s68
  have s66 : leavesOK ctxLitU 164687500000 0 ((leaves.drop 31132).take 68) 165162500000 0 = true :=
    take_step (n := 2) (t := 68) (b := 31134) rfl rfl ArealUCore.ArealUK.chunk_15566 s67
  have s65 : leavesOK ctxLitU 164668750000 0 ((leaves.drop 31130).take 70) 165162500000 0 = true :=
    take_step (n := 2) (t := 70) (b := 31132) rfl rfl ArealUCore.ArealUK.chunk_15565 s66
  have s64 : leavesOK ctxLitU 164656250000 0 ((leaves.drop 31128).take 72) 165162500000 0 = true :=
    take_step (n := 2) (t := 72) (b := 31130) rfl rfl ArealUCore.ArealUK.chunk_15564 s65
  have s63 : leavesOK ctxLitU 164643750000 0 ((leaves.drop 31126).take 74) 165162500000 0 = true :=
    take_step (n := 2) (t := 74) (b := 31128) rfl rfl ArealUCore.ArealUK.chunk_15563 s64
  have s62 : leavesOK ctxLitU 164631250000 0 ((leaves.drop 31124).take 76) 165162500000 0 = true :=
    take_step (n := 2) (t := 76) (b := 31126) rfl rfl ArealUCore.ArealUK.chunk_15562 s63
  have s61 : leavesOK ctxLitU 164612500000 0 ((leaves.drop 31122).take 78) 165162500000 0 = true :=
    take_step (n := 2) (t := 78) (b := 31124) rfl rfl ArealUCore.ArealUK.chunk_15561 s62
  have s60 : leavesOK ctxLitU 164587500000 0 ((leaves.drop 31120).take 80) 165162500000 0 = true :=
    take_step (n := 2) (t := 80) (b := 31122) rfl rfl ArealUCore.ArealUK.chunk_15560 s61
  have s59 : leavesOK ctxLitU 164568750000 0 ((leaves.drop 31118).take 82) 165162500000 0 = true :=
    take_step (n := 2) (t := 82) (b := 31120) rfl rfl ArealUCore.ArealUK.chunk_15559 s60
  have s58 : leavesOK ctxLitU 164556250000 0 ((leaves.drop 31116).take 84) 165162500000 0 = true :=
    take_step (n := 2) (t := 84) (b := 31118) rfl rfl ArealUCore.ArealUK.chunk_15558 s59
  have s57 : leavesOK ctxLitU 164543750000 0 ((leaves.drop 31114).take 86) 165162500000 0 = true :=
    take_step (n := 2) (t := 86) (b := 31116) rfl rfl ArealUCore.ArealUK.chunk_15557 s58
  have s56 : leavesOK ctxLitU 164531250000 0 ((leaves.drop 31112).take 88) 165162500000 0 = true :=
    take_step (n := 2) (t := 88) (b := 31114) rfl rfl ArealUCore.ArealUK.chunk_15556 s57
  have s55 : leavesOK ctxLitU 164512500000 0 ((leaves.drop 31110).take 90) 165162500000 0 = true :=
    take_step (n := 2) (t := 90) (b := 31112) rfl rfl ArealUCore.ArealUK.chunk_15555 s56
  have s54 : leavesOK ctxLitU 329000000000 1 ((leaves.drop 31108).take 92) 165162500000 0 = true :=
    take_step (n := 2) (t := 92) (b := 31110) rfl rfl ArealUCore.ArealUK.chunk_15554 s55
  have s53 : leavesOK ctxLitU 164475000000 0 ((leaves.drop 31106).take 94) 165162500000 0 = true :=
    take_step (n := 2) (t := 94) (b := 31108) rfl rfl ArealUCore.ArealUK.chunk_15553 s54
  have s52 : leavesOK ctxLitU 164462500000 0 ((leaves.drop 31104).take 96) 165162500000 0 = true :=
    take_step (n := 2) (t := 96) (b := 31106) rfl rfl ArealUCore.ArealUK.chunk_15552 s53
  have s51 : leavesOK ctxLitU 164450000000 0 ((leaves.drop 31102).take 98) 165162500000 0 = true :=
    take_step (n := 2) (t := 98) (b := 31104) rfl rfl ArealUCore.ArealUK.chunk_15551 s52
  have s50 : leavesOK ctxLitU 164437500000 0 ((leaves.drop 31100).take 100) 165162500000 0 = true :=
    take_step (n := 2) (t := 100) (b := 31102) rfl rfl ArealUCore.ArealUK.chunk_15550 s51
  have s49 : leavesOK ctxLitU 164425000000 0 ((leaves.drop 31098).take 102) 165162500000 0 = true :=
    take_step (n := 2) (t := 102) (b := 31100) rfl rfl ArealUCore.ArealUK.chunk_15549 s50
  have s48 : leavesOK ctxLitU 164412500000 0 ((leaves.drop 31096).take 104) 165162500000 0 = true :=
    take_step (n := 2) (t := 104) (b := 31098) rfl rfl ArealUCore.ArealUK.chunk_15548 s49
  have s47 : leavesOK ctxLitU 164400000000 0 ((leaves.drop 31094).take 106) 165162500000 0 = true :=
    take_step (n := 2) (t := 106) (b := 31096) rfl rfl ArealUCore.ArealUK.chunk_15547 s48
  have s46 : leavesOK ctxLitU 164387500000 0 ((leaves.drop 31092).take 108) 165162500000 0 = true :=
    take_step (n := 2) (t := 108) (b := 31094) rfl rfl ArealUCore.ArealUK.chunk_15546 s47
  have s45 : leavesOK ctxLitU 164375000000 0 ((leaves.drop 31090).take 110) 165162500000 0 = true :=
    take_step (n := 2) (t := 110) (b := 31092) rfl rfl ArealUCore.ArealUK.chunk_15545 s46
  have s44 : leavesOK ctxLitU 164362500000 0 ((leaves.drop 31088).take 112) 165162500000 0 = true :=
    take_step (n := 2) (t := 112) (b := 31090) rfl rfl ArealUCore.ArealUK.chunk_15544 s45
  have s43 : leavesOK ctxLitU 164350000000 0 ((leaves.drop 31086).take 114) 165162500000 0 = true :=
    take_step (n := 2) (t := 114) (b := 31088) rfl rfl ArealUCore.ArealUK.chunk_15543 s44
  have s42 : leavesOK ctxLitU 164337500000 0 ((leaves.drop 31084).take 116) 165162500000 0 = true :=
    take_step (n := 2) (t := 116) (b := 31086) rfl rfl ArealUCore.ArealUK.chunk_15542 s43
  have s41 : leavesOK ctxLitU 164325000000 0 ((leaves.drop 31082).take 118) 165162500000 0 = true :=
    take_step (n := 2) (t := 118) (b := 31084) rfl rfl ArealUCore.ArealUK.chunk_15541 s42
  have s40 : leavesOK ctxLitU 328625000000 1 ((leaves.drop 31080).take 120) 165162500000 0 = true :=
    take_step (n := 2) (t := 120) (b := 31082) rfl rfl ArealUCore.ArealUK.chunk_15540 s41
  have s39 : leavesOK ctxLitU 328600000000 1 ((leaves.drop 31078).take 122) 165162500000 0 = true :=
    take_step (n := 2) (t := 122) (b := 31080) rfl rfl ArealUCore.ArealUK.chunk_15539 s40
  have s38 : leavesOK ctxLitU 328550000000 1 ((leaves.drop 31076).take 124) 165162500000 0 = true :=
    take_step (n := 2) (t := 124) (b := 31078) rfl rfl ArealUCore.ArealUK.chunk_15538 s39
  have s37 : leavesOK ctxLitU 328500000000 1 ((leaves.drop 31074).take 126) 165162500000 0 = true :=
    take_step (n := 2) (t := 126) (b := 31076) rfl rfl ArealUCore.ArealUK.chunk_15537 s38
  have s36 : leavesOK ctxLitU 328450000000 1 ((leaves.drop 31072).take 128) 165162500000 0 = true :=
    take_step (n := 2) (t := 128) (b := 31074) rfl rfl ArealUCore.ArealUK.chunk_15536 s37
  have s35 : leavesOK ctxLitU 328400000000 1 ((leaves.drop 31070).take 130) 165162500000 0 = true :=
    take_step (n := 2) (t := 130) (b := 31072) rfl rfl ArealUCore.ArealUK.chunk_15535 s36
  have s34 : leavesOK ctxLitU 164175000000 0 ((leaves.drop 31068).take 132) 165162500000 0 = true :=
    take_step (n := 2) (t := 132) (b := 31070) rfl rfl ArealUCore.ArealUK.chunk_15534 s35
  have s33 : leavesOK ctxLitU 164162500000 0 ((leaves.drop 31066).take 134) 165162500000 0 = true :=
    take_step (n := 2) (t := 134) (b := 31068) rfl rfl ArealUCore.ArealUK.chunk_15533 s34
  have s32 : leavesOK ctxLitU 164150000000 0 ((leaves.drop 31064).take 136) 165162500000 0 = true :=
    take_step (n := 2) (t := 136) (b := 31066) rfl rfl ArealUCore.ArealUK.chunk_15532 s33
  have s31 : leavesOK ctxLitU 164137500000 0 ((leaves.drop 31062).take 138) 165162500000 0 = true :=
    take_step (n := 2) (t := 138) (b := 31064) rfl rfl ArealUCore.ArealUK.chunk_15531 s32
  have s30 : leavesOK ctxLitU 164125000000 0 ((leaves.drop 31060).take 140) 165162500000 0 = true :=
    take_step (n := 2) (t := 140) (b := 31062) rfl rfl ArealUCore.ArealUK.chunk_15530 s31
  have s29 : leavesOK ctxLitU 656462500000 2 ((leaves.drop 31058).take 142) 165162500000 0 = true :=
    take_step (n := 2) (t := 142) (b := 31060) rfl rfl ArealUCore.ArealUK.chunk_15529 s30
  have s28 : leavesOK ctxLitU 656437500000 2 ((leaves.drop 31056).take 144) 165162500000 0 = true :=
    take_step (n := 2) (t := 144) (b := 31058) rfl rfl ArealUCore.ArealUK.chunk_15528 s29
  have s27 : leavesOK ctxLitU 328200000000 1 ((leaves.drop 31054).take 146) 165162500000 0 = true :=
    take_step (n := 2) (t := 146) (b := 31056) rfl rfl ArealUCore.ArealUK.chunk_15527 s28
  have s26 : leavesOK ctxLitU 328150000000 1 ((leaves.drop 31052).take 148) 165162500000 0 = true :=
    take_step (n := 2) (t := 148) (b := 31054) rfl rfl ArealUCore.ArealUK.chunk_15526 s27
  have s25 : leavesOK ctxLitU 328100000000 1 ((leaves.drop 31050).take 150) 165162500000 0 = true :=
    take_step (n := 2) (t := 150) (b := 31052) rfl rfl ArealUCore.ArealUK.chunk_15525 s26
  have s24 : leavesOK ctxLitU 328050000000 1 ((leaves.drop 31048).take 152) 165162500000 0 = true :=
    take_step (n := 2) (t := 152) (b := 31050) rfl rfl ArealUCore.ArealUK.chunk_15524 s25
  have s23 : leavesOK ctxLitU 328000000000 1 ((leaves.drop 31046).take 154) 165162500000 0 = true :=
    take_step (n := 2) (t := 154) (b := 31048) rfl rfl ArealUCore.ArealUK.chunk_15523 s24
  have s22 : leavesOK ctxLitU 163975000000 0 ((leaves.drop 31044).take 156) 165162500000 0 = true :=
    take_step (n := 2) (t := 156) (b := 31046) rfl rfl ArealUCore.ArealUK.chunk_15522 s23
  have s21 : leavesOK ctxLitU 163962500000 0 ((leaves.drop 31042).take 158) 165162500000 0 = true :=
    take_step (n := 2) (t := 158) (b := 31044) rfl rfl ArealUCore.ArealUK.chunk_15521 s22
  have s20 : leavesOK ctxLitU 163950000000 0 ((leaves.drop 31040).take 160) 165162500000 0 = true :=
    take_step (n := 2) (t := 160) (b := 31042) rfl rfl ArealUCore.ArealUK.chunk_15520 s21
  have s19 : leavesOK ctxLitU 163937500000 0 ((leaves.drop 31038).take 162) 165162500000 0 = true :=
    take_step (n := 2) (t := 162) (b := 31040) rfl rfl ArealUCore.ArealUK.chunk_15519 s20
  have s18 : leavesOK ctxLitU 163925000000 0 ((leaves.drop 31036).take 164) 165162500000 0 = true :=
    take_step (n := 2) (t := 164) (b := 31038) rfl rfl ArealUCore.ArealUK.chunk_15518 s19
  have s17 : leavesOK ctxLitU 163900000000 0 ((leaves.drop 31034).take 166) 165162500000 0 = true :=
    take_step (n := 2) (t := 166) (b := 31036) rfl rfl ArealUCore.ArealUK.chunk_15517 s18
  have s16 : leavesOK ctxLitU 327775000000 1 ((leaves.drop 31032).take 168) 165162500000 0 = true :=
    take_step (n := 2) (t := 168) (b := 31034) rfl rfl ArealUCore.ArealUK.chunk_15516 s17
  have s15 : leavesOK ctxLitU 327750000000 1 ((leaves.drop 31030).take 170) 165162500000 0 = true :=
    take_step (n := 2) (t := 170) (b := 31032) rfl rfl ArealUCore.ArealUK.chunk_15515 s16
  have s14 : leavesOK ctxLitU 163862500000 0 ((leaves.drop 31028).take 172) 165162500000 0 = true :=
    take_step (n := 2) (t := 172) (b := 31030) rfl rfl ArealUCore.ArealUK.chunk_15514 s15
  have s13 : leavesOK ctxLitU 163850000000 0 ((leaves.drop 31026).take 174) 165162500000 0 = true :=
    take_step (n := 2) (t := 174) (b := 31028) rfl rfl ArealUCore.ArealUK.chunk_15513 s14
  have s12 : leavesOK ctxLitU 163825000000 0 ((leaves.drop 31024).take 176) 165162500000 0 = true :=
    take_step (n := 2) (t := 176) (b := 31026) rfl rfl ArealUCore.ArealUK.chunk_15512 s13
  have s11 : leavesOK ctxLitU 163812500000 0 ((leaves.drop 31022).take 178) 165162500000 0 = true :=
    take_step (n := 2) (t := 178) (b := 31024) rfl rfl ArealUCore.ArealUK.chunk_15511 s12
  have s10 : leavesOK ctxLitU 163800000000 0 ((leaves.drop 31020).take 180) 165162500000 0 = true :=
    take_step (n := 2) (t := 180) (b := 31022) rfl rfl ArealUCore.ArealUK.chunk_15510 s11
  have s9 : leavesOK ctxLitU 163787500000 0 ((leaves.drop 31018).take 182) 165162500000 0 = true :=
    take_step (n := 2) (t := 182) (b := 31020) rfl rfl ArealUCore.ArealUK.chunk_15509 s10
  have s8 : leavesOK ctxLitU 163775000000 0 ((leaves.drop 31016).take 184) 165162500000 0 = true :=
    take_step (n := 2) (t := 184) (b := 31018) rfl rfl ArealUCore.ArealUK.chunk_15508 s9
  have s7 : leavesOK ctxLitU 163762500000 0 ((leaves.drop 31014).take 186) 165162500000 0 = true :=
    take_step (n := 2) (t := 186) (b := 31016) rfl rfl ArealUCore.ArealUK.chunk_15507 s8
  have s6 : leavesOK ctxLitU 163750000000 0 ((leaves.drop 31012).take 188) 165162500000 0 = true :=
    take_step (n := 2) (t := 188) (b := 31014) rfl rfl ArealUCore.ArealUK.chunk_15506 s7
  have s5 : leavesOK ctxLitU 163737500000 0 ((leaves.drop 31010).take 190) 165162500000 0 = true :=
    take_step (n := 2) (t := 190) (b := 31012) rfl rfl ArealUCore.ArealUK.chunk_15505 s6
  have s4 : leavesOK ctxLitU 163725000000 0 ((leaves.drop 31008).take 192) 165162500000 0 = true :=
    take_step (n := 2) (t := 192) (b := 31010) rfl rfl ArealUCore.ArealUK.chunk_15504 s5
  have s3 : leavesOK ctxLitU 163700000000 0 ((leaves.drop 31006).take 194) 165162500000 0 = true :=
    take_step (n := 2) (t := 194) (b := 31008) rfl rfl ArealUCore.ArealUK.chunk_15503 s4
  have s2 : leavesOK ctxLitU 163675000000 0 ((leaves.drop 31004).take 196) 165162500000 0 = true :=
    take_step (n := 2) (t := 196) (b := 31006) rfl rfl ArealUCore.ArealUK.chunk_15502 s3
  have s1 : leavesOK ctxLitU 163662500000 0 ((leaves.drop 31002).take 198) 165162500000 0 = true :=
    take_step (n := 2) (t := 198) (b := 31004) rfl rfl ArealUCore.ArealUK.chunk_15501 s2
  have s0 : leavesOK ctxLitU 163650000000 0 ((leaves.drop 31000).take 200) 165162500000 0 = true :=
    take_step (n := 2) (t := 200) (b := 31002) rfl rfl ArealUCore.ArealUK.chunk_15500 s1
  exact s0

end Areal.UCert

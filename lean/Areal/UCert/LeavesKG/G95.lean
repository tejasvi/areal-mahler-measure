import ArealUK.Chunk9500
import ArealUK.Chunk9501
import ArealUK.Chunk9502
import ArealUK.Chunk9503
import ArealUK.Chunk9504
import ArealUK.Chunk9505
import ArealUK.Chunk9506
import ArealUK.Chunk9507
import ArealUK.Chunk9508
import ArealUK.Chunk9509
import ArealUK.Chunk9510
import ArealUK.Chunk9511
import ArealUK.Chunk9512
import ArealUK.Chunk9513
import ArealUK.Chunk9514
import ArealUK.Chunk9515
import ArealUK.Chunk9516
import ArealUK.Chunk9517
import ArealUK.Chunk9518
import ArealUK.Chunk9519
import ArealUK.Chunk9520
import ArealUK.Chunk9521
import ArealUK.Chunk9522
import ArealUK.Chunk9523
import ArealUK.Chunk9524
import ArealUK.Chunk9525
import ArealUK.Chunk9526
import ArealUK.Chunk9527
import ArealUK.Chunk9528
import ArealUK.Chunk9529
import ArealUK.Chunk9530
import ArealUK.Chunk9531
import ArealUK.Chunk9532
import ArealUK.Chunk9533
import ArealUK.Chunk9534
import ArealUK.Chunk9535
import ArealUK.Chunk9536
import ArealUK.Chunk9537
import ArealUK.Chunk9538
import ArealUK.Chunk9539
import ArealUK.Chunk9540
import ArealUK.Chunk9541
import ArealUK.Chunk9542
import ArealUK.Chunk9543
import ArealUK.Chunk9544
import ArealUK.Chunk9545
import ArealUK.Chunk9546
import ArealUK.Chunk9547
import ArealUK.Chunk9548
import ArealUK.Chunk9549
import ArealUK.Chunk9550
import ArealUK.Chunk9551
import ArealUK.Chunk9552
import ArealUK.Chunk9553
import ArealUK.Chunk9554
import ArealUK.Chunk9555
import ArealUK.Chunk9556
import ArealUK.Chunk9557
import ArealUK.Chunk9558
import ArealUK.Chunk9559
import ArealUK.Chunk9560
import ArealUK.Chunk9561
import ArealUK.Chunk9562
import ArealUK.Chunk9563
import ArealUK.Chunk9564
import ArealUK.Chunk9565
import ArealUK.Chunk9566
import ArealUK.Chunk9567
import ArealUK.Chunk9568
import ArealUK.Chunk9569
import ArealUK.Chunk9570
import ArealUK.Chunk9571
import ArealUK.Chunk9572
import ArealUK.Chunk9573
import ArealUK.Chunk9574
import ArealUK.Chunk9575
import ArealUK.Chunk9576
import ArealUK.Chunk9577
import ArealUK.Chunk9578
import ArealUK.Chunk9579
import ArealUK.Chunk9580
import ArealUK.Chunk9581
import ArealUK.Chunk9582
import ArealUK.Chunk9583
import ArealUK.Chunk9584
import ArealUK.Chunk9585
import ArealUK.Chunk9586
import ArealUK.Chunk9587
import ArealUK.Chunk9588
import ArealUK.Chunk9589
import ArealUK.Chunk9590
import ArealUK.Chunk9591
import ArealUK.Chunk9592
import ArealUK.Chunk9593
import ArealUK.Chunk9594
import ArealUK.Chunk9595
import ArealUK.Chunk9596
import ArealUK.Chunk9597
import ArealUK.Chunk9598
import ArealUK.Chunk9599
import Areal.UCert.LeavesKGen

/-! Group 95 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_95 : leavesOK ctxLitU 329875000000 2 ((leaves.drop 19000).take 200) 334875000000 2 = true := by
  have s99 := ArealUCore.ArealUK.chunk_9599
  have s98 : leavesOK ctxLitU 334775000000 2 ((leaves.drop 19196).take 4) 334875000000 2 = true :=
    take_step (n := 2) (t := 4) (b := 19198) rfl rfl ArealUCore.ArealUK.chunk_9598 s99
  have s97 : leavesOK ctxLitU 334725000000 2 ((leaves.drop 19194).take 6) 334875000000 2 = true :=
    take_step (n := 2) (t := 6) (b := 19196) rfl rfl ArealUCore.ArealUK.chunk_9597 s98
  have s96 : leavesOK ctxLitU 334675000000 2 ((leaves.drop 19192).take 8) 334875000000 2 = true :=
    take_step (n := 2) (t := 8) (b := 19194) rfl rfl ArealUCore.ArealUK.chunk_9596 s97
  have s95 : leavesOK ctxLitU 334625000000 2 ((leaves.drop 19190).take 10) 334875000000 2 = true :=
    take_step (n := 2) (t := 10) (b := 19192) rfl rfl ArealUCore.ArealUK.chunk_9595 s96
  have s94 : leavesOK ctxLitU 334575000000 2 ((leaves.drop 19188).take 12) 334875000000 2 = true :=
    take_step (n := 2) (t := 12) (b := 19190) rfl rfl ArealUCore.ArealUK.chunk_9594 s95
  have s93 : leavesOK ctxLitU 334525000000 2 ((leaves.drop 19186).take 14) 334875000000 2 = true :=
    take_step (n := 2) (t := 14) (b := 19188) rfl rfl ArealUCore.ArealUK.chunk_9593 s94
  have s92 : leavesOK ctxLitU 334475000000 2 ((leaves.drop 19184).take 16) 334875000000 2 = true :=
    take_step (n := 2) (t := 16) (b := 19186) rfl rfl ArealUCore.ArealUK.chunk_9592 s93
  have s91 : leavesOK ctxLitU 334425000000 2 ((leaves.drop 19182).take 18) 334875000000 2 = true :=
    take_step (n := 2) (t := 18) (b := 19184) rfl rfl ArealUCore.ArealUK.chunk_9591 s92
  have s90 : leavesOK ctxLitU 334375000000 2 ((leaves.drop 19180).take 20) 334875000000 2 = true :=
    take_step (n := 2) (t := 20) (b := 19182) rfl rfl ArealUCore.ArealUK.chunk_9590 s91
  have s89 : leavesOK ctxLitU 334325000000 2 ((leaves.drop 19178).take 22) 334875000000 2 = true :=
    take_step (n := 2) (t := 22) (b := 19180) rfl rfl ArealUCore.ArealUK.chunk_9589 s90
  have s88 : leavesOK ctxLitU 334275000000 2 ((leaves.drop 19176).take 24) 334875000000 2 = true :=
    take_step (n := 2) (t := 24) (b := 19178) rfl rfl ArealUCore.ArealUK.chunk_9588 s89
  have s87 : leavesOK ctxLitU 334225000000 2 ((leaves.drop 19174).take 26) 334875000000 2 = true :=
    take_step (n := 2) (t := 26) (b := 19176) rfl rfl ArealUCore.ArealUK.chunk_9587 s88
  have s86 : leavesOK ctxLitU 334175000000 2 ((leaves.drop 19172).take 28) 334875000000 2 = true :=
    take_step (n := 2) (t := 28) (b := 19174) rfl rfl ArealUCore.ArealUK.chunk_9586 s87
  have s85 : leavesOK ctxLitU 334125000000 2 ((leaves.drop 19170).take 30) 334875000000 2 = true :=
    take_step (n := 2) (t := 30) (b := 19172) rfl rfl ArealUCore.ArealUK.chunk_9585 s86
  have s84 : leavesOK ctxLitU 334075000000 2 ((leaves.drop 19168).take 32) 334875000000 2 = true :=
    take_step (n := 2) (t := 32) (b := 19170) rfl rfl ArealUCore.ArealUK.chunk_9584 s85
  have s83 : leavesOK ctxLitU 334025000000 2 ((leaves.drop 19166).take 34) 334875000000 2 = true :=
    take_step (n := 2) (t := 34) (b := 19168) rfl rfl ArealUCore.ArealUK.chunk_9583 s84
  have s82 : leavesOK ctxLitU 333975000000 2 ((leaves.drop 19164).take 36) 334875000000 2 = true :=
    take_step (n := 2) (t := 36) (b := 19166) rfl rfl ArealUCore.ArealUK.chunk_9582 s83
  have s81 : leavesOK ctxLitU 333925000000 2 ((leaves.drop 19162).take 38) 334875000000 2 = true :=
    take_step (n := 2) (t := 38) (b := 19164) rfl rfl ArealUCore.ArealUK.chunk_9581 s82
  have s80 : leavesOK ctxLitU 333875000000 2 ((leaves.drop 19160).take 40) 334875000000 2 = true :=
    take_step (n := 2) (t := 40) (b := 19162) rfl rfl ArealUCore.ArealUK.chunk_9580 s81
  have s79 : leavesOK ctxLitU 333825000000 2 ((leaves.drop 19158).take 42) 334875000000 2 = true :=
    take_step (n := 2) (t := 42) (b := 19160) rfl rfl ArealUCore.ArealUK.chunk_9579 s80
  have s78 : leavesOK ctxLitU 333775000000 2 ((leaves.drop 19156).take 44) 334875000000 2 = true :=
    take_step (n := 2) (t := 44) (b := 19158) rfl rfl ArealUCore.ArealUK.chunk_9578 s79
  have s77 : leavesOK ctxLitU 333725000000 2 ((leaves.drop 19154).take 46) 334875000000 2 = true :=
    take_step (n := 2) (t := 46) (b := 19156) rfl rfl ArealUCore.ArealUK.chunk_9577 s78
  have s76 : leavesOK ctxLitU 333675000000 2 ((leaves.drop 19152).take 48) 334875000000 2 = true :=
    take_step (n := 2) (t := 48) (b := 19154) rfl rfl ArealUCore.ArealUK.chunk_9576 s77
  have s75 : leavesOK ctxLitU 333625000000 2 ((leaves.drop 19150).take 50) 334875000000 2 = true :=
    take_step (n := 2) (t := 50) (b := 19152) rfl rfl ArealUCore.ArealUK.chunk_9575 s76
  have s74 : leavesOK ctxLitU 333575000000 2 ((leaves.drop 19148).take 52) 334875000000 2 = true :=
    take_step (n := 2) (t := 52) (b := 19150) rfl rfl ArealUCore.ArealUK.chunk_9574 s75
  have s73 : leavesOK ctxLitU 333525000000 2 ((leaves.drop 19146).take 54) 334875000000 2 = true :=
    take_step (n := 2) (t := 54) (b := 19148) rfl rfl ArealUCore.ArealUK.chunk_9573 s74
  have s72 : leavesOK ctxLitU 333475000000 2 ((leaves.drop 19144).take 56) 334875000000 2 = true :=
    take_step (n := 2) (t := 56) (b := 19146) rfl rfl ArealUCore.ArealUK.chunk_9572 s73
  have s71 : leavesOK ctxLitU 333425000000 2 ((leaves.drop 19142).take 58) 334875000000 2 = true :=
    take_step (n := 2) (t := 58) (b := 19144) rfl rfl ArealUCore.ArealUK.chunk_9571 s72
  have s70 : leavesOK ctxLitU 333375000000 2 ((leaves.drop 19140).take 60) 334875000000 2 = true :=
    take_step (n := 2) (t := 60) (b := 19142) rfl rfl ArealUCore.ArealUK.chunk_9570 s71
  have s69 : leavesOK ctxLitU 333325000000 2 ((leaves.drop 19138).take 62) 334875000000 2 = true :=
    take_step (n := 2) (t := 62) (b := 19140) rfl rfl ArealUCore.ArealUK.chunk_9569 s70
  have s68 : leavesOK ctxLitU 333275000000 2 ((leaves.drop 19136).take 64) 334875000000 2 = true :=
    take_step (n := 2) (t := 64) (b := 19138) rfl rfl ArealUCore.ArealUK.chunk_9568 s69
  have s67 : leavesOK ctxLitU 333225000000 2 ((leaves.drop 19134).take 66) 334875000000 2 = true :=
    take_step (n := 2) (t := 66) (b := 19136) rfl rfl ArealUCore.ArealUK.chunk_9567 s68
  have s66 : leavesOK ctxLitU 333175000000 2 ((leaves.drop 19132).take 68) 334875000000 2 = true :=
    take_step (n := 2) (t := 68) (b := 19134) rfl rfl ArealUCore.ArealUK.chunk_9566 s67
  have s65 : leavesOK ctxLitU 333125000000 2 ((leaves.drop 19130).take 70) 334875000000 2 = true :=
    take_step (n := 2) (t := 70) (b := 19132) rfl rfl ArealUCore.ArealUK.chunk_9565 s66
  have s64 : leavesOK ctxLitU 333075000000 2 ((leaves.drop 19128).take 72) 334875000000 2 = true :=
    take_step (n := 2) (t := 72) (b := 19130) rfl rfl ArealUCore.ArealUK.chunk_9564 s65
  have s63 : leavesOK ctxLitU 333025000000 2 ((leaves.drop 19126).take 74) 334875000000 2 = true :=
    take_step (n := 2) (t := 74) (b := 19128) rfl rfl ArealUCore.ArealUK.chunk_9563 s64
  have s62 : leavesOK ctxLitU 332975000000 2 ((leaves.drop 19124).take 76) 334875000000 2 = true :=
    take_step (n := 2) (t := 76) (b := 19126) rfl rfl ArealUCore.ArealUK.chunk_9562 s63
  have s61 : leavesOK ctxLitU 332925000000 2 ((leaves.drop 19122).take 78) 334875000000 2 = true :=
    take_step (n := 2) (t := 78) (b := 19124) rfl rfl ArealUCore.ArealUK.chunk_9561 s62
  have s60 : leavesOK ctxLitU 332875000000 2 ((leaves.drop 19120).take 80) 334875000000 2 = true :=
    take_step (n := 2) (t := 80) (b := 19122) rfl rfl ArealUCore.ArealUK.chunk_9560 s61
  have s59 : leavesOK ctxLitU 332825000000 2 ((leaves.drop 19118).take 82) 334875000000 2 = true :=
    take_step (n := 2) (t := 82) (b := 19120) rfl rfl ArealUCore.ArealUK.chunk_9559 s60
  have s58 : leavesOK ctxLitU 332775000000 2 ((leaves.drop 19116).take 84) 334875000000 2 = true :=
    take_step (n := 2) (t := 84) (b := 19118) rfl rfl ArealUCore.ArealUK.chunk_9558 s59
  have s57 : leavesOK ctxLitU 332725000000 2 ((leaves.drop 19114).take 86) 334875000000 2 = true :=
    take_step (n := 2) (t := 86) (b := 19116) rfl rfl ArealUCore.ArealUK.chunk_9557 s58
  have s56 : leavesOK ctxLitU 332675000000 2 ((leaves.drop 19112).take 88) 334875000000 2 = true :=
    take_step (n := 2) (t := 88) (b := 19114) rfl rfl ArealUCore.ArealUK.chunk_9556 s57
  have s55 : leavesOK ctxLitU 332625000000 2 ((leaves.drop 19110).take 90) 334875000000 2 = true :=
    take_step (n := 2) (t := 90) (b := 19112) rfl rfl ArealUCore.ArealUK.chunk_9555 s56
  have s54 : leavesOK ctxLitU 332575000000 2 ((leaves.drop 19108).take 92) 334875000000 2 = true :=
    take_step (n := 2) (t := 92) (b := 19110) rfl rfl ArealUCore.ArealUK.chunk_9554 s55
  have s53 : leavesOK ctxLitU 332525000000 2 ((leaves.drop 19106).take 94) 334875000000 2 = true :=
    take_step (n := 2) (t := 94) (b := 19108) rfl rfl ArealUCore.ArealUK.chunk_9553 s54
  have s52 : leavesOK ctxLitU 332475000000 2 ((leaves.drop 19104).take 96) 334875000000 2 = true :=
    take_step (n := 2) (t := 96) (b := 19106) rfl rfl ArealUCore.ArealUK.chunk_9552 s53
  have s51 : leavesOK ctxLitU 332425000000 2 ((leaves.drop 19102).take 98) 334875000000 2 = true :=
    take_step (n := 2) (t := 98) (b := 19104) rfl rfl ArealUCore.ArealUK.chunk_9551 s52
  have s50 : leavesOK ctxLitU 332375000000 2 ((leaves.drop 19100).take 100) 334875000000 2 = true :=
    take_step (n := 2) (t := 100) (b := 19102) rfl rfl ArealUCore.ArealUK.chunk_9550 s51
  have s49 : leavesOK ctxLitU 332325000000 2 ((leaves.drop 19098).take 102) 334875000000 2 = true :=
    take_step (n := 2) (t := 102) (b := 19100) rfl rfl ArealUCore.ArealUK.chunk_9549 s50
  have s48 : leavesOK ctxLitU 332275000000 2 ((leaves.drop 19096).take 104) 334875000000 2 = true :=
    take_step (n := 2) (t := 104) (b := 19098) rfl rfl ArealUCore.ArealUK.chunk_9548 s49
  have s47 : leavesOK ctxLitU 332225000000 2 ((leaves.drop 19094).take 106) 334875000000 2 = true :=
    take_step (n := 2) (t := 106) (b := 19096) rfl rfl ArealUCore.ArealUK.chunk_9547 s48
  have s46 : leavesOK ctxLitU 332175000000 2 ((leaves.drop 19092).take 108) 334875000000 2 = true :=
    take_step (n := 2) (t := 108) (b := 19094) rfl rfl ArealUCore.ArealUK.chunk_9546 s47
  have s45 : leavesOK ctxLitU 332125000000 2 ((leaves.drop 19090).take 110) 334875000000 2 = true :=
    take_step (n := 2) (t := 110) (b := 19092) rfl rfl ArealUCore.ArealUK.chunk_9545 s46
  have s44 : leavesOK ctxLitU 332075000000 2 ((leaves.drop 19088).take 112) 334875000000 2 = true :=
    take_step (n := 2) (t := 112) (b := 19090) rfl rfl ArealUCore.ArealUK.chunk_9544 s45
  have s43 : leavesOK ctxLitU 332025000000 2 ((leaves.drop 19086).take 114) 334875000000 2 = true :=
    take_step (n := 2) (t := 114) (b := 19088) rfl rfl ArealUCore.ArealUK.chunk_9543 s44
  have s42 : leavesOK ctxLitU 331975000000 2 ((leaves.drop 19084).take 116) 334875000000 2 = true :=
    take_step (n := 2) (t := 116) (b := 19086) rfl rfl ArealUCore.ArealUK.chunk_9542 s43
  have s41 : leavesOK ctxLitU 331925000000 2 ((leaves.drop 19082).take 118) 334875000000 2 = true :=
    take_step (n := 2) (t := 118) (b := 19084) rfl rfl ArealUCore.ArealUK.chunk_9541 s42
  have s40 : leavesOK ctxLitU 331875000000 2 ((leaves.drop 19080).take 120) 334875000000 2 = true :=
    take_step (n := 2) (t := 120) (b := 19082) rfl rfl ArealUCore.ArealUK.chunk_9540 s41
  have s39 : leavesOK ctxLitU 331825000000 2 ((leaves.drop 19078).take 122) 334875000000 2 = true :=
    take_step (n := 2) (t := 122) (b := 19080) rfl rfl ArealUCore.ArealUK.chunk_9539 s40
  have s38 : leavesOK ctxLitU 331775000000 2 ((leaves.drop 19076).take 124) 334875000000 2 = true :=
    take_step (n := 2) (t := 124) (b := 19078) rfl rfl ArealUCore.ArealUK.chunk_9538 s39
  have s37 : leavesOK ctxLitU 331725000000 2 ((leaves.drop 19074).take 126) 334875000000 2 = true :=
    take_step (n := 2) (t := 126) (b := 19076) rfl rfl ArealUCore.ArealUK.chunk_9537 s38
  have s36 : leavesOK ctxLitU 331675000000 2 ((leaves.drop 19072).take 128) 334875000000 2 = true :=
    take_step (n := 2) (t := 128) (b := 19074) rfl rfl ArealUCore.ArealUK.chunk_9536 s37
  have s35 : leavesOK ctxLitU 331625000000 2 ((leaves.drop 19070).take 130) 334875000000 2 = true :=
    take_step (n := 2) (t := 130) (b := 19072) rfl rfl ArealUCore.ArealUK.chunk_9535 s36
  have s34 : leavesOK ctxLitU 331575000000 2 ((leaves.drop 19068).take 132) 334875000000 2 = true :=
    take_step (n := 2) (t := 132) (b := 19070) rfl rfl ArealUCore.ArealUK.chunk_9534 s35
  have s33 : leavesOK ctxLitU 331525000000 2 ((leaves.drop 19066).take 134) 334875000000 2 = true :=
    take_step (n := 2) (t := 134) (b := 19068) rfl rfl ArealUCore.ArealUK.chunk_9533 s34
  have s32 : leavesOK ctxLitU 331475000000 2 ((leaves.drop 19064).take 136) 334875000000 2 = true :=
    take_step (n := 2) (t := 136) (b := 19066) rfl rfl ArealUCore.ArealUK.chunk_9532 s33
  have s31 : leavesOK ctxLitU 331425000000 2 ((leaves.drop 19062).take 138) 334875000000 2 = true :=
    take_step (n := 2) (t := 138) (b := 19064) rfl rfl ArealUCore.ArealUK.chunk_9531 s32
  have s30 : leavesOK ctxLitU 331375000000 2 ((leaves.drop 19060).take 140) 334875000000 2 = true :=
    take_step (n := 2) (t := 140) (b := 19062) rfl rfl ArealUCore.ArealUK.chunk_9530 s31
  have s29 : leavesOK ctxLitU 331325000000 2 ((leaves.drop 19058).take 142) 334875000000 2 = true :=
    take_step (n := 2) (t := 142) (b := 19060) rfl rfl ArealUCore.ArealUK.chunk_9529 s30
  have s28 : leavesOK ctxLitU 331275000000 2 ((leaves.drop 19056).take 144) 334875000000 2 = true :=
    take_step (n := 2) (t := 144) (b := 19058) rfl rfl ArealUCore.ArealUK.chunk_9528 s29
  have s27 : leavesOK ctxLitU 331225000000 2 ((leaves.drop 19054).take 146) 334875000000 2 = true :=
    take_step (n := 2) (t := 146) (b := 19056) rfl rfl ArealUCore.ArealUK.chunk_9527 s28
  have s26 : leavesOK ctxLitU 331175000000 2 ((leaves.drop 19052).take 148) 334875000000 2 = true :=
    take_step (n := 2) (t := 148) (b := 19054) rfl rfl ArealUCore.ArealUK.chunk_9526 s27
  have s25 : leavesOK ctxLitU 331125000000 2 ((leaves.drop 19050).take 150) 334875000000 2 = true :=
    take_step (n := 2) (t := 150) (b := 19052) rfl rfl ArealUCore.ArealUK.chunk_9525 s26
  have s24 : leavesOK ctxLitU 331075000000 2 ((leaves.drop 19048).take 152) 334875000000 2 = true :=
    take_step (n := 2) (t := 152) (b := 19050) rfl rfl ArealUCore.ArealUK.chunk_9524 s25
  have s23 : leavesOK ctxLitU 331025000000 2 ((leaves.drop 19046).take 154) 334875000000 2 = true :=
    take_step (n := 2) (t := 154) (b := 19048) rfl rfl ArealUCore.ArealUK.chunk_9523 s24
  have s22 : leavesOK ctxLitU 330975000000 2 ((leaves.drop 19044).take 156) 334875000000 2 = true :=
    take_step (n := 2) (t := 156) (b := 19046) rfl rfl ArealUCore.ArealUK.chunk_9522 s23
  have s21 : leavesOK ctxLitU 330925000000 2 ((leaves.drop 19042).take 158) 334875000000 2 = true :=
    take_step (n := 2) (t := 158) (b := 19044) rfl rfl ArealUCore.ArealUK.chunk_9521 s22
  have s20 : leavesOK ctxLitU 330875000000 2 ((leaves.drop 19040).take 160) 334875000000 2 = true :=
    take_step (n := 2) (t := 160) (b := 19042) rfl rfl ArealUCore.ArealUK.chunk_9520 s21
  have s19 : leavesOK ctxLitU 330825000000 2 ((leaves.drop 19038).take 162) 334875000000 2 = true :=
    take_step (n := 2) (t := 162) (b := 19040) rfl rfl ArealUCore.ArealUK.chunk_9519 s20
  have s18 : leavesOK ctxLitU 330775000000 2 ((leaves.drop 19036).take 164) 334875000000 2 = true :=
    take_step (n := 2) (t := 164) (b := 19038) rfl rfl ArealUCore.ArealUK.chunk_9518 s19
  have s17 : leavesOK ctxLitU 330725000000 2 ((leaves.drop 19034).take 166) 334875000000 2 = true :=
    take_step (n := 2) (t := 166) (b := 19036) rfl rfl ArealUCore.ArealUK.chunk_9517 s18
  have s16 : leavesOK ctxLitU 330675000000 2 ((leaves.drop 19032).take 168) 334875000000 2 = true :=
    take_step (n := 2) (t := 168) (b := 19034) rfl rfl ArealUCore.ArealUK.chunk_9516 s17
  have s15 : leavesOK ctxLitU 330625000000 2 ((leaves.drop 19030).take 170) 334875000000 2 = true :=
    take_step (n := 2) (t := 170) (b := 19032) rfl rfl ArealUCore.ArealUK.chunk_9515 s16
  have s14 : leavesOK ctxLitU 330575000000 2 ((leaves.drop 19028).take 172) 334875000000 2 = true :=
    take_step (n := 2) (t := 172) (b := 19030) rfl rfl ArealUCore.ArealUK.chunk_9514 s15
  have s13 : leavesOK ctxLitU 330525000000 2 ((leaves.drop 19026).take 174) 334875000000 2 = true :=
    take_step (n := 2) (t := 174) (b := 19028) rfl rfl ArealUCore.ArealUK.chunk_9513 s14
  have s12 : leavesOK ctxLitU 330475000000 2 ((leaves.drop 19024).take 176) 334875000000 2 = true :=
    take_step (n := 2) (t := 176) (b := 19026) rfl rfl ArealUCore.ArealUK.chunk_9512 s13
  have s11 : leavesOK ctxLitU 330425000000 2 ((leaves.drop 19022).take 178) 334875000000 2 = true :=
    take_step (n := 2) (t := 178) (b := 19024) rfl rfl ArealUCore.ArealUK.chunk_9511 s12
  have s10 : leavesOK ctxLitU 330375000000 2 ((leaves.drop 19020).take 180) 334875000000 2 = true :=
    take_step (n := 2) (t := 180) (b := 19022) rfl rfl ArealUCore.ArealUK.chunk_9510 s11
  have s9 : leavesOK ctxLitU 330325000000 2 ((leaves.drop 19018).take 182) 334875000000 2 = true :=
    take_step (n := 2) (t := 182) (b := 19020) rfl rfl ArealUCore.ArealUK.chunk_9509 s10
  have s8 : leavesOK ctxLitU 330275000000 2 ((leaves.drop 19016).take 184) 334875000000 2 = true :=
    take_step (n := 2) (t := 184) (b := 19018) rfl rfl ArealUCore.ArealUK.chunk_9508 s9
  have s7 : leavesOK ctxLitU 330225000000 2 ((leaves.drop 19014).take 186) 334875000000 2 = true :=
    take_step (n := 2) (t := 186) (b := 19016) rfl rfl ArealUCore.ArealUK.chunk_9507 s8
  have s6 : leavesOK ctxLitU 330175000000 2 ((leaves.drop 19012).take 188) 334875000000 2 = true :=
    take_step (n := 2) (t := 188) (b := 19014) rfl rfl ArealUCore.ArealUK.chunk_9506 s7
  have s5 : leavesOK ctxLitU 330125000000 2 ((leaves.drop 19010).take 190) 334875000000 2 = true :=
    take_step (n := 2) (t := 190) (b := 19012) rfl rfl ArealUCore.ArealUK.chunk_9505 s6
  have s4 : leavesOK ctxLitU 330075000000 2 ((leaves.drop 19008).take 192) 334875000000 2 = true :=
    take_step (n := 2) (t := 192) (b := 19010) rfl rfl ArealUCore.ArealUK.chunk_9504 s5
  have s3 : leavesOK ctxLitU 330025000000 2 ((leaves.drop 19006).take 194) 334875000000 2 = true :=
    take_step (n := 2) (t := 194) (b := 19008) rfl rfl ArealUCore.ArealUK.chunk_9503 s4
  have s2 : leavesOK ctxLitU 329975000000 2 ((leaves.drop 19004).take 196) 334875000000 2 = true :=
    take_step (n := 2) (t := 196) (b := 19006) rfl rfl ArealUCore.ArealUK.chunk_9502 s3
  have s1 : leavesOK ctxLitU 329925000000 2 ((leaves.drop 19002).take 198) 334875000000 2 = true :=
    take_step (n := 2) (t := 198) (b := 19004) rfl rfl ArealUCore.ArealUK.chunk_9501 s2
  have s0 : leavesOK ctxLitU 329875000000 2 ((leaves.drop 19000).take 200) 334875000000 2 = true :=
    take_step (n := 2) (t := 200) (b := 19002) rfl rfl ArealUCore.ArealUK.chunk_9500 s1
  exact s0

end Areal.UCert

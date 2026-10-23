import ArealUK.Chunk13500
import ArealUK.Chunk13501
import ArealUK.Chunk13502
import ArealUK.Chunk13503
import ArealUK.Chunk13504
import ArealUK.Chunk13505
import ArealUK.Chunk13506
import ArealUK.Chunk13507
import ArealUK.Chunk13508
import ArealUK.Chunk13509
import ArealUK.Chunk13510
import ArealUK.Chunk13511
import ArealUK.Chunk13512
import ArealUK.Chunk13513
import ArealUK.Chunk13514
import ArealUK.Chunk13515
import ArealUK.Chunk13516
import ArealUK.Chunk13517
import ArealUK.Chunk13518
import ArealUK.Chunk13519
import ArealUK.Chunk13520
import ArealUK.Chunk13521
import ArealUK.Chunk13522
import ArealUK.Chunk13523
import ArealUK.Chunk13524
import ArealUK.Chunk13525
import ArealUK.Chunk13526
import ArealUK.Chunk13527
import ArealUK.Chunk13528
import ArealUK.Chunk13529
import ArealUK.Chunk13530
import ArealUK.Chunk13531
import ArealUK.Chunk13532
import ArealUK.Chunk13533
import ArealUK.Chunk13534
import ArealUK.Chunk13535
import ArealUK.Chunk13536
import ArealUK.Chunk13537
import ArealUK.Chunk13538
import ArealUK.Chunk13539
import ArealUK.Chunk13540
import ArealUK.Chunk13541
import ArealUK.Chunk13542
import ArealUK.Chunk13543
import ArealUK.Chunk13544
import ArealUK.Chunk13545
import ArealUK.Chunk13546
import ArealUK.Chunk13547
import ArealUK.Chunk13548
import ArealUK.Chunk13549
import ArealUK.Chunk13550
import ArealUK.Chunk13551
import ArealUK.Chunk13552
import ArealUK.Chunk13553
import ArealUK.Chunk13554
import ArealUK.Chunk13555
import ArealUK.Chunk13556
import ArealUK.Chunk13557
import ArealUK.Chunk13558
import ArealUK.Chunk13559
import ArealUK.Chunk13560
import ArealUK.Chunk13561
import ArealUK.Chunk13562
import ArealUK.Chunk13563
import ArealUK.Chunk13564
import ArealUK.Chunk13565
import ArealUK.Chunk13566
import ArealUK.Chunk13567
import ArealUK.Chunk13568
import ArealUK.Chunk13569
import ArealUK.Chunk13570
import ArealUK.Chunk13571
import ArealUK.Chunk13572
import ArealUK.Chunk13573
import ArealUK.Chunk13574
import ArealUK.Chunk13575
import ArealUK.Chunk13576
import ArealUK.Chunk13577
import ArealUK.Chunk13578
import ArealUK.Chunk13579
import ArealUK.Chunk13580
import ArealUK.Chunk13581
import ArealUK.Chunk13582
import ArealUK.Chunk13583
import ArealUK.Chunk13584
import ArealUK.Chunk13585
import ArealUK.Chunk13586
import ArealUK.Chunk13587
import ArealUK.Chunk13588
import ArealUK.Chunk13589
import ArealUK.Chunk13590
import ArealUK.Chunk13591
import ArealUK.Chunk13592
import ArealUK.Chunk13593
import ArealUK.Chunk13594
import ArealUK.Chunk13595
import ArealUK.Chunk13596
import ArealUK.Chunk13597
import ArealUK.Chunk13598
import ArealUK.Chunk13599
import Areal.UCert.LeavesKGen

/-! Group 135 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_135 : leavesOK ctxLitU 137943750000 0 ((leaves.drop 27000).take 200) 278262500000 1 = true := by
  have s99 := ArealUCore.ArealUK.chunk_13599
  have s98 : leavesOK ctxLitU 556425000000 2 ((leaves.drop 27196).take 4) 278262500000 1 = true :=
    take_step (n := 2) (t := 4) (b := 27198) rfl rfl ArealUCore.ArealUK.chunk_13598 s99
  have s97 : leavesOK ctxLitU 278187500000 1 ((leaves.drop 27194).take 6) 278262500000 1 = true :=
    take_step (n := 2) (t := 6) (b := 27196) rfl rfl ArealUCore.ArealUK.chunk_13597 s98
  have s96 : leavesOK ctxLitU 278162500000 1 ((leaves.drop 27192).take 8) 278262500000 1 = true :=
    take_step (n := 2) (t := 8) (b := 27194) rfl rfl ArealUCore.ArealUK.chunk_13596 s97
  have s95 : leavesOK ctxLitU 139068750000 0 ((leaves.drop 27190).take 10) 278262500000 1 = true :=
    take_step (n := 2) (t := 10) (b := 27192) rfl rfl ArealUCore.ArealUK.chunk_13595 s96
  have s94 : leavesOK ctxLitU 139056250000 0 ((leaves.drop 27188).take 12) 278262500000 1 = true :=
    take_step (n := 2) (t := 12) (b := 27190) rfl rfl ArealUCore.ArealUK.chunk_13594 s95
  have s93 : leavesOK ctxLitU 139043750000 0 ((leaves.drop 27186).take 14) 278262500000 1 = true :=
    take_step (n := 2) (t := 14) (b := 27188) rfl rfl ArealUCore.ArealUK.chunk_13593 s94
  have s92 : leavesOK ctxLitU 278068750000 1 ((leaves.drop 27184).take 16) 278262500000 1 = true :=
    take_step (n := 2) (t := 16) (b := 27186) rfl rfl ArealUCore.ArealUK.chunk_13592 s93
  have s91 : leavesOK ctxLitU 278056250000 1 ((leaves.drop 27182).take 18) 278262500000 1 = true :=
    take_step (n := 2) (t := 18) (b := 27184) rfl rfl ArealUCore.ArealUK.chunk_13591 s92
  have s90 : leavesOK ctxLitU 278037500000 1 ((leaves.drop 27180).take 20) 278262500000 1 = true :=
    take_step (n := 2) (t := 20) (b := 27182) rfl rfl ArealUCore.ArealUK.chunk_13590 s91
  have s89 : leavesOK ctxLitU 278012500000 1 ((leaves.drop 27178).take 22) 278262500000 1 = true :=
    take_step (n := 2) (t := 22) (b := 27180) rfl rfl ArealUCore.ArealUK.chunk_13589 s90
  have s88 : leavesOK ctxLitU 555975000000 2 ((leaves.drop 27176).take 24) 278262500000 1 = true :=
    take_step (n := 2) (t := 24) (b := 27178) rfl rfl ArealUCore.ArealUK.chunk_13588 s89
  have s87 : leavesOK ctxLitU 555925000000 2 ((leaves.drop 27174).take 26) 278262500000 1 = true :=
    take_step (n := 2) (t := 26) (b := 27176) rfl rfl ArealUCore.ArealUK.chunk_13587 s88
  have s86 : leavesOK ctxLitU 555875000000 2 ((leaves.drop 27172).take 28) 278262500000 1 = true :=
    take_step (n := 2) (t := 28) (b := 27174) rfl rfl ArealUCore.ArealUK.chunk_13586 s87
  have s85 : leavesOK ctxLitU 555825000000 2 ((leaves.drop 27170).take 30) 278262500000 1 = true :=
    take_step (n := 2) (t := 30) (b := 27172) rfl rfl ArealUCore.ArealUK.chunk_13585 s86
  have s84 : leavesOK ctxLitU 555775000000 2 ((leaves.drop 27168).take 32) 278262500000 1 = true :=
    take_step (n := 2) (t := 32) (b := 27170) rfl rfl ArealUCore.ArealUK.chunk_13584 s85
  have s83 : leavesOK ctxLitU 555725000000 2 ((leaves.drop 27166).take 34) 278262500000 1 = true :=
    take_step (n := 2) (t := 34) (b := 27168) rfl rfl ArealUCore.ArealUK.chunk_13583 s84
  have s82 : leavesOK ctxLitU 555675000000 2 ((leaves.drop 27164).take 36) 278262500000 1 = true :=
    take_step (n := 2) (t := 36) (b := 27166) rfl rfl ArealUCore.ArealUK.chunk_13582 s83
  have s81 : leavesOK ctxLitU 555625000000 2 ((leaves.drop 27162).take 38) 278262500000 1 = true :=
    take_step (n := 2) (t := 38) (b := 27164) rfl rfl ArealUCore.ArealUK.chunk_13581 s82
  have s80 : leavesOK ctxLitU 277787500000 1 ((leaves.drop 27160).take 40) 278262500000 1 = true :=
    take_step (n := 2) (t := 40) (b := 27162) rfl rfl ArealUCore.ArealUK.chunk_13580 s81
  have s79 : leavesOK ctxLitU 555550000000 2 ((leaves.drop 27158).take 42) 278262500000 1 = true :=
    take_step (n := 2) (t := 42) (b := 27160) rfl rfl ArealUCore.ArealUK.chunk_13579 s80
  have s78 : leavesOK ctxLitU 555525000000 2 ((leaves.drop 27156).take 44) 278262500000 1 = true :=
    take_step (n := 2) (t := 44) (b := 27158) rfl rfl ArealUCore.ArealUK.chunk_13578 s79
  have s77 : leavesOK ctxLitU 277743750000 1 ((leaves.drop 27154).take 46) 278262500000 1 = true :=
    take_step (n := 2) (t := 46) (b := 27156) rfl rfl ArealUCore.ArealUK.chunk_13577 s78
  have s76 : leavesOK ctxLitU 277731250000 1 ((leaves.drop 27152).take 48) 278262500000 1 = true :=
    take_step (n := 2) (t := 48) (b := 27154) rfl rfl ArealUCore.ArealUK.chunk_13576 s77
  have s75 : leavesOK ctxLitU 138856250000 0 ((leaves.drop 27150).take 50) 278262500000 1 = true :=
    take_step (n := 2) (t := 50) (b := 27152) rfl rfl ArealUCore.ArealUK.chunk_13575 s76
  have s74 : leavesOK ctxLitU 138843750000 0 ((leaves.drop 27148).take 52) 278262500000 1 = true :=
    take_step (n := 2) (t := 52) (b := 27150) rfl rfl ArealUCore.ArealUK.chunk_13574 s75
  have s73 : leavesOK ctxLitU 138831250000 0 ((leaves.drop 27146).take 54) 278262500000 1 = true :=
    take_step (n := 2) (t := 54) (b := 27148) rfl rfl ArealUCore.ArealUK.chunk_13573 s74
  have s72 : leavesOK ctxLitU 277637500000 1 ((leaves.drop 27144).take 56) 278262500000 1 = true :=
    take_step (n := 2) (t := 56) (b := 27146) rfl rfl ArealUCore.ArealUK.chunk_13572 s73
  have s71 : leavesOK ctxLitU 277612500000 1 ((leaves.drop 27142).take 58) 278262500000 1 = true :=
    take_step (n := 2) (t := 58) (b := 27144) rfl rfl ArealUCore.ArealUK.chunk_13571 s72
  have s70 : leavesOK ctxLitU 277587500000 1 ((leaves.drop 27140).take 60) 278262500000 1 = true :=
    take_step (n := 2) (t := 60) (b := 27142) rfl rfl ArealUCore.ArealUK.chunk_13570 s71
  have s69 : leavesOK ctxLitU 277562500000 1 ((leaves.drop 27138).take 62) 278262500000 1 = true :=
    take_step (n := 2) (t := 62) (b := 27140) rfl rfl ArealUCore.ArealUK.chunk_13569 s70
  have s68 : leavesOK ctxLitU 138768750000 0 ((leaves.drop 27136).take 64) 278262500000 1 = true :=
    take_step (n := 2) (t := 64) (b := 27138) rfl rfl ArealUCore.ArealUK.chunk_13568 s69
  have s67 : leavesOK ctxLitU 138756250000 0 ((leaves.drop 27134).take 66) 278262500000 1 = true :=
    take_step (n := 2) (t := 66) (b := 27136) rfl rfl ArealUCore.ArealUK.chunk_13567 s68
  have s66 : leavesOK ctxLitU 138743750000 0 ((leaves.drop 27132).take 68) 278262500000 1 = true :=
    take_step (n := 2) (t := 68) (b := 27134) rfl rfl ArealUCore.ArealUK.chunk_13566 s67
  have s65 : leavesOK ctxLitU 277468750000 1 ((leaves.drop 27130).take 70) 278262500000 1 = true :=
    take_step (n := 2) (t := 70) (b := 27132) rfl rfl ArealUCore.ArealUK.chunk_13565 s66
  have s64 : leavesOK ctxLitU 277456250000 1 ((leaves.drop 27128).take 72) 278262500000 1 = true :=
    take_step (n := 2) (t := 72) (b := 27130) rfl rfl ArealUCore.ArealUK.chunk_13564 s65
  have s63 : leavesOK ctxLitU 277437500000 1 ((leaves.drop 27126).take 74) 278262500000 1 = true :=
    take_step (n := 2) (t := 74) (b := 27128) rfl rfl ArealUCore.ArealUK.chunk_13563 s64
  have s62 : leavesOK ctxLitU 277412500000 1 ((leaves.drop 27124).take 76) 278262500000 1 = true :=
    take_step (n := 2) (t := 76) (b := 27126) rfl rfl ArealUCore.ArealUK.chunk_13562 s63
  have s61 : leavesOK ctxLitU 554775000000 2 ((leaves.drop 27122).take 78) 278262500000 1 = true :=
    take_step (n := 2) (t := 78) (b := 27124) rfl rfl ArealUCore.ArealUK.chunk_13561 s62
  have s60 : leavesOK ctxLitU 554725000000 2 ((leaves.drop 27120).take 80) 278262500000 1 = true :=
    take_step (n := 2) (t := 80) (b := 27122) rfl rfl ArealUCore.ArealUK.chunk_13560 s61
  have s59 : leavesOK ctxLitU 554675000000 2 ((leaves.drop 27118).take 82) 278262500000 1 = true :=
    take_step (n := 2) (t := 82) (b := 27120) rfl rfl ArealUCore.ArealUK.chunk_13559 s60
  have s58 : leavesOK ctxLitU 554625000000 2 ((leaves.drop 27116).take 84) 278262500000 1 = true :=
    take_step (n := 2) (t := 84) (b := 27118) rfl rfl ArealUCore.ArealUK.chunk_13558 s59
  have s57 : leavesOK ctxLitU 554575000000 2 ((leaves.drop 27114).take 86) 278262500000 1 = true :=
    take_step (n := 2) (t := 86) (b := 27116) rfl rfl ArealUCore.ArealUK.chunk_13557 s58
  have s56 : leavesOK ctxLitU 554525000000 2 ((leaves.drop 27112).take 88) 278262500000 1 = true :=
    take_step (n := 2) (t := 88) (b := 27114) rfl rfl ArealUCore.ArealUK.chunk_13556 s57
  have s55 : leavesOK ctxLitU 554475000000 2 ((leaves.drop 27110).take 90) 278262500000 1 = true :=
    take_step (n := 2) (t := 90) (b := 27112) rfl rfl ArealUCore.ArealUK.chunk_13555 s56
  have s54 : leavesOK ctxLitU 554425000000 2 ((leaves.drop 27108).take 92) 278262500000 1 = true :=
    take_step (n := 2) (t := 92) (b := 27110) rfl rfl ArealUCore.ArealUK.chunk_13554 s55
  have s53 : leavesOK ctxLitU 277187500000 1 ((leaves.drop 27106).take 94) 278262500000 1 = true :=
    take_step (n := 2) (t := 94) (b := 27108) rfl rfl ArealUCore.ArealUK.chunk_13553 s54
  have s52 : leavesOK ctxLitU 277162500000 1 ((leaves.drop 27104).take 96) 278262500000 1 = true :=
    take_step (n := 2) (t := 96) (b := 27106) rfl rfl ArealUCore.ArealUK.chunk_13552 s53
  have s51 : leavesOK ctxLitU 138568750000 0 ((leaves.drop 27102).take 98) 278262500000 1 = true :=
    take_step (n := 2) (t := 98) (b := 27104) rfl rfl ArealUCore.ArealUK.chunk_13551 s52
  have s50 : leavesOK ctxLitU 138556250000 0 ((leaves.drop 27100).take 100) 278262500000 1 = true :=
    take_step (n := 2) (t := 100) (b := 27102) rfl rfl ArealUCore.ArealUK.chunk_13550 s51
  have s49 : leavesOK ctxLitU 277087500000 1 ((leaves.drop 27098).take 102) 278262500000 1 = true :=
    take_step (n := 2) (t := 102) (b := 27100) rfl rfl ArealUCore.ArealUK.chunk_13549 s50
  have s48 : leavesOK ctxLitU 277062500000 1 ((leaves.drop 27096).take 104) 278262500000 1 = true :=
    take_step (n := 2) (t := 104) (b := 27098) rfl rfl ArealUCore.ArealUK.chunk_13548 s49
  have s47 : leavesOK ctxLitU 554075000000 2 ((leaves.drop 27094).take 106) 278262500000 1 = true :=
    take_step (n := 2) (t := 106) (b := 27096) rfl rfl ArealUCore.ArealUK.chunk_13547 s48
  have s46 : leavesOK ctxLitU 554025000000 2 ((leaves.drop 27092).take 108) 278262500000 1 = true :=
    take_step (n := 2) (t := 108) (b := 27094) rfl rfl ArealUCore.ArealUK.chunk_13546 s47
  have s45 : leavesOK ctxLitU 553975000000 2 ((leaves.drop 27090).take 110) 278262500000 1 = true :=
    take_step (n := 2) (t := 110) (b := 27092) rfl rfl ArealUCore.ArealUK.chunk_13545 s46
  have s44 : leavesOK ctxLitU 553925000000 2 ((leaves.drop 27088).take 112) 278262500000 1 = true :=
    take_step (n := 2) (t := 112) (b := 27090) rfl rfl ArealUCore.ArealUK.chunk_13544 s45
  have s43 : leavesOK ctxLitU 553875000000 2 ((leaves.drop 27086).take 114) 278262500000 1 = true :=
    take_step (n := 2) (t := 114) (b := 27088) rfl rfl ArealUCore.ArealUK.chunk_13543 s44
  have s42 : leavesOK ctxLitU 553825000000 2 ((leaves.drop 27084).take 116) 278262500000 1 = true :=
    take_step (n := 2) (t := 116) (b := 27086) rfl rfl ArealUCore.ArealUK.chunk_13542 s43
  have s41 : leavesOK ctxLitU 553775000000 2 ((leaves.drop 27082).take 118) 278262500000 1 = true :=
    take_step (n := 2) (t := 118) (b := 27084) rfl rfl ArealUCore.ArealUK.chunk_13541 s42
  have s40 : leavesOK ctxLitU 553725000000 2 ((leaves.drop 27080).take 120) 278262500000 1 = true :=
    take_step (n := 2) (t := 120) (b := 27082) rfl rfl ArealUCore.ArealUK.chunk_13540 s41
  have s39 : leavesOK ctxLitU 553675000000 2 ((leaves.drop 27078).take 122) 278262500000 1 = true :=
    take_step (n := 2) (t := 122) (b := 27080) rfl rfl ArealUCore.ArealUK.chunk_13539 s40
  have s38 : leavesOK ctxLitU 553625000000 2 ((leaves.drop 27076).take 124) 278262500000 1 = true :=
    take_step (n := 2) (t := 124) (b := 27078) rfl rfl ArealUCore.ArealUK.chunk_13538 s39
  have s37 : leavesOK ctxLitU 553575000000 2 ((leaves.drop 27074).take 126) 278262500000 1 = true :=
    take_step (n := 2) (t := 126) (b := 27076) rfl rfl ArealUCore.ArealUK.chunk_13537 s38
  have s36 : leavesOK ctxLitU 553525000000 2 ((leaves.drop 27072).take 128) 278262500000 1 = true :=
    take_step (n := 2) (t := 128) (b := 27074) rfl rfl ArealUCore.ArealUK.chunk_13536 s37
  have s35 : leavesOK ctxLitU 553475000000 2 ((leaves.drop 27070).take 130) 278262500000 1 = true :=
    take_step (n := 2) (t := 130) (b := 27072) rfl rfl ArealUCore.ArealUK.chunk_13535 s36
  have s34 : leavesOK ctxLitU 553425000000 2 ((leaves.drop 27068).take 132) 278262500000 1 = true :=
    take_step (n := 2) (t := 132) (b := 27070) rfl rfl ArealUCore.ArealUK.chunk_13534 s35
  have s33 : leavesOK ctxLitU 553375000000 2 ((leaves.drop 27066).take 134) 278262500000 1 = true :=
    take_step (n := 2) (t := 134) (b := 27068) rfl rfl ArealUCore.ArealUK.chunk_13533 s34
  have s32 : leavesOK ctxLitU 553325000000 2 ((leaves.drop 27064).take 136) 278262500000 1 = true :=
    take_step (n := 2) (t := 136) (b := 27066) rfl rfl ArealUCore.ArealUK.chunk_13532 s33
  have s31 : leavesOK ctxLitU 553275000000 2 ((leaves.drop 27062).take 138) 278262500000 1 = true :=
    take_step (n := 2) (t := 138) (b := 27064) rfl rfl ArealUCore.ArealUK.chunk_13531 s32
  have s30 : leavesOK ctxLitU 553225000000 2 ((leaves.drop 27060).take 140) 278262500000 1 = true :=
    take_step (n := 2) (t := 140) (b := 27062) rfl rfl ArealUCore.ArealUK.chunk_13530 s31
  have s29 : leavesOK ctxLitU 276587500000 1 ((leaves.drop 27058).take 142) 278262500000 1 = true :=
    take_step (n := 2) (t := 142) (b := 27060) rfl rfl ArealUCore.ArealUK.chunk_13529 s30
  have s28 : leavesOK ctxLitU 276562500000 1 ((leaves.drop 27056).take 144) 278262500000 1 = true :=
    take_step (n := 2) (t := 144) (b := 27058) rfl rfl ArealUCore.ArealUK.chunk_13528 s29
  have s27 : leavesOK ctxLitU 138268750000 0 ((leaves.drop 27054).take 146) 278262500000 1 = true :=
    take_step (n := 2) (t := 146) (b := 27056) rfl rfl ArealUCore.ArealUK.chunk_13527 s28
  have s26 : leavesOK ctxLitU 138256250000 0 ((leaves.drop 27052).take 148) 278262500000 1 = true :=
    take_step (n := 2) (t := 148) (b := 27054) rfl rfl ArealUCore.ArealUK.chunk_13526 s27
  have s25 : leavesOK ctxLitU 138243750000 0 ((leaves.drop 27050).take 150) 278262500000 1 = true :=
    take_step (n := 2) (t := 150) (b := 27052) rfl rfl ArealUCore.ArealUK.chunk_13525 s26
  have s24 : leavesOK ctxLitU 276468750000 1 ((leaves.drop 27048).take 152) 278262500000 1 = true :=
    take_step (n := 2) (t := 152) (b := 27050) rfl rfl ArealUCore.ArealUK.chunk_13524 s25
  have s23 : leavesOK ctxLitU 276456250000 1 ((leaves.drop 27046).take 154) 278262500000 1 = true :=
    take_step (n := 2) (t := 154) (b := 27048) rfl rfl ArealUCore.ArealUK.chunk_13523 s24
  have s22 : leavesOK ctxLitU 276437500000 1 ((leaves.drop 27044).take 156) 278262500000 1 = true :=
    take_step (n := 2) (t := 156) (b := 27046) rfl rfl ArealUCore.ArealUK.chunk_13522 s23
  have s21 : leavesOK ctxLitU 276412500000 1 ((leaves.drop 27042).take 158) 278262500000 1 = true :=
    take_step (n := 2) (t := 158) (b := 27044) rfl rfl ArealUCore.ArealUK.chunk_13521 s22
  have s20 : leavesOK ctxLitU 276387500000 1 ((leaves.drop 27040).take 160) 278262500000 1 = true :=
    take_step (n := 2) (t := 160) (b := 27042) rfl rfl ArealUCore.ArealUK.chunk_13520 s21
  have s19 : leavesOK ctxLitU 276362500000 1 ((leaves.drop 27038).take 162) 278262500000 1 = true :=
    take_step (n := 2) (t := 162) (b := 27040) rfl rfl ArealUCore.ArealUK.chunk_13519 s20
  have s18 : leavesOK ctxLitU 138168750000 0 ((leaves.drop 27036).take 164) 278262500000 1 = true :=
    take_step (n := 2) (t := 164) (b := 27038) rfl rfl ArealUCore.ArealUK.chunk_13518 s19
  have s17 : leavesOK ctxLitU 138156250000 0 ((leaves.drop 27034).take 166) 278262500000 1 = true :=
    take_step (n := 2) (t := 166) (b := 27036) rfl rfl ArealUCore.ArealUK.chunk_13517 s18
  have s16 : leavesOK ctxLitU 138143750000 0 ((leaves.drop 27032).take 168) 278262500000 1 = true :=
    take_step (n := 2) (t := 168) (b := 27034) rfl rfl ArealUCore.ArealUK.chunk_13516 s17
  have s15 : leavesOK ctxLitU 138131250000 0 ((leaves.drop 27030).take 170) 278262500000 1 = true :=
    take_step (n := 2) (t := 170) (b := 27032) rfl rfl ArealUCore.ArealUK.chunk_13515 s16
  have s14 : leavesOK ctxLitU 276237500000 1 ((leaves.drop 27028).take 172) 278262500000 1 = true :=
    take_step (n := 2) (t := 172) (b := 27030) rfl rfl ArealUCore.ArealUK.chunk_13514 s15
  have s13 : leavesOK ctxLitU 276212500000 1 ((leaves.drop 27026).take 174) 278262500000 1 = true :=
    take_step (n := 2) (t := 174) (b := 27028) rfl rfl ArealUCore.ArealUK.chunk_13513 s14
  have s12 : leavesOK ctxLitU 552375000000 2 ((leaves.drop 27024).take 176) 278262500000 1 = true :=
    take_step (n := 2) (t := 176) (b := 27026) rfl rfl ArealUCore.ArealUK.chunk_13512 s13
  have s11 : leavesOK ctxLitU 552325000000 2 ((leaves.drop 27022).take 178) 278262500000 1 = true :=
    take_step (n := 2) (t := 178) (b := 27024) rfl rfl ArealUCore.ArealUK.chunk_13511 s12
  have s10 : leavesOK ctxLitU 552275000000 2 ((leaves.drop 27020).take 180) 278262500000 1 = true :=
    take_step (n := 2) (t := 180) (b := 27022) rfl rfl ArealUCore.ArealUK.chunk_13510 s11
  have s9 : leavesOK ctxLitU 552225000000 2 ((leaves.drop 27018).take 182) 278262500000 1 = true :=
    take_step (n := 2) (t := 182) (b := 27020) rfl rfl ArealUCore.ArealUK.chunk_13509 s10
  have s8 : leavesOK ctxLitU 552175000000 2 ((leaves.drop 27016).take 184) 278262500000 1 = true :=
    take_step (n := 2) (t := 184) (b := 27018) rfl rfl ArealUCore.ArealUK.chunk_13508 s9
  have s7 : leavesOK ctxLitU 552125000000 2 ((leaves.drop 27014).take 186) 278262500000 1 = true :=
    take_step (n := 2) (t := 186) (b := 27016) rfl rfl ArealUCore.ArealUK.chunk_13507 s8
  have s6 : leavesOK ctxLitU 552075000000 2 ((leaves.drop 27012).take 188) 278262500000 1 = true :=
    take_step (n := 2) (t := 188) (b := 27014) rfl rfl ArealUCore.ArealUK.chunk_13506 s7
  have s5 : leavesOK ctxLitU 552025000000 2 ((leaves.drop 27010).take 190) 278262500000 1 = true :=
    take_step (n := 2) (t := 190) (b := 27012) rfl rfl ArealUCore.ArealUK.chunk_13505 s6
  have s4 : leavesOK ctxLitU 275987500000 1 ((leaves.drop 27008).take 192) 278262500000 1 = true :=
    take_step (n := 2) (t := 192) (b := 27010) rfl rfl ArealUCore.ArealUK.chunk_13504 s5
  have s3 : leavesOK ctxLitU 275962500000 1 ((leaves.drop 27006).take 194) 278262500000 1 = true :=
    take_step (n := 2) (t := 194) (b := 27008) rfl rfl ArealUCore.ArealUK.chunk_13503 s4
  have s2 : leavesOK ctxLitU 137968750000 0 ((leaves.drop 27004).take 196) 278262500000 1 = true :=
    take_step (n := 2) (t := 196) (b := 27006) rfl rfl ArealUCore.ArealUK.chunk_13502 s3
  have s1 : leavesOK ctxLitU 137956250000 0 ((leaves.drop 27002).take 198) 278262500000 1 = true :=
    take_step (n := 2) (t := 198) (b := 27004) rfl rfl ArealUCore.ArealUK.chunk_13501 s2
  have s0 : leavesOK ctxLitU 137943750000 0 ((leaves.drop 27000).take 200) 278262500000 1 = true :=
    take_step (n := 2) (t := 200) (b := 27002) rfl rfl ArealUCore.ArealUK.chunk_13500 s1
  exact s0

end Areal.UCert

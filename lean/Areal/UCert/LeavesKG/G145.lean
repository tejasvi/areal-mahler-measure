import ArealUK.Chunk14500
import ArealUK.Chunk14501
import ArealUK.Chunk14502
import ArealUK.Chunk14503
import ArealUK.Chunk14504
import ArealUK.Chunk14505
import ArealUK.Chunk14506
import ArealUK.Chunk14507
import ArealUK.Chunk14508
import ArealUK.Chunk14509
import ArealUK.Chunk14510
import ArealUK.Chunk14511
import ArealUK.Chunk14512
import ArealUK.Chunk14513
import ArealUK.Chunk14514
import ArealUK.Chunk14515
import ArealUK.Chunk14516
import ArealUK.Chunk14517
import ArealUK.Chunk14518
import ArealUK.Chunk14519
import ArealUK.Chunk14520
import ArealUK.Chunk14521
import ArealUK.Chunk14522
import ArealUK.Chunk14523
import ArealUK.Chunk14524
import ArealUK.Chunk14525
import ArealUK.Chunk14526
import ArealUK.Chunk14527
import ArealUK.Chunk14528
import ArealUK.Chunk14529
import ArealUK.Chunk14530
import ArealUK.Chunk14531
import ArealUK.Chunk14532
import ArealUK.Chunk14533
import ArealUK.Chunk14534
import ArealUK.Chunk14535
import ArealUK.Chunk14536
import ArealUK.Chunk14537
import ArealUK.Chunk14538
import ArealUK.Chunk14539
import ArealUK.Chunk14540
import ArealUK.Chunk14541
import ArealUK.Chunk14542
import ArealUK.Chunk14543
import ArealUK.Chunk14544
import ArealUK.Chunk14545
import ArealUK.Chunk14546
import ArealUK.Chunk14547
import ArealUK.Chunk14548
import ArealUK.Chunk14549
import ArealUK.Chunk14550
import ArealUK.Chunk14551
import ArealUK.Chunk14552
import ArealUK.Chunk14553
import ArealUK.Chunk14554
import ArealUK.Chunk14555
import ArealUK.Chunk14556
import ArealUK.Chunk14557
import ArealUK.Chunk14558
import ArealUK.Chunk14559
import ArealUK.Chunk14560
import ArealUK.Chunk14561
import ArealUK.Chunk14562
import ArealUK.Chunk14563
import ArealUK.Chunk14564
import ArealUK.Chunk14565
import ArealUK.Chunk14566
import ArealUK.Chunk14567
import ArealUK.Chunk14568
import ArealUK.Chunk14569
import ArealUK.Chunk14570
import ArealUK.Chunk14571
import ArealUK.Chunk14572
import ArealUK.Chunk14573
import ArealUK.Chunk14574
import ArealUK.Chunk14575
import ArealUK.Chunk14576
import ArealUK.Chunk14577
import ArealUK.Chunk14578
import ArealUK.Chunk14579
import ArealUK.Chunk14580
import ArealUK.Chunk14581
import ArealUK.Chunk14582
import ArealUK.Chunk14583
import ArealUK.Chunk14584
import ArealUK.Chunk14585
import ArealUK.Chunk14586
import ArealUK.Chunk14587
import ArealUK.Chunk14588
import ArealUK.Chunk14589
import ArealUK.Chunk14590
import ArealUK.Chunk14591
import ArealUK.Chunk14592
import ArealUK.Chunk14593
import ArealUK.Chunk14594
import ArealUK.Chunk14595
import ArealUK.Chunk14596
import ArealUK.Chunk14597
import ArealUK.Chunk14598
import ArealUK.Chunk14599
import Areal.UCert.LeavesKGen

/-! Group 145 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_145 : leavesOK ctxLitU 149831250000 0 ((leaves.drop 29000).take 200) 302125000000 1 = true := by
  have s99 := ArealUCore.ArealUK.chunk_14599
  have s98 : leavesOK ctxLitU 151037500000 0 ((leaves.drop 29196).take 4) 302125000000 1 = true :=
    take_step (n := 2) (t := 4) (b := 29198) rfl rfl ArealUCore.ArealUK.chunk_14598 s99
  have s97 : leavesOK ctxLitU 302062500000 1 ((leaves.drop 29194).take 6) 302125000000 1 = true :=
    take_step (n := 2) (t := 6) (b := 29196) rfl rfl ArealUCore.ArealUK.chunk_14597 s98
  have s96 : leavesOK ctxLitU 302050000000 1 ((leaves.drop 29192).take 8) 302125000000 1 = true :=
    take_step (n := 2) (t := 8) (b := 29194) rfl rfl ArealUCore.ArealUK.chunk_14596 s97
  have s95 : leavesOK ctxLitU 302025000000 1 ((leaves.drop 29190).take 10) 302125000000 1 = true :=
    take_step (n := 2) (t := 10) (b := 29192) rfl rfl ArealUCore.ArealUK.chunk_14595 s96
  have s94 : leavesOK ctxLitU 302000000000 1 ((leaves.drop 29188).take 12) 302125000000 1 = true :=
    take_step (n := 2) (t := 12) (b := 29190) rfl rfl ArealUCore.ArealUK.chunk_14594 s95
  have s93 : leavesOK ctxLitU 301975000000 1 ((leaves.drop 29186).take 14) 302125000000 1 = true :=
    take_step (n := 2) (t := 14) (b := 29188) rfl rfl ArealUCore.ArealUK.chunk_14593 s94
  have s92 : leavesOK ctxLitU 301950000000 1 ((leaves.drop 29184).take 16) 302125000000 1 = true :=
    take_step (n := 2) (t := 16) (b := 29186) rfl rfl ArealUCore.ArealUK.chunk_14592 s93
  have s91 : leavesOK ctxLitU 150962500000 0 ((leaves.drop 29182).take 18) 302125000000 1 = true :=
    take_step (n := 2) (t := 18) (b := 29184) rfl rfl ArealUCore.ArealUK.chunk_14591 s92
  have s90 : leavesOK ctxLitU 150950000000 0 ((leaves.drop 29180).take 20) 302125000000 1 = true :=
    take_step (n := 2) (t := 20) (b := 29182) rfl rfl ArealUCore.ArealUK.chunk_14590 s91
  have s89 : leavesOK ctxLitU 150937500000 0 ((leaves.drop 29178).take 22) 302125000000 1 = true :=
    take_step (n := 2) (t := 22) (b := 29180) rfl rfl ArealUCore.ArealUK.chunk_14589 s90
  have s88 : leavesOK ctxLitU 150925000000 0 ((leaves.drop 29176).take 24) 302125000000 1 = true :=
    take_step (n := 2) (t := 24) (b := 29178) rfl rfl ArealUCore.ArealUK.chunk_14588 s89
  have s87 : leavesOK ctxLitU 301825000000 1 ((leaves.drop 29174).take 26) 302125000000 1 = true :=
    take_step (n := 2) (t := 26) (b := 29176) rfl rfl ArealUCore.ArealUK.chunk_14587 s88
  have s86 : leavesOK ctxLitU 301800000000 1 ((leaves.drop 29172).take 28) 302125000000 1 = true :=
    take_step (n := 2) (t := 28) (b := 29174) rfl rfl ArealUCore.ArealUK.chunk_14586 s87
  have s85 : leavesOK ctxLitU 301775000000 1 ((leaves.drop 29170).take 30) 302125000000 1 = true :=
    take_step (n := 2) (t := 30) (b := 29172) rfl rfl ArealUCore.ArealUK.chunk_14585 s86
  have s84 : leavesOK ctxLitU 301750000000 1 ((leaves.drop 29168).take 32) 302125000000 1 = true :=
    take_step (n := 2) (t := 32) (b := 29170) rfl rfl ArealUCore.ArealUK.chunk_14584 s85
  have s83 : leavesOK ctxLitU 150862500000 0 ((leaves.drop 29166).take 34) 302125000000 1 = true :=
    take_step (n := 2) (t := 34) (b := 29168) rfl rfl ArealUCore.ArealUK.chunk_14583 s84
  have s82 : leavesOK ctxLitU 150850000000 0 ((leaves.drop 29164).take 36) 302125000000 1 = true :=
    take_step (n := 2) (t := 36) (b := 29166) rfl rfl ArealUCore.ArealUK.chunk_14582 s83
  have s81 : leavesOK ctxLitU 150837500000 0 ((leaves.drop 29162).take 38) 302125000000 1 = true :=
    take_step (n := 2) (t := 38) (b := 29164) rfl rfl ArealUCore.ArealUK.chunk_14581 s82
  have s80 : leavesOK ctxLitU 150825000000 0 ((leaves.drop 29160).take 40) 302125000000 1 = true :=
    take_step (n := 2) (t := 40) (b := 29162) rfl rfl ArealUCore.ArealUK.chunk_14580 s81
  have s79 : leavesOK ctxLitU 301625000000 1 ((leaves.drop 29158).take 42) 302125000000 1 = true :=
    take_step (n := 2) (t := 42) (b := 29160) rfl rfl ArealUCore.ArealUK.chunk_14579 s80
  have s78 : leavesOK ctxLitU 301587500000 1 ((leaves.drop 29156).take 44) 302125000000 1 = true :=
    take_step (n := 2) (t := 44) (b := 29158) rfl rfl ArealUCore.ArealUK.chunk_14578 s79
  have s77 : leavesOK ctxLitU 301562500000 1 ((leaves.drop 29154).take 46) 302125000000 1 = true :=
    take_step (n := 2) (t := 46) (b := 29156) rfl rfl ArealUCore.ArealUK.chunk_14577 s78
  have s76 : leavesOK ctxLitU 150768750000 0 ((leaves.drop 29152).take 48) 302125000000 1 = true :=
    take_step (n := 2) (t := 48) (b := 29154) rfl rfl ArealUCore.ArealUK.chunk_14576 s77
  have s75 : leavesOK ctxLitU 150756250000 0 ((leaves.drop 29150).take 50) 302125000000 1 = true :=
    take_step (n := 2) (t := 50) (b := 29152) rfl rfl ArealUCore.ArealUK.chunk_14575 s76
  have s74 : leavesOK ctxLitU 150743750000 0 ((leaves.drop 29148).take 52) 302125000000 1 = true :=
    take_step (n := 2) (t := 52) (b := 29150) rfl rfl ArealUCore.ArealUK.chunk_14574 s75
  have s73 : leavesOK ctxLitU 150731250000 0 ((leaves.drop 29146).take 54) 302125000000 1 = true :=
    take_step (n := 2) (t := 54) (b := 29148) rfl rfl ArealUCore.ArealUK.chunk_14573 s74
  have s72 : leavesOK ctxLitU 301437500000 1 ((leaves.drop 29144).take 56) 302125000000 1 = true :=
    take_step (n := 2) (t := 56) (b := 29146) rfl rfl ArealUCore.ArealUK.chunk_14572 s73
  have s71 : leavesOK ctxLitU 301412500000 1 ((leaves.drop 29142).take 58) 302125000000 1 = true :=
    take_step (n := 2) (t := 58) (b := 29144) rfl rfl ArealUCore.ArealUK.chunk_14571 s72
  have s70 : leavesOK ctxLitU 602775000000 2 ((leaves.drop 29140).take 60) 302125000000 1 = true :=
    take_step (n := 2) (t := 60) (b := 29142) rfl rfl ArealUCore.ArealUK.chunk_14570 s71
  have s69 : leavesOK ctxLitU 301350000000 1 ((leaves.drop 29138).take 62) 302125000000 1 = true :=
    take_step (n := 2) (t := 62) (b := 29140) rfl rfl ArealUCore.ArealUK.chunk_14569 s70
  have s68 : leavesOK ctxLitU 301325000000 1 ((leaves.drop 29136).take 64) 302125000000 1 = true :=
    take_step (n := 2) (t := 64) (b := 29138) rfl rfl ArealUCore.ArealUK.chunk_14568 s69
  have s67 : leavesOK ctxLitU 301300000000 1 ((leaves.drop 29134).take 66) 302125000000 1 = true :=
    take_step (n := 2) (t := 66) (b := 29136) rfl rfl ArealUCore.ArealUK.chunk_14567 s68
  have s66 : leavesOK ctxLitU 150637500000 0 ((leaves.drop 29132).take 68) 302125000000 1 = true :=
    take_step (n := 2) (t := 68) (b := 29134) rfl rfl ArealUCore.ArealUK.chunk_14566 s67
  have s65 : leavesOK ctxLitU 301262500000 1 ((leaves.drop 29130).take 70) 302125000000 1 = true :=
    take_step (n := 2) (t := 70) (b := 29132) rfl rfl ArealUCore.ArealUK.chunk_14565 s66
  have s64 : leavesOK ctxLitU 301250000000 1 ((leaves.drop 29128).take 72) 302125000000 1 = true :=
    take_step (n := 2) (t := 72) (b := 29130) rfl rfl ArealUCore.ArealUK.chunk_14564 s65
  have s63 : leavesOK ctxLitU 301225000000 1 ((leaves.drop 29126).take 74) 302125000000 1 = true :=
    take_step (n := 2) (t := 74) (b := 29128) rfl rfl ArealUCore.ArealUK.chunk_14563 s64
  have s62 : leavesOK ctxLitU 301200000000 1 ((leaves.drop 29124).take 76) 302125000000 1 = true :=
    take_step (n := 2) (t := 76) (b := 29126) rfl rfl ArealUCore.ArealUK.chunk_14562 s63
  have s61 : leavesOK ctxLitU 301175000000 1 ((leaves.drop 29122).take 78) 302125000000 1 = true :=
    take_step (n := 2) (t := 78) (b := 29124) rfl rfl ArealUCore.ArealUK.chunk_14561 s62
  have s60 : leavesOK ctxLitU 301150000000 1 ((leaves.drop 29120).take 80) 302125000000 1 = true :=
    take_step (n := 2) (t := 80) (b := 29122) rfl rfl ArealUCore.ArealUK.chunk_14560 s61
  have s59 : leavesOK ctxLitU 150562500000 0 ((leaves.drop 29118).take 82) 302125000000 1 = true :=
    take_step (n := 2) (t := 82) (b := 29120) rfl rfl ArealUCore.ArealUK.chunk_14559 s60
  have s58 : leavesOK ctxLitU 150550000000 0 ((leaves.drop 29116).take 84) 302125000000 1 = true :=
    take_step (n := 2) (t := 84) (b := 29118) rfl rfl ArealUCore.ArealUK.chunk_14558 s59
  have s57 : leavesOK ctxLitU 150537500000 0 ((leaves.drop 29114).take 86) 302125000000 1 = true :=
    take_step (n := 2) (t := 86) (b := 29116) rfl rfl ArealUCore.ArealUK.chunk_14557 s58
  have s56 : leavesOK ctxLitU 150525000000 0 ((leaves.drop 29112).take 88) 302125000000 1 = true :=
    take_step (n := 2) (t := 88) (b := 29114) rfl rfl ArealUCore.ArealUK.chunk_14556 s57
  have s55 : leavesOK ctxLitU 301025000000 1 ((leaves.drop 29110).take 90) 302125000000 1 = true :=
    take_step (n := 2) (t := 90) (b := 29112) rfl rfl ArealUCore.ArealUK.chunk_14555 s56
  have s54 : leavesOK ctxLitU 301000000000 1 ((leaves.drop 29108).take 92) 302125000000 1 = true :=
    take_step (n := 2) (t := 92) (b := 29110) rfl rfl ArealUCore.ArealUK.chunk_14554 s55
  have s53 : leavesOK ctxLitU 601950000000 2 ((leaves.drop 29106).take 94) 302125000000 1 = true :=
    take_step (n := 2) (t := 94) (b := 29108) rfl rfl ArealUCore.ArealUK.chunk_14553 s54
  have s52 : leavesOK ctxLitU 300937500000 1 ((leaves.drop 29104).take 96) 302125000000 1 = true :=
    take_step (n := 2) (t := 96) (b := 29106) rfl rfl ArealUCore.ArealUK.chunk_14552 s53
  have s51 : leavesOK ctxLitU 300912500000 1 ((leaves.drop 29102).take 98) 302125000000 1 = true :=
    take_step (n := 2) (t := 98) (b := 29104) rfl rfl ArealUCore.ArealUK.chunk_14551 s52
  have s50 : leavesOK ctxLitU 150443750000 0 ((leaves.drop 29100).take 100) 302125000000 1 = true :=
    take_step (n := 2) (t := 100) (b := 29102) rfl rfl ArealUCore.ArealUK.chunk_14550 s51
  have s49 : leavesOK ctxLitU 300868750000 1 ((leaves.drop 29098).take 102) 302125000000 1 = true :=
    take_step (n := 2) (t := 102) (b := 29100) rfl rfl ArealUCore.ArealUK.chunk_14549 s50
  have s48 : leavesOK ctxLitU 300856250000 1 ((leaves.drop 29096).take 104) 302125000000 1 = true :=
    take_step (n := 2) (t := 104) (b := 29098) rfl rfl ArealUCore.ArealUK.chunk_14548 s49
  have s47 : leavesOK ctxLitU 300837500000 1 ((leaves.drop 29094).take 106) 302125000000 1 = true :=
    take_step (n := 2) (t := 106) (b := 29096) rfl rfl ArealUCore.ArealUK.chunk_14547 s48
  have s46 : leavesOK ctxLitU 300812500000 1 ((leaves.drop 29092).take 108) 302125000000 1 = true :=
    take_step (n := 2) (t := 108) (b := 29094) rfl rfl ArealUCore.ArealUK.chunk_14546 s47
  have s45 : leavesOK ctxLitU 300787500000 1 ((leaves.drop 29090).take 110) 302125000000 1 = true :=
    take_step (n := 2) (t := 110) (b := 29092) rfl rfl ArealUCore.ArealUK.chunk_14545 s46
  have s44 : leavesOK ctxLitU 300762500000 1 ((leaves.drop 29088).take 112) 302125000000 1 = true :=
    take_step (n := 2) (t := 112) (b := 29090) rfl rfl ArealUCore.ArealUK.chunk_14544 s45
  have s43 : leavesOK ctxLitU 150368750000 0 ((leaves.drop 29086).take 114) 302125000000 1 = true :=
    take_step (n := 2) (t := 114) (b := 29088) rfl rfl ArealUCore.ArealUK.chunk_14543 s44
  have s42 : leavesOK ctxLitU 150356250000 0 ((leaves.drop 29084).take 116) 302125000000 1 = true :=
    take_step (n := 2) (t := 116) (b := 29086) rfl rfl ArealUCore.ArealUK.chunk_14542 s43
  have s41 : leavesOK ctxLitU 150343750000 0 ((leaves.drop 29082).take 118) 302125000000 1 = true :=
    take_step (n := 2) (t := 118) (b := 29084) rfl rfl ArealUCore.ArealUK.chunk_14541 s42
  have s40 : leavesOK ctxLitU 150331250000 0 ((leaves.drop 29080).take 120) 302125000000 1 = true :=
    take_step (n := 2) (t := 120) (b := 29082) rfl rfl ArealUCore.ArealUK.chunk_14540 s41
  have s39 : leavesOK ctxLitU 300637500000 1 ((leaves.drop 29078).take 122) 302125000000 1 = true :=
    take_step (n := 2) (t := 122) (b := 29080) rfl rfl ArealUCore.ArealUK.chunk_14539 s40
  have s38 : leavesOK ctxLitU 300612500000 1 ((leaves.drop 29076).take 124) 302125000000 1 = true :=
    take_step (n := 2) (t := 124) (b := 29078) rfl rfl ArealUCore.ArealUK.chunk_14538 s39
  have s37 : leavesOK ctxLitU 300587500000 1 ((leaves.drop 29074).take 126) 302125000000 1 = true :=
    take_step (n := 2) (t := 126) (b := 29076) rfl rfl ArealUCore.ArealUK.chunk_14537 s38
  have s36 : leavesOK ctxLitU 300562500000 1 ((leaves.drop 29072).take 128) 302125000000 1 = true :=
    take_step (n := 2) (t := 128) (b := 29074) rfl rfl ArealUCore.ArealUK.chunk_14536 s37
  have s35 : leavesOK ctxLitU 150268750000 0 ((leaves.drop 29070).take 130) 302125000000 1 = true :=
    take_step (n := 2) (t := 130) (b := 29072) rfl rfl ArealUCore.ArealUK.chunk_14535 s36
  have s34 : leavesOK ctxLitU 150256250000 0 ((leaves.drop 29068).take 132) 302125000000 1 = true :=
    take_step (n := 2) (t := 132) (b := 29070) rfl rfl ArealUCore.ArealUK.chunk_14534 s35
  have s33 : leavesOK ctxLitU 150243750000 0 ((leaves.drop 29066).take 134) 302125000000 1 = true :=
    take_step (n := 2) (t := 134) (b := 29068) rfl rfl ArealUCore.ArealUK.chunk_14533 s34
  have s32 : leavesOK ctxLitU 150231250000 0 ((leaves.drop 29064).take 136) 302125000000 1 = true :=
    take_step (n := 2) (t := 136) (b := 29066) rfl rfl ArealUCore.ArealUK.chunk_14532 s33
  have s31 : leavesOK ctxLitU 300437500000 1 ((leaves.drop 29062).take 138) 302125000000 1 = true :=
    take_step (n := 2) (t := 138) (b := 29064) rfl rfl ArealUCore.ArealUK.chunk_14531 s32
  have s30 : leavesOK ctxLitU 300412500000 1 ((leaves.drop 29060).take 140) 302125000000 1 = true :=
    take_step (n := 2) (t := 140) (b := 29062) rfl rfl ArealUCore.ArealUK.chunk_14530 s31
  have s29 : leavesOK ctxLitU 300387500000 1 ((leaves.drop 29058).take 142) 302125000000 1 = true :=
    take_step (n := 2) (t := 142) (b := 29060) rfl rfl ArealUCore.ArealUK.chunk_14529 s30
  have s28 : leavesOK ctxLitU 300362500000 1 ((leaves.drop 29056).take 144) 302125000000 1 = true :=
    take_step (n := 2) (t := 144) (b := 29058) rfl rfl ArealUCore.ArealUK.chunk_14528 s29
  have s27 : leavesOK ctxLitU 300343750000 1 ((leaves.drop 29054).take 146) 302125000000 1 = true :=
    take_step (n := 2) (t := 146) (b := 29056) rfl rfl ArealUCore.ArealUK.chunk_14527 s28
  have s26 : leavesOK ctxLitU 150162500000 0 ((leaves.drop 29052).take 148) 302125000000 1 = true :=
    take_step (n := 2) (t := 148) (b := 29054) rfl rfl ArealUCore.ArealUK.chunk_14526 s27
  have s25 : leavesOK ctxLitU 150150000000 0 ((leaves.drop 29050).take 150) 302125000000 1 = true :=
    take_step (n := 2) (t := 150) (b := 29052) rfl rfl ArealUCore.ArealUK.chunk_14525 s26
  have s24 : leavesOK ctxLitU 300275000000 1 ((leaves.drop 29048).take 152) 302125000000 1 = true :=
    take_step (n := 2) (t := 152) (b := 29050) rfl rfl ArealUCore.ArealUK.chunk_14524 s25
  have s23 : leavesOK ctxLitU 300250000000 1 ((leaves.drop 29046).take 154) 302125000000 1 = true :=
    take_step (n := 2) (t := 154) (b := 29048) rfl rfl ArealUCore.ArealUK.chunk_14523 s24
  have s22 : leavesOK ctxLitU 600425000000 2 ((leaves.drop 29044).take 156) 302125000000 1 = true :=
    take_step (n := 2) (t := 156) (b := 29046) rfl rfl ArealUCore.ArealUK.chunk_14522 s23
  have s21 : leavesOK ctxLitU 300187500000 1 ((leaves.drop 29042).take 158) 302125000000 1 = true :=
    take_step (n := 2) (t := 158) (b := 29044) rfl rfl ArealUCore.ArealUK.chunk_14521 s22
  have s20 : leavesOK ctxLitU 300162500000 1 ((leaves.drop 29040).take 160) 302125000000 1 = true :=
    take_step (n := 2) (t := 160) (b := 29042) rfl rfl ArealUCore.ArealUK.chunk_14520 s21
  have s19 : leavesOK ctxLitU 150068750000 0 ((leaves.drop 29038).take 162) 302125000000 1 = true :=
    take_step (n := 2) (t := 162) (b := 29040) rfl rfl ArealUCore.ArealUK.chunk_14519 s20
  have s18 : leavesOK ctxLitU 150056250000 0 ((leaves.drop 29036).take 164) 302125000000 1 = true :=
    take_step (n := 2) (t := 164) (b := 29038) rfl rfl ArealUCore.ArealUK.chunk_14518 s19
  have s17 : leavesOK ctxLitU 150043750000 0 ((leaves.drop 29034).take 166) 302125000000 1 = true :=
    take_step (n := 2) (t := 166) (b := 29036) rfl rfl ArealUCore.ArealUK.chunk_14517 s18
  have s16 : leavesOK ctxLitU 150031250000 0 ((leaves.drop 29032).take 168) 302125000000 1 = true :=
    take_step (n := 2) (t := 168) (b := 29034) rfl rfl ArealUCore.ArealUK.chunk_14516 s17
  have s15 : leavesOK ctxLitU 300037500000 1 ((leaves.drop 29030).take 170) 302125000000 1 = true :=
    take_step (n := 2) (t := 170) (b := 29032) rfl rfl ArealUCore.ArealUK.chunk_14515 s16
  have s14 : leavesOK ctxLitU 300012500000 1 ((leaves.drop 29028).take 172) 302125000000 1 = true :=
    take_step (n := 2) (t := 172) (b := 29030) rfl rfl ArealUCore.ArealUK.chunk_14514 s15
  have s13 : leavesOK ctxLitU 299987500000 1 ((leaves.drop 29026).take 174) 302125000000 1 = true :=
    take_step (n := 2) (t := 174) (b := 29028) rfl rfl ArealUCore.ArealUK.chunk_14513 s14
  have s12 : leavesOK ctxLitU 299962500000 1 ((leaves.drop 29024).take 176) 302125000000 1 = true :=
    take_step (n := 2) (t := 176) (b := 29026) rfl rfl ArealUCore.ArealUK.chunk_14512 s13
  have s11 : leavesOK ctxLitU 149968750000 0 ((leaves.drop 29022).take 178) 302125000000 1 = true :=
    take_step (n := 2) (t := 178) (b := 29024) rfl rfl ArealUCore.ArealUK.chunk_14511 s12
  have s10 : leavesOK ctxLitU 149956250000 0 ((leaves.drop 29020).take 180) 302125000000 1 = true :=
    take_step (n := 2) (t := 180) (b := 29022) rfl rfl ArealUCore.ArealUK.chunk_14510 s11
  have s9 : leavesOK ctxLitU 149943750000 0 ((leaves.drop 29018).take 182) 302125000000 1 = true :=
    take_step (n := 2) (t := 182) (b := 29020) rfl rfl ArealUCore.ArealUK.chunk_14509 s10
  have s8 : leavesOK ctxLitU 149931250000 0 ((leaves.drop 29016).take 184) 302125000000 1 = true :=
    take_step (n := 2) (t := 184) (b := 29018) rfl rfl ArealUCore.ArealUK.chunk_14508 s9
  have s7 : leavesOK ctxLitU 299837500000 1 ((leaves.drop 29014).take 186) 302125000000 1 = true :=
    take_step (n := 2) (t := 186) (b := 29016) rfl rfl ArealUCore.ArealUK.chunk_14507 s8
  have s6 : leavesOK ctxLitU 299812500000 1 ((leaves.drop 29012).take 188) 302125000000 1 = true :=
    take_step (n := 2) (t := 188) (b := 29014) rfl rfl ArealUCore.ArealUK.chunk_14506 s7
  have s5 : leavesOK ctxLitU 299787500000 1 ((leaves.drop 29010).take 190) 302125000000 1 = true :=
    take_step (n := 2) (t := 190) (b := 29012) rfl rfl ArealUCore.ArealUK.chunk_14505 s6
  have s4 : leavesOK ctxLitU 299762500000 1 ((leaves.drop 29008).take 192) 302125000000 1 = true :=
    take_step (n := 2) (t := 192) (b := 29010) rfl rfl ArealUCore.ArealUK.chunk_14504 s5
  have s3 : leavesOK ctxLitU 149868750000 0 ((leaves.drop 29006).take 194) 302125000000 1 = true :=
    take_step (n := 2) (t := 194) (b := 29008) rfl rfl ArealUCore.ArealUK.chunk_14503 s4
  have s2 : leavesOK ctxLitU 149856250000 0 ((leaves.drop 29004).take 196) 302125000000 1 = true :=
    take_step (n := 2) (t := 196) (b := 29006) rfl rfl ArealUCore.ArealUK.chunk_14502 s3
  have s1 : leavesOK ctxLitU 149843750000 0 ((leaves.drop 29002).take 198) 302125000000 1 = true :=
    take_step (n := 2) (t := 198) (b := 29004) rfl rfl ArealUCore.ArealUK.chunk_14501 s2
  have s0 : leavesOK ctxLitU 149831250000 0 ((leaves.drop 29000).take 200) 302125000000 1 = true :=
    take_step (n := 2) (t := 200) (b := 29002) rfl rfl ArealUCore.ArealUK.chunk_14500 s1
  exact s0

end Areal.UCert

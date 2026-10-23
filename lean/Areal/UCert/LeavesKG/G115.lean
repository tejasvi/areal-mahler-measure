import ArealUK.Chunk11500
import ArealUK.Chunk11501
import ArealUK.Chunk11502
import ArealUK.Chunk11503
import ArealUK.Chunk11504
import ArealUK.Chunk11505
import ArealUK.Chunk11506
import ArealUK.Chunk11507
import ArealUK.Chunk11508
import ArealUK.Chunk11509
import ArealUK.Chunk11510
import ArealUK.Chunk11511
import ArealUK.Chunk11512
import ArealUK.Chunk11513
import ArealUK.Chunk11514
import ArealUK.Chunk11515
import ArealUK.Chunk11516
import ArealUK.Chunk11517
import ArealUK.Chunk11518
import ArealUK.Chunk11519
import ArealUK.Chunk11520
import ArealUK.Chunk11521
import ArealUK.Chunk11522
import ArealUK.Chunk11523
import ArealUK.Chunk11524
import ArealUK.Chunk11525
import ArealUK.Chunk11526
import ArealUK.Chunk11527
import ArealUK.Chunk11528
import ArealUK.Chunk11529
import ArealUK.Chunk11530
import ArealUK.Chunk11531
import ArealUK.Chunk11532
import ArealUK.Chunk11533
import ArealUK.Chunk11534
import ArealUK.Chunk11535
import ArealUK.Chunk11536
import ArealUK.Chunk11537
import ArealUK.Chunk11538
import ArealUK.Chunk11539
import ArealUK.Chunk11540
import ArealUK.Chunk11541
import ArealUK.Chunk11542
import ArealUK.Chunk11543
import ArealUK.Chunk11544
import ArealUK.Chunk11545
import ArealUK.Chunk11546
import ArealUK.Chunk11547
import ArealUK.Chunk11548
import ArealUK.Chunk11549
import ArealUK.Chunk11550
import ArealUK.Chunk11551
import ArealUK.Chunk11552
import ArealUK.Chunk11553
import ArealUK.Chunk11554
import ArealUK.Chunk11555
import ArealUK.Chunk11556
import ArealUK.Chunk11557
import ArealUK.Chunk11558
import ArealUK.Chunk11559
import ArealUK.Chunk11560
import ArealUK.Chunk11561
import ArealUK.Chunk11562
import ArealUK.Chunk11563
import ArealUK.Chunk11564
import ArealUK.Chunk11565
import ArealUK.Chunk11566
import ArealUK.Chunk11567
import ArealUK.Chunk11568
import ArealUK.Chunk11569
import ArealUK.Chunk11570
import ArealUK.Chunk11571
import ArealUK.Chunk11572
import ArealUK.Chunk11573
import ArealUK.Chunk11574
import ArealUK.Chunk11575
import ArealUK.Chunk11576
import ArealUK.Chunk11577
import ArealUK.Chunk11578
import ArealUK.Chunk11579
import ArealUK.Chunk11580
import ArealUK.Chunk11581
import ArealUK.Chunk11582
import ArealUK.Chunk11583
import ArealUK.Chunk11584
import ArealUK.Chunk11585
import ArealUK.Chunk11586
import ArealUK.Chunk11587
import ArealUK.Chunk11588
import ArealUK.Chunk11589
import ArealUK.Chunk11590
import ArealUK.Chunk11591
import ArealUK.Chunk11592
import ArealUK.Chunk11593
import ArealUK.Chunk11594
import ArealUK.Chunk11595
import ArealUK.Chunk11596
import ArealUK.Chunk11597
import ArealUK.Chunk11598
import ArealUK.Chunk11599
import Areal.UCert.LeavesKGen

/-! Group 115 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_115 : leavesOK ctxLitU 111875000000 0 ((leaves.drop 23000).take 200) 456750000000 2 = true := by
  have s99 := ArealUCore.ArealUK.chunk_11599
  have s98 : leavesOK ctxLitU 456650000000 2 ((leaves.drop 23196).take 4) 456750000000 2 = true :=
    take_step (n := 2) (t := 4) (b := 23198) rfl rfl ArealUCore.ArealUK.chunk_11598 s99
  have s97 : leavesOK ctxLitU 456600000000 2 ((leaves.drop 23194).take 6) 456750000000 2 = true :=
    take_step (n := 2) (t := 6) (b := 23196) rfl rfl ArealUCore.ArealUK.chunk_11597 s98
  have s96 : leavesOK ctxLitU 456550000000 2 ((leaves.drop 23192).take 8) 456750000000 2 = true :=
    take_step (n := 2) (t := 8) (b := 23194) rfl rfl ArealUCore.ArealUK.chunk_11596 s97
  have s95 : leavesOK ctxLitU 456500000000 2 ((leaves.drop 23190).take 10) 456750000000 2 = true :=
    take_step (n := 2) (t := 10) (b := 23192) rfl rfl ArealUCore.ArealUK.chunk_11595 s96
  have s94 : leavesOK ctxLitU 456450000000 2 ((leaves.drop 23188).take 12) 456750000000 2 = true :=
    take_step (n := 2) (t := 12) (b := 23190) rfl rfl ArealUCore.ArealUK.chunk_11594 s95
  have s93 : leavesOK ctxLitU 456400000000 2 ((leaves.drop 23186).take 14) 456750000000 2 = true :=
    take_step (n := 2) (t := 14) (b := 23188) rfl rfl ArealUCore.ArealUK.chunk_11593 s94
  have s92 : leavesOK ctxLitU 456350000000 2 ((leaves.drop 23184).take 16) 456750000000 2 = true :=
    take_step (n := 2) (t := 16) (b := 23186) rfl rfl ArealUCore.ArealUK.chunk_11592 s93
  have s91 : leavesOK ctxLitU 456300000000 2 ((leaves.drop 23182).take 18) 456750000000 2 = true :=
    take_step (n := 2) (t := 18) (b := 23184) rfl rfl ArealUCore.ArealUK.chunk_11591 s92
  have s90 : leavesOK ctxLitU 456250000000 2 ((leaves.drop 23180).take 20) 456750000000 2 = true :=
    take_step (n := 2) (t := 20) (b := 23182) rfl rfl ArealUCore.ArealUK.chunk_11590 s91
  have s89 : leavesOK ctxLitU 456200000000 2 ((leaves.drop 23178).take 22) 456750000000 2 = true :=
    take_step (n := 2) (t := 22) (b := 23180) rfl rfl ArealUCore.ArealUK.chunk_11589 s90
  have s88 : leavesOK ctxLitU 456150000000 2 ((leaves.drop 23176).take 24) 456750000000 2 = true :=
    take_step (n := 2) (t := 24) (b := 23178) rfl rfl ArealUCore.ArealUK.chunk_11588 s89
  have s87 : leavesOK ctxLitU 456100000000 2 ((leaves.drop 23174).take 26) 456750000000 2 = true :=
    take_step (n := 2) (t := 26) (b := 23176) rfl rfl ArealUCore.ArealUK.chunk_11587 s88
  have s86 : leavesOK ctxLitU 456050000000 2 ((leaves.drop 23172).take 28) 456750000000 2 = true :=
    take_step (n := 2) (t := 28) (b := 23174) rfl rfl ArealUCore.ArealUK.chunk_11586 s87
  have s85 : leavesOK ctxLitU 456000000000 2 ((leaves.drop 23170).take 30) 456750000000 2 = true :=
    take_step (n := 2) (t := 30) (b := 23172) rfl rfl ArealUCore.ArealUK.chunk_11585 s86
  have s84 : leavesOK ctxLitU 455950000000 2 ((leaves.drop 23168).take 32) 456750000000 2 = true :=
    take_step (n := 2) (t := 32) (b := 23170) rfl rfl ArealUCore.ArealUK.chunk_11584 s85
  have s83 : leavesOK ctxLitU 455900000000 2 ((leaves.drop 23166).take 34) 456750000000 2 = true :=
    take_step (n := 2) (t := 34) (b := 23168) rfl rfl ArealUCore.ArealUK.chunk_11583 s84
  have s82 : leavesOK ctxLitU 455850000000 2 ((leaves.drop 23164).take 36) 456750000000 2 = true :=
    take_step (n := 2) (t := 36) (b := 23166) rfl rfl ArealUCore.ArealUK.chunk_11582 s83
  have s81 : leavesOK ctxLitU 455800000000 2 ((leaves.drop 23162).take 38) 456750000000 2 = true :=
    take_step (n := 2) (t := 38) (b := 23164) rfl rfl ArealUCore.ArealUK.chunk_11581 s82
  have s80 : leavesOK ctxLitU 455750000000 2 ((leaves.drop 23160).take 40) 456750000000 2 = true :=
    take_step (n := 2) (t := 40) (b := 23162) rfl rfl ArealUCore.ArealUK.chunk_11580 s81
  have s79 : leavesOK ctxLitU 455700000000 2 ((leaves.drop 23158).take 42) 456750000000 2 = true :=
    take_step (n := 2) (t := 42) (b := 23160) rfl rfl ArealUCore.ArealUK.chunk_11579 s80
  have s78 : leavesOK ctxLitU 455650000000 2 ((leaves.drop 23156).take 44) 456750000000 2 = true :=
    take_step (n := 2) (t := 44) (b := 23158) rfl rfl ArealUCore.ArealUK.chunk_11578 s79
  have s77 : leavesOK ctxLitU 455600000000 2 ((leaves.drop 23154).take 46) 456750000000 2 = true :=
    take_step (n := 2) (t := 46) (b := 23156) rfl rfl ArealUCore.ArealUK.chunk_11577 s78
  have s76 : leavesOK ctxLitU 455550000000 2 ((leaves.drop 23152).take 48) 456750000000 2 = true :=
    take_step (n := 2) (t := 48) (b := 23154) rfl rfl ArealUCore.ArealUK.chunk_11576 s77
  have s75 : leavesOK ctxLitU 455500000000 2 ((leaves.drop 23150).take 50) 456750000000 2 = true :=
    take_step (n := 2) (t := 50) (b := 23152) rfl rfl ArealUCore.ArealUK.chunk_11575 s76
  have s74 : leavesOK ctxLitU 455450000000 2 ((leaves.drop 23148).take 52) 456750000000 2 = true :=
    take_step (n := 2) (t := 52) (b := 23150) rfl rfl ArealUCore.ArealUK.chunk_11574 s75
  have s73 : leavesOK ctxLitU 455400000000 2 ((leaves.drop 23146).take 54) 456750000000 2 = true :=
    take_step (n := 2) (t := 54) (b := 23148) rfl rfl ArealUCore.ArealUK.chunk_11573 s74
  have s72 : leavesOK ctxLitU 455350000000 2 ((leaves.drop 23144).take 56) 456750000000 2 = true :=
    take_step (n := 2) (t := 56) (b := 23146) rfl rfl ArealUCore.ArealUK.chunk_11572 s73
  have s71 : leavesOK ctxLitU 455300000000 2 ((leaves.drop 23142).take 58) 456750000000 2 = true :=
    take_step (n := 2) (t := 58) (b := 23144) rfl rfl ArealUCore.ArealUK.chunk_11571 s72
  have s70 : leavesOK ctxLitU 455250000000 2 ((leaves.drop 23140).take 60) 456750000000 2 = true :=
    take_step (n := 2) (t := 60) (b := 23142) rfl rfl ArealUCore.ArealUK.chunk_11570 s71
  have s69 : leavesOK ctxLitU 455200000000 2 ((leaves.drop 23138).take 62) 456750000000 2 = true :=
    take_step (n := 2) (t := 62) (b := 23140) rfl rfl ArealUCore.ArealUK.chunk_11569 s70
  have s68 : leavesOK ctxLitU 455150000000 2 ((leaves.drop 23136).take 64) 456750000000 2 = true :=
    take_step (n := 2) (t := 64) (b := 23138) rfl rfl ArealUCore.ArealUK.chunk_11568 s69
  have s67 : leavesOK ctxLitU 455100000000 2 ((leaves.drop 23134).take 66) 456750000000 2 = true :=
    take_step (n := 2) (t := 66) (b := 23136) rfl rfl ArealUCore.ArealUK.chunk_11567 s68
  have s66 : leavesOK ctxLitU 455050000000 2 ((leaves.drop 23132).take 68) 456750000000 2 = true :=
    take_step (n := 2) (t := 68) (b := 23134) rfl rfl ArealUCore.ArealUK.chunk_11566 s67
  have s65 : leavesOK ctxLitU 455000000000 2 ((leaves.drop 23130).take 70) 456750000000 2 = true :=
    take_step (n := 2) (t := 70) (b := 23132) rfl rfl ArealUCore.ArealUK.chunk_11565 s66
  have s64 : leavesOK ctxLitU 454950000000 2 ((leaves.drop 23128).take 72) 456750000000 2 = true :=
    take_step (n := 2) (t := 72) (b := 23130) rfl rfl ArealUCore.ArealUK.chunk_11564 s65
  have s63 : leavesOK ctxLitU 454900000000 2 ((leaves.drop 23126).take 74) 456750000000 2 = true :=
    take_step (n := 2) (t := 74) (b := 23128) rfl rfl ArealUCore.ArealUK.chunk_11563 s64
  have s62 : leavesOK ctxLitU 454850000000 2 ((leaves.drop 23124).take 76) 456750000000 2 = true :=
    take_step (n := 2) (t := 76) (b := 23126) rfl rfl ArealUCore.ArealUK.chunk_11562 s63
  have s61 : leavesOK ctxLitU 454800000000 2 ((leaves.drop 23122).take 78) 456750000000 2 = true :=
    take_step (n := 2) (t := 78) (b := 23124) rfl rfl ArealUCore.ArealUK.chunk_11561 s62
  have s60 : leavesOK ctxLitU 454750000000 2 ((leaves.drop 23120).take 80) 456750000000 2 = true :=
    take_step (n := 2) (t := 80) (b := 23122) rfl rfl ArealUCore.ArealUK.chunk_11560 s61
  have s59 : leavesOK ctxLitU 454700000000 2 ((leaves.drop 23118).take 82) 456750000000 2 = true :=
    take_step (n := 2) (t := 82) (b := 23120) rfl rfl ArealUCore.ArealUK.chunk_11559 s60
  have s58 : leavesOK ctxLitU 454650000000 2 ((leaves.drop 23116).take 84) 456750000000 2 = true :=
    take_step (n := 2) (t := 84) (b := 23118) rfl rfl ArealUCore.ArealUK.chunk_11558 s59
  have s57 : leavesOK ctxLitU 454600000000 2 ((leaves.drop 23114).take 86) 456750000000 2 = true :=
    take_step (n := 2) (t := 86) (b := 23116) rfl rfl ArealUCore.ArealUK.chunk_11557 s58
  have s56 : leavesOK ctxLitU 454550000000 2 ((leaves.drop 23112).take 88) 456750000000 2 = true :=
    take_step (n := 2) (t := 88) (b := 23114) rfl rfl ArealUCore.ArealUK.chunk_11556 s57
  have s55 : leavesOK ctxLitU 454500000000 2 ((leaves.drop 23110).take 90) 456750000000 2 = true :=
    take_step (n := 2) (t := 90) (b := 23112) rfl rfl ArealUCore.ArealUK.chunk_11555 s56
  have s54 : leavesOK ctxLitU 454450000000 2 ((leaves.drop 23108).take 92) 456750000000 2 = true :=
    take_step (n := 2) (t := 92) (b := 23110) rfl rfl ArealUCore.ArealUK.chunk_11554 s55
  have s53 : leavesOK ctxLitU 454400000000 2 ((leaves.drop 23106).take 94) 456750000000 2 = true :=
    take_step (n := 2) (t := 94) (b := 23108) rfl rfl ArealUCore.ArealUK.chunk_11553 s54
  have s52 : leavesOK ctxLitU 454350000000 2 ((leaves.drop 23104).take 96) 456750000000 2 = true :=
    take_step (n := 2) (t := 96) (b := 23106) rfl rfl ArealUCore.ArealUK.chunk_11552 s53
  have s51 : leavesOK ctxLitU 454300000000 2 ((leaves.drop 23102).take 98) 456750000000 2 = true :=
    take_step (n := 2) (t := 98) (b := 23104) rfl rfl ArealUCore.ArealUK.chunk_11551 s52
  have s50 : leavesOK ctxLitU 454250000000 2 ((leaves.drop 23100).take 100) 456750000000 2 = true :=
    take_step (n := 2) (t := 100) (b := 23102) rfl rfl ArealUCore.ArealUK.chunk_11550 s51
  have s49 : leavesOK ctxLitU 454200000000 2 ((leaves.drop 23098).take 102) 456750000000 2 = true :=
    take_step (n := 2) (t := 102) (b := 23100) rfl rfl ArealUCore.ArealUK.chunk_11549 s50
  have s48 : leavesOK ctxLitU 454150000000 2 ((leaves.drop 23096).take 104) 456750000000 2 = true :=
    take_step (n := 2) (t := 104) (b := 23098) rfl rfl ArealUCore.ArealUK.chunk_11548 s49
  have s47 : leavesOK ctxLitU 454100000000 2 ((leaves.drop 23094).take 106) 456750000000 2 = true :=
    take_step (n := 2) (t := 106) (b := 23096) rfl rfl ArealUCore.ArealUK.chunk_11547 s48
  have s46 : leavesOK ctxLitU 454062500000 2 ((leaves.drop 23092).take 108) 456750000000 2 = true :=
    take_step (n := 2) (t := 108) (b := 23094) rfl rfl ArealUCore.ArealUK.chunk_11546 s47
  have s45 : leavesOK ctxLitU 227012500000 1 ((leaves.drop 23090).take 110) 456750000000 2 = true :=
    take_step (n := 2) (t := 110) (b := 23092) rfl rfl ArealUCore.ArealUK.chunk_11545 s46
  have s44 : leavesOK ctxLitU 226993750000 1 ((leaves.drop 23088).take 112) 456750000000 2 = true :=
    take_step (n := 2) (t := 112) (b := 23090) rfl rfl ArealUCore.ArealUK.chunk_11544 s45
  have s43 : leavesOK ctxLitU 453975000000 2 ((leaves.drop 23086).take 114) 456750000000 2 = true :=
    take_step (n := 2) (t := 114) (b := 23088) rfl rfl ArealUCore.ArealUK.chunk_11543 s44
  have s42 : leavesOK ctxLitU 453962500000 2 ((leaves.drop 23084).take 116) 456750000000 2 = true :=
    take_step (n := 2) (t := 116) (b := 23086) rfl rfl ArealUCore.ArealUK.chunk_11542 s43
  have s41 : leavesOK ctxLitU 226968750000 1 ((leaves.drop 23082).take 118) 456750000000 2 = true :=
    take_step (n := 2) (t := 118) (b := 23084) rfl rfl ArealUCore.ArealUK.chunk_11541 s42
  have s40 : leavesOK ctxLitU 453925000000 2 ((leaves.drop 23080).take 120) 456750000000 2 = true :=
    take_step (n := 2) (t := 120) (b := 23082) rfl rfl ArealUCore.ArealUK.chunk_11540 s41
  have s39 : leavesOK ctxLitU 453912500000 2 ((leaves.drop 23078).take 122) 456750000000 2 = true :=
    take_step (n := 2) (t := 122) (b := 23080) rfl rfl ArealUCore.ArealUK.chunk_11539 s40
  have s38 : leavesOK ctxLitU 113468750000 0 ((leaves.drop 23076).take 124) 456750000000 2 = true :=
    take_step (n := 2) (t := 124) (b := 23078) rfl rfl ArealUCore.ArealUK.chunk_11538 s39
  have s37 : leavesOK ctxLitU 226925000000 1 ((leaves.drop 23074).take 126) 456750000000 2 = true :=
    take_step (n := 2) (t := 126) (b := 23076) rfl rfl ArealUCore.ArealUK.chunk_11537 s38
  have s36 : leavesOK ctxLitU 453831250000 2 ((leaves.drop 23072).take 128) 456750000000 2 = true :=
    take_step (n := 2) (t := 128) (b := 23074) rfl rfl ArealUCore.ArealUK.chunk_11536 s37
  have s35 : leavesOK ctxLitU 113450000000 0 ((leaves.drop 23070).take 130) 456750000000 2 = true :=
    take_step (n := 2) (t := 130) (b := 23072) rfl rfl ArealUCore.ArealUK.chunk_11535 s36
  have s34 : leavesOK ctxLitU 113437500000 0 ((leaves.drop 23068).take 132) 456750000000 2 = true :=
    take_step (n := 2) (t := 132) (b := 23070) rfl rfl ArealUCore.ArealUK.chunk_11534 s35
  have s33 : leavesOK ctxLitU 113425000000 0 ((leaves.drop 23066).take 134) 456750000000 2 = true :=
    take_step (n := 2) (t := 134) (b := 23068) rfl rfl ArealUCore.ArealUK.chunk_11533 s34
  have s32 : leavesOK ctxLitU 113412500000 0 ((leaves.drop 23064).take 136) 456750000000 2 = true :=
    take_step (n := 2) (t := 136) (b := 23066) rfl rfl ArealUCore.ArealUK.chunk_11532 s33
  have s31 : leavesOK ctxLitU 113400000000 0 ((leaves.drop 23062).take 138) 456750000000 2 = true :=
    take_step (n := 2) (t := 138) (b := 23064) rfl rfl ArealUCore.ArealUK.chunk_11531 s32
  have s30 : leavesOK ctxLitU 113375000000 0 ((leaves.drop 23060).take 140) 456750000000 2 = true :=
    take_step (n := 2) (t := 140) (b := 23062) rfl rfl ArealUCore.ArealUK.chunk_11530 s31
  have s29 : leavesOK ctxLitU 113325000000 0 ((leaves.drop 23058).take 142) 456750000000 2 = true :=
    take_step (n := 2) (t := 142) (b := 23060) rfl rfl ArealUCore.ArealUK.chunk_11529 s30
  have s28 : leavesOK ctxLitU 113275000000 0 ((leaves.drop 23056).take 144) 456750000000 2 = true :=
    take_step (n := 2) (t := 144) (b := 23058) rfl rfl ArealUCore.ArealUK.chunk_11528 s29
  have s27 : leavesOK ctxLitU 113225000000 0 ((leaves.drop 23054).take 146) 456750000000 2 = true :=
    take_step (n := 2) (t := 146) (b := 23056) rfl rfl ArealUCore.ArealUK.chunk_11527 s28
  have s26 : leavesOK ctxLitU 113175000000 0 ((leaves.drop 23052).take 148) 456750000000 2 = true :=
    take_step (n := 2) (t := 148) (b := 23054) rfl rfl ArealUCore.ArealUK.chunk_11526 s27
  have s25 : leavesOK ctxLitU 113125000000 0 ((leaves.drop 23050).take 150) 456750000000 2 = true :=
    take_step (n := 2) (t := 150) (b := 23052) rfl rfl ArealUCore.ArealUK.chunk_11525 s26
  have s24 : leavesOK ctxLitU 113075000000 0 ((leaves.drop 23048).take 152) 456750000000 2 = true :=
    take_step (n := 2) (t := 152) (b := 23050) rfl rfl ArealUCore.ArealUK.chunk_11524 s25
  have s23 : leavesOK ctxLitU 113025000000 0 ((leaves.drop 23046).take 154) 456750000000 2 = true :=
    take_step (n := 2) (t := 154) (b := 23048) rfl rfl ArealUCore.ArealUK.chunk_11523 s24
  have s22 : leavesOK ctxLitU 112975000000 0 ((leaves.drop 23044).take 156) 456750000000 2 = true :=
    take_step (n := 2) (t := 156) (b := 23046) rfl rfl ArealUCore.ArealUK.chunk_11522 s23
  have s21 : leavesOK ctxLitU 112925000000 0 ((leaves.drop 23042).take 158) 456750000000 2 = true :=
    take_step (n := 2) (t := 158) (b := 23044) rfl rfl ArealUCore.ArealUK.chunk_11521 s22
  have s20 : leavesOK ctxLitU 112875000000 0 ((leaves.drop 23040).take 160) 456750000000 2 = true :=
    take_step (n := 2) (t := 160) (b := 23042) rfl rfl ArealUCore.ArealUK.chunk_11520 s21
  have s19 : leavesOK ctxLitU 112825000000 0 ((leaves.drop 23038).take 162) 456750000000 2 = true :=
    take_step (n := 2) (t := 162) (b := 23040) rfl rfl ArealUCore.ArealUK.chunk_11519 s20
  have s18 : leavesOK ctxLitU 112775000000 0 ((leaves.drop 23036).take 164) 456750000000 2 = true :=
    take_step (n := 2) (t := 164) (b := 23038) rfl rfl ArealUCore.ArealUK.chunk_11518 s19
  have s17 : leavesOK ctxLitU 112725000000 0 ((leaves.drop 23034).take 166) 456750000000 2 = true :=
    take_step (n := 2) (t := 166) (b := 23036) rfl rfl ArealUCore.ArealUK.chunk_11517 s18
  have s16 : leavesOK ctxLitU 112675000000 0 ((leaves.drop 23032).take 168) 456750000000 2 = true :=
    take_step (n := 2) (t := 168) (b := 23034) rfl rfl ArealUCore.ArealUK.chunk_11516 s17
  have s15 : leavesOK ctxLitU 112625000000 0 ((leaves.drop 23030).take 170) 456750000000 2 = true :=
    take_step (n := 2) (t := 170) (b := 23032) rfl rfl ArealUCore.ArealUK.chunk_11515 s16
  have s14 : leavesOK ctxLitU 112575000000 0 ((leaves.drop 23028).take 172) 456750000000 2 = true :=
    take_step (n := 2) (t := 172) (b := 23030) rfl rfl ArealUCore.ArealUK.chunk_11514 s15
  have s13 : leavesOK ctxLitU 112525000000 0 ((leaves.drop 23026).take 174) 456750000000 2 = true :=
    take_step (n := 2) (t := 174) (b := 23028) rfl rfl ArealUCore.ArealUK.chunk_11513 s14
  have s12 : leavesOK ctxLitU 112475000000 0 ((leaves.drop 23024).take 176) 456750000000 2 = true :=
    take_step (n := 2) (t := 176) (b := 23026) rfl rfl ArealUCore.ArealUK.chunk_11512 s13
  have s11 : leavesOK ctxLitU 112425000000 0 ((leaves.drop 23022).take 178) 456750000000 2 = true :=
    take_step (n := 2) (t := 178) (b := 23024) rfl rfl ArealUCore.ArealUK.chunk_11511 s12
  have s10 : leavesOK ctxLitU 112375000000 0 ((leaves.drop 23020).take 180) 456750000000 2 = true :=
    take_step (n := 2) (t := 180) (b := 23022) rfl rfl ArealUCore.ArealUK.chunk_11510 s11
  have s9 : leavesOK ctxLitU 112325000000 0 ((leaves.drop 23018).take 182) 456750000000 2 = true :=
    take_step (n := 2) (t := 182) (b := 23020) rfl rfl ArealUCore.ArealUK.chunk_11509 s10
  have s8 : leavesOK ctxLitU 112275000000 0 ((leaves.drop 23016).take 184) 456750000000 2 = true :=
    take_step (n := 2) (t := 184) (b := 23018) rfl rfl ArealUCore.ArealUK.chunk_11508 s9
  have s7 : leavesOK ctxLitU 112225000000 0 ((leaves.drop 23014).take 186) 456750000000 2 = true :=
    take_step (n := 2) (t := 186) (b := 23016) rfl rfl ArealUCore.ArealUK.chunk_11507 s8
  have s6 : leavesOK ctxLitU 112175000000 0 ((leaves.drop 23012).take 188) 456750000000 2 = true :=
    take_step (n := 2) (t := 188) (b := 23014) rfl rfl ArealUCore.ArealUK.chunk_11506 s7
  have s5 : leavesOK ctxLitU 112125000000 0 ((leaves.drop 23010).take 190) 456750000000 2 = true :=
    take_step (n := 2) (t := 190) (b := 23012) rfl rfl ArealUCore.ArealUK.chunk_11505 s6
  have s4 : leavesOK ctxLitU 112075000000 0 ((leaves.drop 23008).take 192) 456750000000 2 = true :=
    take_step (n := 2) (t := 192) (b := 23010) rfl rfl ArealUCore.ArealUK.chunk_11504 s5
  have s3 : leavesOK ctxLitU 112025000000 0 ((leaves.drop 23006).take 194) 456750000000 2 = true :=
    take_step (n := 2) (t := 194) (b := 23008) rfl rfl ArealUCore.ArealUK.chunk_11503 s4
  have s2 : leavesOK ctxLitU 111975000000 0 ((leaves.drop 23004).take 196) 456750000000 2 = true :=
    take_step (n := 2) (t := 196) (b := 23006) rfl rfl ArealUCore.ArealUK.chunk_11502 s3
  have s1 : leavesOK ctxLitU 111925000000 0 ((leaves.drop 23002).take 198) 456750000000 2 = true :=
    take_step (n := 2) (t := 198) (b := 23004) rfl rfl ArealUCore.ArealUK.chunk_11501 s2
  have s0 : leavesOK ctxLitU 111875000000 0 ((leaves.drop 23000).take 200) 456750000000 2 = true :=
    take_step (n := 2) (t := 200) (b := 23002) rfl rfl ArealUCore.ArealUK.chunk_11500 s1
  exact s0

end Areal.UCert

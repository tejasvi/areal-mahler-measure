import ArealUK.Chunk12400
import ArealUK.Chunk12401
import ArealUK.Chunk12402
import ArealUK.Chunk12403
import ArealUK.Chunk12404
import ArealUK.Chunk12405
import ArealUK.Chunk12406
import ArealUK.Chunk12407
import ArealUK.Chunk12408
import ArealUK.Chunk12409
import ArealUK.Chunk12410
import ArealUK.Chunk12411
import ArealUK.Chunk12412
import ArealUK.Chunk12413
import ArealUK.Chunk12414
import ArealUK.Chunk12415
import ArealUK.Chunk12416
import ArealUK.Chunk12417
import ArealUK.Chunk12418
import ArealUK.Chunk12419
import ArealUK.Chunk12420
import ArealUK.Chunk12421
import ArealUK.Chunk12422
import ArealUK.Chunk12423
import ArealUK.Chunk12424
import ArealUK.Chunk12425
import ArealUK.Chunk12426
import ArealUK.Chunk12427
import ArealUK.Chunk12428
import ArealUK.Chunk12429
import ArealUK.Chunk12430
import ArealUK.Chunk12431
import ArealUK.Chunk12432
import ArealUK.Chunk12433
import ArealUK.Chunk12434
import ArealUK.Chunk12435
import ArealUK.Chunk12436
import ArealUK.Chunk12437
import ArealUK.Chunk12438
import ArealUK.Chunk12439
import ArealUK.Chunk12440
import ArealUK.Chunk12441
import ArealUK.Chunk12442
import ArealUK.Chunk12443
import ArealUK.Chunk12444
import ArealUK.Chunk12445
import ArealUK.Chunk12446
import ArealUK.Chunk12447
import ArealUK.Chunk12448
import ArealUK.Chunk12449
import ArealUK.Chunk12450
import ArealUK.Chunk12451
import ArealUK.Chunk12452
import ArealUK.Chunk12453
import ArealUK.Chunk12454
import ArealUK.Chunk12455
import ArealUK.Chunk12456
import ArealUK.Chunk12457
import ArealUK.Chunk12458
import ArealUK.Chunk12459
import ArealUK.Chunk12460
import ArealUK.Chunk12461
import ArealUK.Chunk12462
import ArealUK.Chunk12463
import ArealUK.Chunk12464
import ArealUK.Chunk12465
import ArealUK.Chunk12466
import ArealUK.Chunk12467
import ArealUK.Chunk12468
import ArealUK.Chunk12469
import ArealUK.Chunk12470
import ArealUK.Chunk12471
import ArealUK.Chunk12472
import ArealUK.Chunk12473
import ArealUK.Chunk12474
import ArealUK.Chunk12475
import ArealUK.Chunk12476
import ArealUK.Chunk12477
import ArealUK.Chunk12478
import ArealUK.Chunk12479
import ArealUK.Chunk12480
import ArealUK.Chunk12481
import ArealUK.Chunk12482
import ArealUK.Chunk12483
import ArealUK.Chunk12484
import ArealUK.Chunk12485
import ArealUK.Chunk12486
import ArealUK.Chunk12487
import ArealUK.Chunk12488
import ArealUK.Chunk12489
import ArealUK.Chunk12490
import ArealUK.Chunk12491
import ArealUK.Chunk12492
import ArealUK.Chunk12493
import ArealUK.Chunk12494
import ArealUK.Chunk12495
import ArealUK.Chunk12496
import ArealUK.Chunk12497
import ArealUK.Chunk12498
import ArealUK.Chunk12499
import Areal.UCert.LeavesKGen

/-! Group 124 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_124 : leavesOK ctxLitU 497775000000 2 ((leaves.drop 24800).take 200) 505125000000 2 = true := by
  have s99 := ArealUCore.ArealUK.chunk_12499
  have s98 : leavesOK ctxLitU 252500000000 1 ((leaves.drop 24996).take 4) 505125000000 2 = true :=
    take_step (n := 2) (t := 4) (b := 24998) rfl rfl ArealUCore.ArealUK.chunk_12498 s99
  have s97 : leavesOK ctxLitU 252450000000 1 ((leaves.drop 24994).take 6) 505125000000 2 = true :=
    take_step (n := 2) (t := 6) (b := 24996) rfl rfl ArealUCore.ArealUK.chunk_12497 s98
  have s96 : leavesOK ctxLitU 504825000000 2 ((leaves.drop 24992).take 8) 505125000000 2 = true :=
    take_step (n := 2) (t := 8) (b := 24994) rfl rfl ArealUCore.ArealUK.chunk_12496 s97
  have s95 : leavesOK ctxLitU 504775000000 2 ((leaves.drop 24990).take 10) 505125000000 2 = true :=
    take_step (n := 2) (t := 10) (b := 24992) rfl rfl ArealUCore.ArealUK.chunk_12495 s96
  have s94 : leavesOK ctxLitU 504725000000 2 ((leaves.drop 24988).take 12) 505125000000 2 = true :=
    take_step (n := 2) (t := 12) (b := 24990) rfl rfl ArealUCore.ArealUK.chunk_12494 s95
  have s93 : leavesOK ctxLitU 504675000000 2 ((leaves.drop 24986).take 14) 505125000000 2 = true :=
    take_step (n := 2) (t := 14) (b := 24988) rfl rfl ArealUCore.ArealUK.chunk_12493 s94
  have s92 : leavesOK ctxLitU 504625000000 2 ((leaves.drop 24984).take 16) 505125000000 2 = true :=
    take_step (n := 2) (t := 16) (b := 24986) rfl rfl ArealUCore.ArealUK.chunk_12492 s93
  have s91 : leavesOK ctxLitU 252275000000 1 ((leaves.drop 24982).take 18) 505125000000 2 = true :=
    take_step (n := 2) (t := 18) (b := 24984) rfl rfl ArealUCore.ArealUK.chunk_12491 s92
  have s90 : leavesOK ctxLitU 252237500000 1 ((leaves.drop 24980).take 20) 505125000000 2 = true :=
    take_step (n := 2) (t := 20) (b := 24982) rfl rfl ArealUCore.ArealUK.chunk_12490 s91
  have s89 : leavesOK ctxLitU 504450000000 2 ((leaves.drop 24978).take 22) 505125000000 2 = true :=
    take_step (n := 2) (t := 22) (b := 24980) rfl rfl ArealUCore.ArealUK.chunk_12489 s90
  have s88 : leavesOK ctxLitU 252200000000 1 ((leaves.drop 24976).take 24) 505125000000 2 = true :=
    take_step (n := 2) (t := 24) (b := 24978) rfl rfl ArealUCore.ArealUK.chunk_12488 s89
  have s87 : leavesOK ctxLitU 126087500000 0 ((leaves.drop 24974).take 26) 505125000000 2 = true :=
    take_step (n := 2) (t := 26) (b := 24976) rfl rfl ArealUCore.ArealUK.chunk_12487 s88
  have s86 : leavesOK ctxLitU 126075000000 0 ((leaves.drop 24972).take 28) 505125000000 2 = true :=
    take_step (n := 2) (t := 28) (b := 24974) rfl rfl ArealUCore.ArealUK.chunk_12486 s87
  have s85 : leavesOK ctxLitU 126062500000 0 ((leaves.drop 24970).take 30) 505125000000 2 = true :=
    take_step (n := 2) (t := 30) (b := 24972) rfl rfl ArealUCore.ArealUK.chunk_12485 s86
  have s84 : leavesOK ctxLitU 126050000000 0 ((leaves.drop 24968).take 32) 505125000000 2 = true :=
    take_step (n := 2) (t := 32) (b := 24970) rfl rfl ArealUCore.ArealUK.chunk_12484 s85
  have s83 : leavesOK ctxLitU 126025000000 0 ((leaves.drop 24966).take 34) 505125000000 2 = true :=
    take_step (n := 2) (t := 34) (b := 24968) rfl rfl ArealUCore.ArealUK.chunk_12483 s84
  have s82 : leavesOK ctxLitU 125975000000 0 ((leaves.drop 24964).take 36) 505125000000 2 = true :=
    take_step (n := 2) (t := 36) (b := 24966) rfl rfl ArealUCore.ArealUK.chunk_12482 s83
  have s81 : leavesOK ctxLitU 125925000000 0 ((leaves.drop 24962).take 38) 505125000000 2 = true :=
    take_step (n := 2) (t := 38) (b := 24964) rfl rfl ArealUCore.ArealUK.chunk_12481 s82
  have s80 : leavesOK ctxLitU 125875000000 0 ((leaves.drop 24960).take 40) 505125000000 2 = true :=
    take_step (n := 2) (t := 40) (b := 24962) rfl rfl ArealUCore.ArealUK.chunk_12480 s81
  have s79 : leavesOK ctxLitU 125825000000 0 ((leaves.drop 24958).take 42) 505125000000 2 = true :=
    take_step (n := 2) (t := 42) (b := 24960) rfl rfl ArealUCore.ArealUK.chunk_12479 s80
  have s78 : leavesOK ctxLitU 125775000000 0 ((leaves.drop 24956).take 44) 505125000000 2 = true :=
    take_step (n := 2) (t := 44) (b := 24958) rfl rfl ArealUCore.ArealUK.chunk_12478 s79
  have s77 : leavesOK ctxLitU 125725000000 0 ((leaves.drop 24954).take 46) 505125000000 2 = true :=
    take_step (n := 2) (t := 46) (b := 24956) rfl rfl ArealUCore.ArealUK.chunk_12477 s78
  have s76 : leavesOK ctxLitU 125675000000 0 ((leaves.drop 24952).take 48) 505125000000 2 = true :=
    take_step (n := 2) (t := 48) (b := 24954) rfl rfl ArealUCore.ArealUK.chunk_12476 s77
  have s75 : leavesOK ctxLitU 514707581943727 12 ((leaves.drop 24950).take 50) 505125000000 2 = true :=
    take_step (n := 2) (t := 50) (b := 24952) rfl rfl ArealUCore.ArealUK.chunk_12475 s76
  have s74 : leavesOK ctxLitU 125625000000 0 ((leaves.drop 24948).take 52) 505125000000 2 = true :=
    take_step (n := 2) (t := 52) (b := 24950) rfl rfl ArealUCore.ArealUK.chunk_12474 s75
  have s73 : leavesOK ctxLitU 125575000000 0 ((leaves.drop 24946).take 54) 505125000000 2 = true :=
    take_step (n := 2) (t := 54) (b := 24948) rfl rfl ArealUCore.ArealUK.chunk_12473 s74
  have s72 : leavesOK ctxLitU 125525000000 0 ((leaves.drop 24944).take 56) 505125000000 2 = true :=
    take_step (n := 2) (t := 56) (b := 24946) rfl rfl ArealUCore.ArealUK.chunk_12472 s73
  have s71 : leavesOK ctxLitU 125475000000 0 ((leaves.drop 24942).take 58) 505125000000 2 = true :=
    take_step (n := 2) (t := 58) (b := 24944) rfl rfl ArealUCore.ArealUK.chunk_12471 s72
  have s70 : leavesOK ctxLitU 125425000000 0 ((leaves.drop 24940).take 60) 505125000000 2 = true :=
    take_step (n := 2) (t := 60) (b := 24942) rfl rfl ArealUCore.ArealUK.chunk_12470 s71
  have s69 : leavesOK ctxLitU 125375000000 0 ((leaves.drop 24938).take 62) 505125000000 2 = true :=
    take_step (n := 2) (t := 62) (b := 24940) rfl rfl ArealUCore.ArealUK.chunk_12469 s70
  have s68 : leavesOK ctxLitU 125325000000 0 ((leaves.drop 24936).take 64) 505125000000 2 = true :=
    take_step (n := 2) (t := 64) (b := 24938) rfl rfl ArealUCore.ArealUK.chunk_12468 s69
  have s67 : leavesOK ctxLitU 125287500000 0 ((leaves.drop 24934).take 66) 505125000000 2 = true :=
    take_step (n := 2) (t := 66) (b := 24936) rfl rfl ArealUCore.ArealUK.chunk_12467 s68
  have s66 : leavesOK ctxLitU 125268750000 0 ((leaves.drop 24932).take 68) 505125000000 2 = true :=
    take_step (n := 2) (t := 68) (b := 24934) rfl rfl ArealUCore.ArealUK.chunk_12466 s67
  have s65 : leavesOK ctxLitU 125256250000 0 ((leaves.drop 24930).take 70) 505125000000 2 = true :=
    take_step (n := 2) (t := 70) (b := 24932) rfl rfl ArealUCore.ArealUK.chunk_12465 s66
  have s64 : leavesOK ctxLitU 125243750000 0 ((leaves.drop 24928).take 72) 505125000000 2 = true :=
    take_step (n := 2) (t := 72) (b := 24930) rfl rfl ArealUCore.ArealUK.chunk_12464 s65
  have s63 : leavesOK ctxLitU 125231250000 0 ((leaves.drop 24926).take 74) 505125000000 2 = true :=
    take_step (n := 2) (t := 74) (b := 24928) rfl rfl ArealUCore.ArealUK.chunk_12463 s64
  have s62 : leavesOK ctxLitU 125218750000 0 ((leaves.drop 24924).take 76) 505125000000 2 = true :=
    take_step (n := 2) (t := 76) (b := 24926) rfl rfl ArealUCore.ArealUK.chunk_12462 s63
  have s61 : leavesOK ctxLitU 250425000000 1 ((leaves.drop 24922).take 78) 505125000000 2 = true :=
    take_step (n := 2) (t := 78) (b := 24924) rfl rfl ArealUCore.ArealUK.chunk_12461 s62
  have s60 : leavesOK ctxLitU 500837500000 2 ((leaves.drop 24920).take 80) 505125000000 2 = true :=
    take_step (n := 2) (t := 80) (b := 24922) rfl rfl ArealUCore.ArealUK.chunk_12460 s61
  have s59 : leavesOK ctxLitU 125200000000 0 ((leaves.drop 24918).take 82) 505125000000 2 = true :=
    take_step (n := 2) (t := 82) (b := 24920) rfl rfl ArealUCore.ArealUK.chunk_12459 s60
  have s58 : leavesOK ctxLitU 125175000000 0 ((leaves.drop 24916).take 84) 505125000000 2 = true :=
    take_step (n := 2) (t := 84) (b := 24918) rfl rfl ArealUCore.ArealUK.chunk_12458 s59
  have s57 : leavesOK ctxLitU 500650000000 2 ((leaves.drop 24914).take 86) 505125000000 2 = true :=
    take_step (n := 2) (t := 86) (b := 24916) rfl rfl ArealUCore.ArealUK.chunk_12457 s58
  have s56 : leavesOK ctxLitU 500600000000 2 ((leaves.drop 24912).take 88) 505125000000 2 = true :=
    take_step (n := 2) (t := 88) (b := 24914) rfl rfl ArealUCore.ArealUK.chunk_12456 s57
  have s55 : leavesOK ctxLitU 500550000000 2 ((leaves.drop 24910).take 90) 505125000000 2 = true :=
    take_step (n := 2) (t := 90) (b := 24912) rfl rfl ArealUCore.ArealUK.chunk_12455 s56
  have s54 : leavesOK ctxLitU 500500000000 2 ((leaves.drop 24908).take 92) 505125000000 2 = true :=
    take_step (n := 2) (t := 92) (b := 24910) rfl rfl ArealUCore.ArealUK.chunk_12454 s55
  have s53 : leavesOK ctxLitU 500450000000 2 ((leaves.drop 24906).take 94) 505125000000 2 = true :=
    take_step (n := 2) (t := 94) (b := 24908) rfl rfl ArealUCore.ArealUK.chunk_12453 s54
  have s52 : leavesOK ctxLitU 500400000000 2 ((leaves.drop 24904).take 96) 505125000000 2 = true :=
    take_step (n := 2) (t := 96) (b := 24906) rfl rfl ArealUCore.ArealUK.chunk_12452 s53
  have s51 : leavesOK ctxLitU 500350000000 2 ((leaves.drop 24902).take 98) 505125000000 2 = true :=
    take_step (n := 2) (t := 98) (b := 24904) rfl rfl ArealUCore.ArealUK.chunk_12451 s52
  have s50 : leavesOK ctxLitU 500300000000 2 ((leaves.drop 24900).take 100) 505125000000 2 = true :=
    take_step (n := 2) (t := 100) (b := 24902) rfl rfl ArealUCore.ArealUK.chunk_12450 s51
  have s49 : leavesOK ctxLitU 250100000000 1 ((leaves.drop 24898).take 102) 505125000000 2 = true :=
    take_step (n := 2) (t := 102) (b := 24900) rfl rfl ArealUCore.ArealUK.chunk_12449 s50
  have s48 : leavesOK ctxLitU 250050000000 1 ((leaves.drop 24896).take 104) 505125000000 2 = true :=
    take_step (n := 2) (t := 104) (b := 24898) rfl rfl ArealUCore.ArealUK.chunk_12448 s49
  have s47 : leavesOK ctxLitU 500050000000 2 ((leaves.drop 24894).take 106) 505125000000 2 = true :=
    take_step (n := 2) (t := 106) (b := 24896) rfl rfl ArealUCore.ArealUK.chunk_12447 s48
  have s46 : leavesOK ctxLitU 500000000000 2 ((leaves.drop 24892).take 108) 505125000000 2 = true :=
    take_step (n := 2) (t := 108) (b := 24894) rfl rfl ArealUCore.ArealUK.chunk_12446 s47
  have s45 : leavesOK ctxLitU 499950000000 2 ((leaves.drop 24890).take 110) 505125000000 2 = true :=
    take_step (n := 2) (t := 110) (b := 24892) rfl rfl ArealUCore.ArealUK.chunk_12445 s46
  have s44 : leavesOK ctxLitU 499900000000 2 ((leaves.drop 24888).take 112) 505125000000 2 = true :=
    take_step (n := 2) (t := 112) (b := 24890) rfl rfl ArealUCore.ArealUK.chunk_12444 s45
  have s43 : leavesOK ctxLitU 249925000000 1 ((leaves.drop 24886).take 114) 505125000000 2 = true :=
    take_step (n := 2) (t := 114) (b := 24888) rfl rfl ArealUCore.ArealUK.chunk_12443 s44
  have s42 : leavesOK ctxLitU 249893750000 1 ((leaves.drop 24884).take 116) 505125000000 2 = true :=
    take_step (n := 2) (t := 116) (b := 24886) rfl rfl ArealUCore.ArealUK.chunk_12442 s43
  have s41 : leavesOK ctxLitU 249881250000 1 ((leaves.drop 24882).take 118) 505125000000 2 = true :=
    take_step (n := 2) (t := 118) (b := 24884) rfl rfl ArealUCore.ArealUK.chunk_12441 s42
  have s40 : leavesOK ctxLitU 124931250000 0 ((leaves.drop 24880).take 120) 505125000000 2 = true :=
    take_step (n := 2) (t := 120) (b := 24882) rfl rfl ArealUCore.ArealUK.chunk_12440 s41
  have s39 : leavesOK ctxLitU 499687500000 2 ((leaves.drop 24878).take 122) 505125000000 2 = true :=
    take_step (n := 2) (t := 122) (b := 24880) rfl rfl ArealUCore.ArealUK.chunk_12439 s40
  have s38 : leavesOK ctxLitU 249825000000 1 ((leaves.drop 24876).take 124) 505125000000 2 = true :=
    take_step (n := 2) (t := 124) (b := 24878) rfl rfl ArealUCore.ArealUK.chunk_12438 s39
  have s37 : leavesOK ctxLitU 249800000000 1 ((leaves.drop 24874).take 126) 505125000000 2 = true :=
    take_step (n := 2) (t := 126) (b := 24876) rfl rfl ArealUCore.ArealUK.chunk_12437 s38
  have s36 : leavesOK ctxLitU 249775000000 1 ((leaves.drop 24872).take 128) 505125000000 2 = true :=
    take_step (n := 2) (t := 128) (b := 24874) rfl rfl ArealUCore.ArealUK.chunk_12436 s37
  have s35 : leavesOK ctxLitU 249750000000 1 ((leaves.drop 24870).take 130) 505125000000 2 = true :=
    take_step (n := 2) (t := 130) (b := 24872) rfl rfl ArealUCore.ArealUK.chunk_12435 s36
  have s34 : leavesOK ctxLitU 124862500000 0 ((leaves.drop 24868).take 132) 505125000000 2 = true :=
    take_step (n := 2) (t := 132) (b := 24870) rfl rfl ArealUCore.ArealUK.chunk_12434 s35
  have s33 : leavesOK ctxLitU 124850000000 0 ((leaves.drop 24866).take 134) 505125000000 2 = true :=
    take_step (n := 2) (t := 134) (b := 24868) rfl rfl ArealUCore.ArealUK.chunk_12433 s34
  have s32 : leavesOK ctxLitU 124837500000 0 ((leaves.drop 24864).take 136) 505125000000 2 = true :=
    take_step (n := 2) (t := 136) (b := 24866) rfl rfl ArealUCore.ArealUK.chunk_12432 s33
  have s31 : leavesOK ctxLitU 124825000000 0 ((leaves.drop 24862).take 138) 505125000000 2 = true :=
    take_step (n := 2) (t := 138) (b := 24864) rfl rfl ArealUCore.ArealUK.chunk_12431 s32
  have s30 : leavesOK ctxLitU 499275000000 2 ((leaves.drop 24860).take 140) 505125000000 2 = true :=
    take_step (n := 2) (t := 140) (b := 24862) rfl rfl ArealUCore.ArealUK.chunk_12430 s31
  have s29 : leavesOK ctxLitU 249612500000 1 ((leaves.drop 24858).take 142) 505125000000 2 = true :=
    take_step (n := 2) (t := 142) (b := 24860) rfl rfl ArealUCore.ArealUK.chunk_12429 s30
  have s28 : leavesOK ctxLitU 499175000000 2 ((leaves.drop 24856).take 144) 505125000000 2 = true :=
    take_step (n := 2) (t := 144) (b := 24858) rfl rfl ArealUCore.ArealUK.chunk_12428 s29
  have s27 : leavesOK ctxLitU 499125000000 2 ((leaves.drop 24854).take 146) 505125000000 2 = true :=
    take_step (n := 2) (t := 146) (b := 24856) rfl rfl ArealUCore.ArealUK.chunk_12427 s28
  have s26 : leavesOK ctxLitU 499075000000 2 ((leaves.drop 24852).take 148) 505125000000 2 = true :=
    take_step (n := 2) (t := 148) (b := 24854) rfl rfl ArealUCore.ArealUK.chunk_12426 s27
  have s25 : leavesOK ctxLitU 499025000000 2 ((leaves.drop 24850).take 150) 505125000000 2 = true :=
    take_step (n := 2) (t := 150) (b := 24852) rfl rfl ArealUCore.ArealUK.chunk_12425 s26
  have s24 : leavesOK ctxLitU 498975000000 2 ((leaves.drop 24848).take 152) 505125000000 2 = true :=
    take_step (n := 2) (t := 152) (b := 24850) rfl rfl ArealUCore.ArealUK.chunk_12424 s25
  have s23 : leavesOK ctxLitU 498925000000 2 ((leaves.drop 24846).take 154) 505125000000 2 = true :=
    take_step (n := 2) (t := 154) (b := 24848) rfl rfl ArealUCore.ArealUK.chunk_12423 s24
  have s22 : leavesOK ctxLitU 498875000000 2 ((leaves.drop 24844).take 156) 505125000000 2 = true :=
    take_step (n := 2) (t := 156) (b := 24846) rfl rfl ArealUCore.ArealUK.chunk_12422 s23
  have s21 : leavesOK ctxLitU 498825000000 2 ((leaves.drop 24842).take 158) 505125000000 2 = true :=
    take_step (n := 2) (t := 158) (b := 24844) rfl rfl ArealUCore.ArealUK.chunk_12421 s22
  have s20 : leavesOK ctxLitU 498775000000 2 ((leaves.drop 24840).take 160) 505125000000 2 = true :=
    take_step (n := 2) (t := 160) (b := 24842) rfl rfl ArealUCore.ArealUK.chunk_12420 s21
  have s19 : leavesOK ctxLitU 498725000000 2 ((leaves.drop 24838).take 162) 505125000000 2 = true :=
    take_step (n := 2) (t := 162) (b := 24840) rfl rfl ArealUCore.ArealUK.chunk_12419 s20
  have s18 : leavesOK ctxLitU 498675000000 2 ((leaves.drop 24836).take 164) 505125000000 2 = true :=
    take_step (n := 2) (t := 164) (b := 24838) rfl rfl ArealUCore.ArealUK.chunk_12418 s19
  have s17 : leavesOK ctxLitU 498625000000 2 ((leaves.drop 24834).take 166) 505125000000 2 = true :=
    take_step (n := 2) (t := 166) (b := 24836) rfl rfl ArealUCore.ArealUK.chunk_12417 s18
  have s16 : leavesOK ctxLitU 498575000000 2 ((leaves.drop 24832).take 168) 505125000000 2 = true :=
    take_step (n := 2) (t := 168) (b := 24834) rfl rfl ArealUCore.ArealUK.chunk_12416 s17
  have s15 : leavesOK ctxLitU 498525000000 2 ((leaves.drop 24830).take 170) 505125000000 2 = true :=
    take_step (n := 2) (t := 170) (b := 24832) rfl rfl ArealUCore.ArealUK.chunk_12415 s16
  have s14 : leavesOK ctxLitU 498475000000 2 ((leaves.drop 24828).take 172) 505125000000 2 = true :=
    take_step (n := 2) (t := 172) (b := 24830) rfl rfl ArealUCore.ArealUK.chunk_12414 s15
  have s13 : leavesOK ctxLitU 498425000000 2 ((leaves.drop 24826).take 174) 505125000000 2 = true :=
    take_step (n := 2) (t := 174) (b := 24828) rfl rfl ArealUCore.ArealUK.chunk_12413 s14
  have s12 : leavesOK ctxLitU 498375000000 2 ((leaves.drop 24824).take 176) 505125000000 2 = true :=
    take_step (n := 2) (t := 176) (b := 24826) rfl rfl ArealUCore.ArealUK.chunk_12412 s13
  have s11 : leavesOK ctxLitU 498325000000 2 ((leaves.drop 24822).take 178) 505125000000 2 = true :=
    take_step (n := 2) (t := 178) (b := 24824) rfl rfl ArealUCore.ArealUK.chunk_12411 s12
  have s10 : leavesOK ctxLitU 498275000000 2 ((leaves.drop 24820).take 180) 505125000000 2 = true :=
    take_step (n := 2) (t := 180) (b := 24822) rfl rfl ArealUCore.ArealUK.chunk_12410 s11
  have s9 : leavesOK ctxLitU 498225000000 2 ((leaves.drop 24818).take 182) 505125000000 2 = true :=
    take_step (n := 2) (t := 182) (b := 24820) rfl rfl ArealUCore.ArealUK.chunk_12409 s10
  have s8 : leavesOK ctxLitU 498175000000 2 ((leaves.drop 24816).take 184) 505125000000 2 = true :=
    take_step (n := 2) (t := 184) (b := 24818) rfl rfl ArealUCore.ArealUK.chunk_12408 s9
  have s7 : leavesOK ctxLitU 498125000000 2 ((leaves.drop 24814).take 186) 505125000000 2 = true :=
    take_step (n := 2) (t := 186) (b := 24816) rfl rfl ArealUCore.ArealUK.chunk_12407 s8
  have s6 : leavesOK ctxLitU 498075000000 2 ((leaves.drop 24812).take 188) 505125000000 2 = true :=
    take_step (n := 2) (t := 188) (b := 24814) rfl rfl ArealUCore.ArealUK.chunk_12406 s7
  have s5 : leavesOK ctxLitU 498025000000 2 ((leaves.drop 24810).take 190) 505125000000 2 = true :=
    take_step (n := 2) (t := 190) (b := 24812) rfl rfl ArealUCore.ArealUK.chunk_12405 s6
  have s4 : leavesOK ctxLitU 497975000000 2 ((leaves.drop 24808).take 192) 505125000000 2 = true :=
    take_step (n := 2) (t := 192) (b := 24810) rfl rfl ArealUCore.ArealUK.chunk_12404 s5
  have s3 : leavesOK ctxLitU 497925000000 2 ((leaves.drop 24806).take 194) 505125000000 2 = true :=
    take_step (n := 2) (t := 194) (b := 24808) rfl rfl ArealUCore.ArealUK.chunk_12403 s4
  have s2 : leavesOK ctxLitU 497875000000 2 ((leaves.drop 24804).take 196) 505125000000 2 = true :=
    take_step (n := 2) (t := 196) (b := 24806) rfl rfl ArealUCore.ArealUK.chunk_12402 s3
  have s1 : leavesOK ctxLitU 497825000000 2 ((leaves.drop 24802).take 198) 505125000000 2 = true :=
    take_step (n := 2) (t := 198) (b := 24804) rfl rfl ArealUCore.ArealUK.chunk_12401 s2
  have s0 : leavesOK ctxLitU 497775000000 2 ((leaves.drop 24800).take 200) 505125000000 2 = true :=
    take_step (n := 2) (t := 200) (b := 24802) rfl rfl ArealUCore.ArealUK.chunk_12400 s1
  exact s0

end Areal.UCert

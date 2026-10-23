import ArealUK.Chunk11400
import ArealUK.Chunk11401
import ArealUK.Chunk11402
import ArealUK.Chunk11403
import ArealUK.Chunk11404
import ArealUK.Chunk11405
import ArealUK.Chunk11406
import ArealUK.Chunk11407
import ArealUK.Chunk11408
import ArealUK.Chunk11409
import ArealUK.Chunk11410
import ArealUK.Chunk11411
import ArealUK.Chunk11412
import ArealUK.Chunk11413
import ArealUK.Chunk11414
import ArealUK.Chunk11415
import ArealUK.Chunk11416
import ArealUK.Chunk11417
import ArealUK.Chunk11418
import ArealUK.Chunk11419
import ArealUK.Chunk11420
import ArealUK.Chunk11421
import ArealUK.Chunk11422
import ArealUK.Chunk11423
import ArealUK.Chunk11424
import ArealUK.Chunk11425
import ArealUK.Chunk11426
import ArealUK.Chunk11427
import ArealUK.Chunk11428
import ArealUK.Chunk11429
import ArealUK.Chunk11430
import ArealUK.Chunk11431
import ArealUK.Chunk11432
import ArealUK.Chunk11433
import ArealUK.Chunk11434
import ArealUK.Chunk11435
import ArealUK.Chunk11436
import ArealUK.Chunk11437
import ArealUK.Chunk11438
import ArealUK.Chunk11439
import ArealUK.Chunk11440
import ArealUK.Chunk11441
import ArealUK.Chunk11442
import ArealUK.Chunk11443
import ArealUK.Chunk11444
import ArealUK.Chunk11445
import ArealUK.Chunk11446
import ArealUK.Chunk11447
import ArealUK.Chunk11448
import ArealUK.Chunk11449
import ArealUK.Chunk11450
import ArealUK.Chunk11451
import ArealUK.Chunk11452
import ArealUK.Chunk11453
import ArealUK.Chunk11454
import ArealUK.Chunk11455
import ArealUK.Chunk11456
import ArealUK.Chunk11457
import ArealUK.Chunk11458
import ArealUK.Chunk11459
import ArealUK.Chunk11460
import ArealUK.Chunk11461
import ArealUK.Chunk11462
import ArealUK.Chunk11463
import ArealUK.Chunk11464
import ArealUK.Chunk11465
import ArealUK.Chunk11466
import ArealUK.Chunk11467
import ArealUK.Chunk11468
import ArealUK.Chunk11469
import ArealUK.Chunk11470
import ArealUK.Chunk11471
import ArealUK.Chunk11472
import ArealUK.Chunk11473
import ArealUK.Chunk11474
import ArealUK.Chunk11475
import ArealUK.Chunk11476
import ArealUK.Chunk11477
import ArealUK.Chunk11478
import ArealUK.Chunk11479
import ArealUK.Chunk11480
import ArealUK.Chunk11481
import ArealUK.Chunk11482
import ArealUK.Chunk11483
import ArealUK.Chunk11484
import ArealUK.Chunk11485
import ArealUK.Chunk11486
import ArealUK.Chunk11487
import ArealUK.Chunk11488
import ArealUK.Chunk11489
import ArealUK.Chunk11490
import ArealUK.Chunk11491
import ArealUK.Chunk11492
import ArealUK.Chunk11493
import ArealUK.Chunk11494
import ArealUK.Chunk11495
import ArealUK.Chunk11496
import ArealUK.Chunk11497
import ArealUK.Chunk11498
import ArealUK.Chunk11499
import Areal.UCert.LeavesKGen

/-! Group 114 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_114 : leavesOK ctxLitU 107525000000 0 ((leaves.drop 22800).take 200) 111875000000 0 = true := by
  have s99 := ArealUCore.ArealUK.chunk_11499
  have s98 : leavesOK ctxLitU 111775000000 0 ((leaves.drop 22996).take 4) 111875000000 0 = true :=
    take_step (n := 2) (t := 4) (b := 22998) rfl rfl ArealUCore.ArealUK.chunk_11498 s99
  have s97 : leavesOK ctxLitU 111725000000 0 ((leaves.drop 22994).take 6) 111875000000 0 = true :=
    take_step (n := 2) (t := 6) (b := 22996) rfl rfl ArealUCore.ArealUK.chunk_11497 s98
  have s96 : leavesOK ctxLitU 111675000000 0 ((leaves.drop 22992).take 8) 111875000000 0 = true :=
    take_step (n := 2) (t := 8) (b := 22994) rfl rfl ArealUCore.ArealUK.chunk_11496 s97
  have s95 : leavesOK ctxLitU 111625000000 0 ((leaves.drop 22990).take 10) 111875000000 0 = true :=
    take_step (n := 2) (t := 10) (b := 22992) rfl rfl ArealUCore.ArealUK.chunk_11495 s96
  have s94 : leavesOK ctxLitU 111587500000 0 ((leaves.drop 22988).take 12) 111875000000 0 = true :=
    take_step (n := 2) (t := 12) (b := 22990) rfl rfl ArealUCore.ArealUK.chunk_11494 s95
  have s93 : leavesOK ctxLitU 111568750000 0 ((leaves.drop 22986).take 14) 111875000000 0 = true :=
    take_step (n := 2) (t := 14) (b := 22988) rfl rfl ArealUCore.ArealUK.chunk_11493 s94
  have s92 : leavesOK ctxLitU 111556250000 0 ((leaves.drop 22984).take 16) 111875000000 0 = true :=
    take_step (n := 2) (t := 16) (b := 22986) rfl rfl ArealUCore.ArealUK.chunk_11492 s93
  have s91 : leavesOK ctxLitU 456874025756605 12 ((leaves.drop 22982).take 18) 111875000000 0 = true :=
    take_step (n := 2) (t := 18) (b := 22984) rfl rfl ArealUCore.ArealUK.chunk_11491 s92
  have s90 : leavesOK ctxLitU 456857600000000 12 ((leaves.drop 22980).take 20) 111875000000 0 = true :=
    take_step (n := 2) (t := 20) (b := 22982) rfl rfl ArealUCore.ArealUK.chunk_11490 s91
  have s89 : leavesOK ctxLitU 111518750000 0 ((leaves.drop 22978).take 22) 111875000000 0 = true :=
    take_step (n := 2) (t := 22) (b := 22980) rfl rfl ArealUCore.ArealUK.chunk_11489 s90
  have s88 : leavesOK ctxLitU 111506250000 0 ((leaves.drop 22976).take 24) 111875000000 0 = true :=
    take_step (n := 2) (t := 24) (b := 22978) rfl rfl ArealUCore.ArealUK.chunk_11488 s89
  have s87 : leavesOK ctxLitU 111487500000 0 ((leaves.drop 22974).take 26) 111875000000 0 = true :=
    take_step (n := 2) (t := 26) (b := 22976) rfl rfl ArealUCore.ArealUK.chunk_11487 s88
  have s86 : leavesOK ctxLitU 111450000000 0 ((leaves.drop 22972).take 28) 111875000000 0 = true :=
    take_step (n := 2) (t := 28) (b := 22974) rfl rfl ArealUCore.ArealUK.chunk_11486 s87
  have s85 : leavesOK ctxLitU 111400000000 0 ((leaves.drop 22970).take 30) 111875000000 0 = true :=
    take_step (n := 2) (t := 30) (b := 22972) rfl rfl ArealUCore.ArealUK.chunk_11485 s86
  have s84 : leavesOK ctxLitU 111350000000 0 ((leaves.drop 22968).take 32) 111875000000 0 = true :=
    take_step (n := 2) (t := 32) (b := 22970) rfl rfl ArealUCore.ArealUK.chunk_11484 s85
  have s83 : leavesOK ctxLitU 111300000000 0 ((leaves.drop 22966).take 34) 111875000000 0 = true :=
    take_step (n := 2) (t := 34) (b := 22968) rfl rfl ArealUCore.ArealUK.chunk_11483 s84
  have s82 : leavesOK ctxLitU 111250000000 0 ((leaves.drop 22964).take 36) 111875000000 0 = true :=
    take_step (n := 2) (t := 36) (b := 22966) rfl rfl ArealUCore.ArealUK.chunk_11482 s83
  have s81 : leavesOK ctxLitU 111200000000 0 ((leaves.drop 22962).take 38) 111875000000 0 = true :=
    take_step (n := 2) (t := 38) (b := 22964) rfl rfl ArealUCore.ArealUK.chunk_11481 s82
  have s80 : leavesOK ctxLitU 111150000000 0 ((leaves.drop 22960).take 40) 111875000000 0 = true :=
    take_step (n := 2) (t := 40) (b := 22962) rfl rfl ArealUCore.ArealUK.chunk_11480 s81
  have s79 : leavesOK ctxLitU 111100000000 0 ((leaves.drop 22958).take 42) 111875000000 0 = true :=
    take_step (n := 2) (t := 42) (b := 22960) rfl rfl ArealUCore.ArealUK.chunk_11479 s80
  have s78 : leavesOK ctxLitU 111050000000 0 ((leaves.drop 22956).take 44) 111875000000 0 = true :=
    take_step (n := 2) (t := 44) (b := 22958) rfl rfl ArealUCore.ArealUK.chunk_11478 s79
  have s77 : leavesOK ctxLitU 111000000000 0 ((leaves.drop 22954).take 46) 111875000000 0 = true :=
    take_step (n := 2) (t := 46) (b := 22956) rfl rfl ArealUCore.ArealUK.chunk_11477 s78
  have s76 : leavesOK ctxLitU 110950000000 0 ((leaves.drop 22952).take 48) 111875000000 0 = true :=
    take_step (n := 2) (t := 48) (b := 22954) rfl rfl ArealUCore.ArealUK.chunk_11476 s77
  have s75 : leavesOK ctxLitU 110900000000 0 ((leaves.drop 22950).take 50) 111875000000 0 = true :=
    take_step (n := 2) (t := 50) (b := 22952) rfl rfl ArealUCore.ArealUK.chunk_11475 s76
  have s74 : leavesOK ctxLitU 110850000000 0 ((leaves.drop 22948).take 52) 111875000000 0 = true :=
    take_step (n := 2) (t := 52) (b := 22950) rfl rfl ArealUCore.ArealUK.chunk_11474 s75
  have s73 : leavesOK ctxLitU 110800000000 0 ((leaves.drop 22946).take 54) 111875000000 0 = true :=
    take_step (n := 2) (t := 54) (b := 22948) rfl rfl ArealUCore.ArealUK.chunk_11473 s74
  have s72 : leavesOK ctxLitU 110750000000 0 ((leaves.drop 22944).take 56) 111875000000 0 = true :=
    take_step (n := 2) (t := 56) (b := 22946) rfl rfl ArealUCore.ArealUK.chunk_11472 s73
  have s71 : leavesOK ctxLitU 110700000000 0 ((leaves.drop 22942).take 58) 111875000000 0 = true :=
    take_step (n := 2) (t := 58) (b := 22944) rfl rfl ArealUCore.ArealUK.chunk_11471 s72
  have s70 : leavesOK ctxLitU 110650000000 0 ((leaves.drop 22940).take 60) 111875000000 0 = true :=
    take_step (n := 2) (t := 60) (b := 22942) rfl rfl ArealUCore.ArealUK.chunk_11470 s71
  have s69 : leavesOK ctxLitU 110600000000 0 ((leaves.drop 22938).take 62) 111875000000 0 = true :=
    take_step (n := 2) (t := 62) (b := 22940) rfl rfl ArealUCore.ArealUK.chunk_11469 s70
  have s68 : leavesOK ctxLitU 110550000000 0 ((leaves.drop 22936).take 64) 111875000000 0 = true :=
    take_step (n := 2) (t := 64) (b := 22938) rfl rfl ArealUCore.ArealUK.chunk_11468 s69
  have s67 : leavesOK ctxLitU 110500000000 0 ((leaves.drop 22934).take 66) 111875000000 0 = true :=
    take_step (n := 2) (t := 66) (b := 22936) rfl rfl ArealUCore.ArealUK.chunk_11467 s68
  have s66 : leavesOK ctxLitU 110450000000 0 ((leaves.drop 22932).take 68) 111875000000 0 = true :=
    take_step (n := 2) (t := 68) (b := 22934) rfl rfl ArealUCore.ArealUK.chunk_11466 s67
  have s65 : leavesOK ctxLitU 110400000000 0 ((leaves.drop 22930).take 70) 111875000000 0 = true :=
    take_step (n := 2) (t := 70) (b := 22932) rfl rfl ArealUCore.ArealUK.chunk_11465 s66
  have s64 : leavesOK ctxLitU 110350000000 0 ((leaves.drop 22928).take 72) 111875000000 0 = true :=
    take_step (n := 2) (t := 72) (b := 22930) rfl rfl ArealUCore.ArealUK.chunk_11464 s65
  have s63 : leavesOK ctxLitU 110300000000 0 ((leaves.drop 22926).take 74) 111875000000 0 = true :=
    take_step (n := 2) (t := 74) (b := 22928) rfl rfl ArealUCore.ArealUK.chunk_11463 s64
  have s62 : leavesOK ctxLitU 110250000000 0 ((leaves.drop 22924).take 76) 111875000000 0 = true :=
    take_step (n := 2) (t := 76) (b := 22926) rfl rfl ArealUCore.ArealUK.chunk_11462 s63
  have s61 : leavesOK ctxLitU 110200000000 0 ((leaves.drop 22922).take 78) 111875000000 0 = true :=
    take_step (n := 2) (t := 78) (b := 22924) rfl rfl ArealUCore.ArealUK.chunk_11461 s62
  have s60 : leavesOK ctxLitU 110150000000 0 ((leaves.drop 22920).take 80) 111875000000 0 = true :=
    take_step (n := 2) (t := 80) (b := 22922) rfl rfl ArealUCore.ArealUK.chunk_11460 s61
  have s59 : leavesOK ctxLitU 110100000000 0 ((leaves.drop 22918).take 82) 111875000000 0 = true :=
    take_step (n := 2) (t := 82) (b := 22920) rfl rfl ArealUCore.ArealUK.chunk_11459 s60
  have s58 : leavesOK ctxLitU 110050000000 0 ((leaves.drop 22916).take 84) 111875000000 0 = true :=
    take_step (n := 2) (t := 84) (b := 22918) rfl rfl ArealUCore.ArealUK.chunk_11458 s59
  have s57 : leavesOK ctxLitU 110000000000 0 ((leaves.drop 22914).take 86) 111875000000 0 = true :=
    take_step (n := 2) (t := 86) (b := 22916) rfl rfl ArealUCore.ArealUK.chunk_11457 s58
  have s56 : leavesOK ctxLitU 109950000000 0 ((leaves.drop 22912).take 88) 111875000000 0 = true :=
    take_step (n := 2) (t := 88) (b := 22914) rfl rfl ArealUCore.ArealUK.chunk_11456 s57
  have s55 : leavesOK ctxLitU 109900000000 0 ((leaves.drop 22910).take 90) 111875000000 0 = true :=
    take_step (n := 2) (t := 90) (b := 22912) rfl rfl ArealUCore.ArealUK.chunk_11455 s56
  have s54 : leavesOK ctxLitU 109850000000 0 ((leaves.drop 22908).take 92) 111875000000 0 = true :=
    take_step (n := 2) (t := 92) (b := 22910) rfl rfl ArealUCore.ArealUK.chunk_11454 s55
  have s53 : leavesOK ctxLitU 109800000000 0 ((leaves.drop 22906).take 94) 111875000000 0 = true :=
    take_step (n := 2) (t := 94) (b := 22908) rfl rfl ArealUCore.ArealUK.chunk_11453 s54
  have s52 : leavesOK ctxLitU 109750000000 0 ((leaves.drop 22904).take 96) 111875000000 0 = true :=
    take_step (n := 2) (t := 96) (b := 22906) rfl rfl ArealUCore.ArealUK.chunk_11452 s53
  have s51 : leavesOK ctxLitU 109700000000 0 ((leaves.drop 22902).take 98) 111875000000 0 = true :=
    take_step (n := 2) (t := 98) (b := 22904) rfl rfl ArealUCore.ArealUK.chunk_11451 s52
  have s50 : leavesOK ctxLitU 109650000000 0 ((leaves.drop 22900).take 100) 111875000000 0 = true :=
    take_step (n := 2) (t := 100) (b := 22902) rfl rfl ArealUCore.ArealUK.chunk_11450 s51
  have s49 : leavesOK ctxLitU 109600000000 0 ((leaves.drop 22898).take 102) 111875000000 0 = true :=
    take_step (n := 2) (t := 102) (b := 22900) rfl rfl ArealUCore.ArealUK.chunk_11449 s50
  have s48 : leavesOK ctxLitU 109550000000 0 ((leaves.drop 22896).take 104) 111875000000 0 = true :=
    take_step (n := 2) (t := 104) (b := 22898) rfl rfl ArealUCore.ArealUK.chunk_11448 s49
  have s47 : leavesOK ctxLitU 109500000000 0 ((leaves.drop 22894).take 106) 111875000000 0 = true :=
    take_step (n := 2) (t := 106) (b := 22896) rfl rfl ArealUCore.ArealUK.chunk_11447 s48
  have s46 : leavesOK ctxLitU 109450000000 0 ((leaves.drop 22892).take 108) 111875000000 0 = true :=
    take_step (n := 2) (t := 108) (b := 22894) rfl rfl ArealUCore.ArealUK.chunk_11446 s47
  have s45 : leavesOK ctxLitU 109400000000 0 ((leaves.drop 22890).take 110) 111875000000 0 = true :=
    take_step (n := 2) (t := 110) (b := 22892) rfl rfl ArealUCore.ArealUK.chunk_11445 s46
  have s44 : leavesOK ctxLitU 109350000000 0 ((leaves.drop 22888).take 112) 111875000000 0 = true :=
    take_step (n := 2) (t := 112) (b := 22890) rfl rfl ArealUCore.ArealUK.chunk_11444 s45
  have s43 : leavesOK ctxLitU 109300000000 0 ((leaves.drop 22886).take 114) 111875000000 0 = true :=
    take_step (n := 2) (t := 114) (b := 22888) rfl rfl ArealUCore.ArealUK.chunk_11443 s44
  have s42 : leavesOK ctxLitU 109250000000 0 ((leaves.drop 22884).take 116) 111875000000 0 = true :=
    take_step (n := 2) (t := 116) (b := 22886) rfl rfl ArealUCore.ArealUK.chunk_11442 s43
  have s41 : leavesOK ctxLitU 109200000000 0 ((leaves.drop 22882).take 118) 111875000000 0 = true :=
    take_step (n := 2) (t := 118) (b := 22884) rfl rfl ArealUCore.ArealUK.chunk_11441 s42
  have s40 : leavesOK ctxLitU 109150000000 0 ((leaves.drop 22880).take 120) 111875000000 0 = true :=
    take_step (n := 2) (t := 120) (b := 22882) rfl rfl ArealUCore.ArealUK.chunk_11440 s41
  have s39 : leavesOK ctxLitU 109112500000 0 ((leaves.drop 22878).take 122) 111875000000 0 = true :=
    take_step (n := 2) (t := 122) (b := 22880) rfl rfl ArealUCore.ArealUK.chunk_11439 s40
  have s38 : leavesOK ctxLitU 109093750000 0 ((leaves.drop 22876).take 124) 111875000000 0 = true :=
    take_step (n := 2) (t := 124) (b := 22878) rfl rfl ArealUCore.ArealUK.chunk_11438 s39
  have s37 : leavesOK ctxLitU 109081250000 0 ((leaves.drop 22874).take 126) 111875000000 0 = true :=
    take_step (n := 2) (t := 126) (b := 22876) rfl rfl ArealUCore.ArealUK.chunk_11437 s38
  have s36 : leavesOK ctxLitU 109062500000 0 ((leaves.drop 22872).take 128) 111875000000 0 = true :=
    take_step (n := 2) (t := 128) (b := 22874) rfl rfl ArealUCore.ArealUK.chunk_11436 s37
  have s35 : leavesOK ctxLitU 446593912364001 12 ((leaves.drop 22870).take 130) 111875000000 0 = true :=
    take_step (n := 2) (t := 130) (b := 22872) rfl rfl ArealUCore.ArealUK.chunk_11435 s36
  have s34 : leavesOK ctxLitU 446566400000000 12 ((leaves.drop 22868).take 132) 111875000000 0 = true :=
    take_step (n := 2) (t := 132) (b := 22870) rfl rfl ArealUCore.ArealUK.chunk_11434 s35
  have s33 : leavesOK ctxLitU 109000000000 0 ((leaves.drop 22866).take 134) 111875000000 0 = true :=
    take_step (n := 2) (t := 134) (b := 22868) rfl rfl ArealUCore.ArealUK.chunk_11433 s34
  have s32 : leavesOK ctxLitU 108987500000 0 ((leaves.drop 22864).take 136) 111875000000 0 = true :=
    take_step (n := 2) (t := 136) (b := 22866) rfl rfl ArealUCore.ArealUK.chunk_11432 s33
  have s31 : leavesOK ctxLitU 108975000000 0 ((leaves.drop 22862).take 138) 111875000000 0 = true :=
    take_step (n := 2) (t := 138) (b := 22864) rfl rfl ArealUCore.ArealUK.chunk_11431 s32
  have s30 : leavesOK ctxLitU 108962500000 0 ((leaves.drop 22860).take 140) 111875000000 0 = true :=
    take_step (n := 2) (t := 140) (b := 22862) rfl rfl ArealUCore.ArealUK.chunk_11430 s31
  have s29 : leavesOK ctxLitU 108950000000 0 ((leaves.drop 22858).take 142) 111875000000 0 = true :=
    take_step (n := 2) (t := 142) (b := 22860) rfl rfl ArealUCore.ArealUK.chunk_11429 s30
  have s28 : leavesOK ctxLitU 108925000000 0 ((leaves.drop 22856).take 144) 111875000000 0 = true :=
    take_step (n := 2) (t := 144) (b := 22858) rfl rfl ArealUCore.ArealUK.chunk_11428 s29
  have s27 : leavesOK ctxLitU 108875000000 0 ((leaves.drop 22854).take 146) 111875000000 0 = true :=
    take_step (n := 2) (t := 146) (b := 22856) rfl rfl ArealUCore.ArealUK.chunk_11427 s28
  have s26 : leavesOK ctxLitU 108825000000 0 ((leaves.drop 22852).take 148) 111875000000 0 = true :=
    take_step (n := 2) (t := 148) (b := 22854) rfl rfl ArealUCore.ArealUK.chunk_11426 s27
  have s25 : leavesOK ctxLitU 108775000000 0 ((leaves.drop 22850).take 150) 111875000000 0 = true :=
    take_step (n := 2) (t := 150) (b := 22852) rfl rfl ArealUCore.ArealUK.chunk_11425 s26
  have s24 : leavesOK ctxLitU 108725000000 0 ((leaves.drop 22848).take 152) 111875000000 0 = true :=
    take_step (n := 2) (t := 152) (b := 22850) rfl rfl ArealUCore.ArealUK.chunk_11424 s25
  have s23 : leavesOK ctxLitU 108675000000 0 ((leaves.drop 22846).take 154) 111875000000 0 = true :=
    take_step (n := 2) (t := 154) (b := 22848) rfl rfl ArealUCore.ArealUK.chunk_11423 s24
  have s22 : leavesOK ctxLitU 108625000000 0 ((leaves.drop 22844).take 156) 111875000000 0 = true :=
    take_step (n := 2) (t := 156) (b := 22846) rfl rfl ArealUCore.ArealUK.chunk_11422 s23
  have s21 : leavesOK ctxLitU 108575000000 0 ((leaves.drop 22842).take 158) 111875000000 0 = true :=
    take_step (n := 2) (t := 158) (b := 22844) rfl rfl ArealUCore.ArealUK.chunk_11421 s22
  have s20 : leavesOK ctxLitU 108525000000 0 ((leaves.drop 22840).take 160) 111875000000 0 = true :=
    take_step (n := 2) (t := 160) (b := 22842) rfl rfl ArealUCore.ArealUK.chunk_11420 s21
  have s19 : leavesOK ctxLitU 108475000000 0 ((leaves.drop 22838).take 162) 111875000000 0 = true :=
    take_step (n := 2) (t := 162) (b := 22840) rfl rfl ArealUCore.ArealUK.chunk_11419 s20
  have s18 : leavesOK ctxLitU 108425000000 0 ((leaves.drop 22836).take 164) 111875000000 0 = true :=
    take_step (n := 2) (t := 164) (b := 22838) rfl rfl ArealUCore.ArealUK.chunk_11418 s19
  have s17 : leavesOK ctxLitU 108375000000 0 ((leaves.drop 22834).take 166) 111875000000 0 = true :=
    take_step (n := 2) (t := 166) (b := 22836) rfl rfl ArealUCore.ArealUK.chunk_11417 s18
  have s16 : leavesOK ctxLitU 108325000000 0 ((leaves.drop 22832).take 168) 111875000000 0 = true :=
    take_step (n := 2) (t := 168) (b := 22834) rfl rfl ArealUCore.ArealUK.chunk_11416 s17
  have s15 : leavesOK ctxLitU 108275000000 0 ((leaves.drop 22830).take 170) 111875000000 0 = true :=
    take_step (n := 2) (t := 170) (b := 22832) rfl rfl ArealUCore.ArealUK.chunk_11415 s16
  have s14 : leavesOK ctxLitU 108225000000 0 ((leaves.drop 22828).take 172) 111875000000 0 = true :=
    take_step (n := 2) (t := 172) (b := 22830) rfl rfl ArealUCore.ArealUK.chunk_11414 s15
  have s13 : leavesOK ctxLitU 108175000000 0 ((leaves.drop 22826).take 174) 111875000000 0 = true :=
    take_step (n := 2) (t := 174) (b := 22828) rfl rfl ArealUCore.ArealUK.chunk_11413 s14
  have s12 : leavesOK ctxLitU 108125000000 0 ((leaves.drop 22824).take 176) 111875000000 0 = true :=
    take_step (n := 2) (t := 176) (b := 22826) rfl rfl ArealUCore.ArealUK.chunk_11412 s13
  have s11 : leavesOK ctxLitU 108075000000 0 ((leaves.drop 22822).take 178) 111875000000 0 = true :=
    take_step (n := 2) (t := 178) (b := 22824) rfl rfl ArealUCore.ArealUK.chunk_11411 s12
  have s10 : leavesOK ctxLitU 108025000000 0 ((leaves.drop 22820).take 180) 111875000000 0 = true :=
    take_step (n := 2) (t := 180) (b := 22822) rfl rfl ArealUCore.ArealUK.chunk_11410 s11
  have s9 : leavesOK ctxLitU 107975000000 0 ((leaves.drop 22818).take 182) 111875000000 0 = true :=
    take_step (n := 2) (t := 182) (b := 22820) rfl rfl ArealUCore.ArealUK.chunk_11409 s10
  have s8 : leavesOK ctxLitU 107925000000 0 ((leaves.drop 22816).take 184) 111875000000 0 = true :=
    take_step (n := 2) (t := 184) (b := 22818) rfl rfl ArealUCore.ArealUK.chunk_11408 s9
  have s7 : leavesOK ctxLitU 107875000000 0 ((leaves.drop 22814).take 186) 111875000000 0 = true :=
    take_step (n := 2) (t := 186) (b := 22816) rfl rfl ArealUCore.ArealUK.chunk_11407 s8
  have s6 : leavesOK ctxLitU 107825000000 0 ((leaves.drop 22812).take 188) 111875000000 0 = true :=
    take_step (n := 2) (t := 188) (b := 22814) rfl rfl ArealUCore.ArealUK.chunk_11406 s7
  have s5 : leavesOK ctxLitU 107775000000 0 ((leaves.drop 22810).take 190) 111875000000 0 = true :=
    take_step (n := 2) (t := 190) (b := 22812) rfl rfl ArealUCore.ArealUK.chunk_11405 s6
  have s4 : leavesOK ctxLitU 107725000000 0 ((leaves.drop 22808).take 192) 111875000000 0 = true :=
    take_step (n := 2) (t := 192) (b := 22810) rfl rfl ArealUCore.ArealUK.chunk_11404 s5
  have s3 : leavesOK ctxLitU 107675000000 0 ((leaves.drop 22806).take 194) 111875000000 0 = true :=
    take_step (n := 2) (t := 194) (b := 22808) rfl rfl ArealUCore.ArealUK.chunk_11403 s4
  have s2 : leavesOK ctxLitU 107625000000 0 ((leaves.drop 22804).take 196) 111875000000 0 = true :=
    take_step (n := 2) (t := 196) (b := 22806) rfl rfl ArealUCore.ArealUK.chunk_11402 s3
  have s1 : leavesOK ctxLitU 107575000000 0 ((leaves.drop 22802).take 198) 111875000000 0 = true :=
    take_step (n := 2) (t := 198) (b := 22804) rfl rfl ArealUCore.ArealUK.chunk_11401 s2
  have s0 : leavesOK ctxLitU 107525000000 0 ((leaves.drop 22800).take 200) 111875000000 0 = true :=
    take_step (n := 2) (t := 200) (b := 22802) rfl rfl ArealUCore.ArealUK.chunk_11400 s1
  exact s0

end Areal.UCert

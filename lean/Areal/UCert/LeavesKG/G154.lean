import ArealUK.Chunk15400
import ArealUK.Chunk15401
import ArealUK.Chunk15402
import ArealUK.Chunk15403
import ArealUK.Chunk15404
import ArealUK.Chunk15405
import ArealUK.Chunk15406
import ArealUK.Chunk15407
import ArealUK.Chunk15408
import ArealUK.Chunk15409
import ArealUK.Chunk15410
import ArealUK.Chunk15411
import ArealUK.Chunk15412
import ArealUK.Chunk15413
import ArealUK.Chunk15414
import ArealUK.Chunk15415
import ArealUK.Chunk15416
import ArealUK.Chunk15417
import ArealUK.Chunk15418
import ArealUK.Chunk15419
import ArealUK.Chunk15420
import ArealUK.Chunk15421
import ArealUK.Chunk15422
import ArealUK.Chunk15423
import ArealUK.Chunk15424
import ArealUK.Chunk15425
import ArealUK.Chunk15426
import ArealUK.Chunk15427
import ArealUK.Chunk15428
import ArealUK.Chunk15429
import ArealUK.Chunk15430
import ArealUK.Chunk15431
import ArealUK.Chunk15432
import ArealUK.Chunk15433
import ArealUK.Chunk15434
import ArealUK.Chunk15435
import ArealUK.Chunk15436
import ArealUK.Chunk15437
import ArealUK.Chunk15438
import ArealUK.Chunk15439
import ArealUK.Chunk15440
import ArealUK.Chunk15441
import ArealUK.Chunk15442
import ArealUK.Chunk15443
import ArealUK.Chunk15444
import ArealUK.Chunk15445
import ArealUK.Chunk15446
import ArealUK.Chunk15447
import ArealUK.Chunk15448
import ArealUK.Chunk15449
import ArealUK.Chunk15450
import ArealUK.Chunk15451
import ArealUK.Chunk15452
import ArealUK.Chunk15453
import ArealUK.Chunk15454
import ArealUK.Chunk15455
import ArealUK.Chunk15456
import ArealUK.Chunk15457
import ArealUK.Chunk15458
import ArealUK.Chunk15459
import ArealUK.Chunk15460
import ArealUK.Chunk15461
import ArealUK.Chunk15462
import ArealUK.Chunk15463
import ArealUK.Chunk15464
import ArealUK.Chunk15465
import ArealUK.Chunk15466
import ArealUK.Chunk15467
import ArealUK.Chunk15468
import ArealUK.Chunk15469
import ArealUK.Chunk15470
import ArealUK.Chunk15471
import ArealUK.Chunk15472
import ArealUK.Chunk15473
import ArealUK.Chunk15474
import ArealUK.Chunk15475
import ArealUK.Chunk15476
import ArealUK.Chunk15477
import ArealUK.Chunk15478
import ArealUK.Chunk15479
import ArealUK.Chunk15480
import ArealUK.Chunk15481
import ArealUK.Chunk15482
import ArealUK.Chunk15483
import ArealUK.Chunk15484
import ArealUK.Chunk15485
import ArealUK.Chunk15486
import ArealUK.Chunk15487
import ArealUK.Chunk15488
import ArealUK.Chunk15489
import ArealUK.Chunk15490
import ArealUK.Chunk15491
import ArealUK.Chunk15492
import ArealUK.Chunk15493
import ArealUK.Chunk15494
import ArealUK.Chunk15495
import ArealUK.Chunk15496
import ArealUK.Chunk15497
import ArealUK.Chunk15498
import ArealUK.Chunk15499
import Areal.UCert.LeavesKGen

/-! Group 154 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_154 : leavesOK ctxLitU 324387500000 1 ((leaves.drop 30800).take 200) 163650000000 0 = true := by
  have s99 := ArealUCore.ArealUK.chunk_15499
  have s98 : leavesOK ctxLitU 163625000000 0 ((leaves.drop 30996).take 4) 163650000000 0 = true :=
    take_step (n := 2) (t := 4) (b := 30998) rfl rfl ArealUCore.ArealUK.chunk_15498 s99
  have s97 : leavesOK ctxLitU 163612500000 0 ((leaves.drop 30994).take 6) 163650000000 0 = true :=
    take_step (n := 2) (t := 6) (b := 30996) rfl rfl ArealUCore.ArealUK.chunk_15497 s98
  have s96 : leavesOK ctxLitU 163600000000 0 ((leaves.drop 30992).take 8) 163650000000 0 = true :=
    take_step (n := 2) (t := 8) (b := 30994) rfl rfl ArealUCore.ArealUK.chunk_15496 s97
  have s95 : leavesOK ctxLitU 163587500000 0 ((leaves.drop 30990).take 10) 163650000000 0 = true :=
    take_step (n := 2) (t := 10) (b := 30992) rfl rfl ArealUCore.ArealUK.chunk_15495 s96
  have s94 : leavesOK ctxLitU 163575000000 0 ((leaves.drop 30988).take 12) 163650000000 0 = true :=
    take_step (n := 2) (t := 12) (b := 30990) rfl rfl ArealUCore.ArealUK.chunk_15494 s95
  have s93 : leavesOK ctxLitU 163562500000 0 ((leaves.drop 30986).take 14) 163650000000 0 = true :=
    take_step (n := 2) (t := 14) (b := 30988) rfl rfl ArealUCore.ArealUK.chunk_15493 s94
  have s92 : leavesOK ctxLitU 163550000000 0 ((leaves.drop 30984).take 16) 163650000000 0 = true :=
    take_step (n := 2) (t := 16) (b := 30986) rfl rfl ArealUCore.ArealUK.chunk_15492 s93
  have s91 : leavesOK ctxLitU 163537500000 0 ((leaves.drop 30982).take 18) 163650000000 0 = true :=
    take_step (n := 2) (t := 18) (b := 30984) rfl rfl ArealUCore.ArealUK.chunk_15491 s92
  have s90 : leavesOK ctxLitU 163525000000 0 ((leaves.drop 30980).take 20) 163650000000 0 = true :=
    take_step (n := 2) (t := 20) (b := 30982) rfl rfl ArealUCore.ArealUK.chunk_15490 s91
  have s89 : leavesOK ctxLitU 327025000000 1 ((leaves.drop 30978).take 22) 163650000000 0 = true :=
    take_step (n := 2) (t := 22) (b := 30980) rfl rfl ArealUCore.ArealUK.chunk_15489 s90
  have s88 : leavesOK ctxLitU 327000000000 1 ((leaves.drop 30976).take 24) 163650000000 0 = true :=
    take_step (n := 2) (t := 24) (b := 30978) rfl rfl ArealUCore.ArealUK.chunk_15488 s89
  have s87 : leavesOK ctxLitU 326950000000 1 ((leaves.drop 30974).take 26) 163650000000 0 = true :=
    take_step (n := 2) (t := 26) (b := 30976) rfl rfl ArealUCore.ArealUK.chunk_15487 s88
  have s86 : leavesOK ctxLitU 163450000000 0 ((leaves.drop 30972).take 28) 163650000000 0 = true :=
    take_step (n := 2) (t := 28) (b := 30974) rfl rfl ArealUCore.ArealUK.chunk_15486 s87
  have s85 : leavesOK ctxLitU 163437500000 0 ((leaves.drop 30970).take 30) 163650000000 0 = true :=
    take_step (n := 2) (t := 30) (b := 30972) rfl rfl ArealUCore.ArealUK.chunk_15485 s86
  have s84 : leavesOK ctxLitU 163425000000 0 ((leaves.drop 30968).take 32) 163650000000 0 = true :=
    take_step (n := 2) (t := 32) (b := 30970) rfl rfl ArealUCore.ArealUK.chunk_15484 s85
  have s83 : leavesOK ctxLitU 163412500000 0 ((leaves.drop 30966).take 34) 163650000000 0 = true :=
    take_step (n := 2) (t := 34) (b := 30968) rfl rfl ArealUCore.ArealUK.chunk_15483 s84
  have s82 : leavesOK ctxLitU 163400000000 0 ((leaves.drop 30964).take 36) 163650000000 0 = true :=
    take_step (n := 2) (t := 36) (b := 30966) rfl rfl ArealUCore.ArealUK.chunk_15482 s83
  have s81 : leavesOK ctxLitU 163387500000 0 ((leaves.drop 30962).take 38) 163650000000 0 = true :=
    take_step (n := 2) (t := 38) (b := 30964) rfl rfl ArealUCore.ArealUK.chunk_15481 s82
  have s80 : leavesOK ctxLitU 163375000000 0 ((leaves.drop 30960).take 40) 163650000000 0 = true :=
    take_step (n := 2) (t := 40) (b := 30962) rfl rfl ArealUCore.ArealUK.chunk_15480 s81
  have s79 : leavesOK ctxLitU 163350000000 0 ((leaves.drop 30958).take 42) 163650000000 0 = true :=
    take_step (n := 2) (t := 42) (b := 30960) rfl rfl ArealUCore.ArealUK.chunk_15479 s80
  have s78 : leavesOK ctxLitU 163337500000 0 ((leaves.drop 30956).take 44) 163650000000 0 = true :=
    take_step (n := 2) (t := 44) (b := 30958) rfl rfl ArealUCore.ArealUK.chunk_15478 s79
  have s77 : leavesOK ctxLitU 163325000000 0 ((leaves.drop 30954).take 46) 163650000000 0 = true :=
    take_step (n := 2) (t := 46) (b := 30956) rfl rfl ArealUCore.ArealUK.chunk_15477 s78
  have s76 : leavesOK ctxLitU 163312500000 0 ((leaves.drop 30952).take 48) 163650000000 0 = true :=
    take_step (n := 2) (t := 48) (b := 30954) rfl rfl ArealUCore.ArealUK.chunk_15476 s77
  have s75 : leavesOK ctxLitU 163300000000 0 ((leaves.drop 30950).take 50) 163650000000 0 = true :=
    take_step (n := 2) (t := 50) (b := 30952) rfl rfl ArealUCore.ArealUK.chunk_15475 s76
  have s74 : leavesOK ctxLitU 163275000000 0 ((leaves.drop 30948).take 52) 163650000000 0 = true :=
    take_step (n := 2) (t := 52) (b := 30950) rfl rfl ArealUCore.ArealUK.chunk_15474 s75
  have s73 : leavesOK ctxLitU 163262500000 0 ((leaves.drop 30946).take 54) 163650000000 0 = true :=
    take_step (n := 2) (t := 54) (b := 30948) rfl rfl ArealUCore.ArealUK.chunk_15473 s74
  have s72 : leavesOK ctxLitU 163250000000 0 ((leaves.drop 30944).take 56) 163650000000 0 = true :=
    take_step (n := 2) (t := 56) (b := 30946) rfl rfl ArealUCore.ArealUK.chunk_15472 s73
  have s71 : leavesOK ctxLitU 163237500000 0 ((leaves.drop 30942).take 58) 163650000000 0 = true :=
    take_step (n := 2) (t := 58) (b := 30944) rfl rfl ArealUCore.ArealUK.chunk_15471 s72
  have s70 : leavesOK ctxLitU 163225000000 0 ((leaves.drop 30940).take 60) 163650000000 0 = true :=
    take_step (n := 2) (t := 60) (b := 30942) rfl rfl ArealUCore.ArealUK.chunk_15470 s71
  have s69 : leavesOK ctxLitU 163212500000 0 ((leaves.drop 30938).take 62) 163650000000 0 = true :=
    take_step (n := 2) (t := 62) (b := 30940) rfl rfl ArealUCore.ArealUK.chunk_15469 s70
  have s68 : leavesOK ctxLitU 163200000000 0 ((leaves.drop 30936).take 64) 163650000000 0 = true :=
    take_step (n := 2) (t := 64) (b := 30938) rfl rfl ArealUCore.ArealUK.chunk_15468 s69
  have s67 : leavesOK ctxLitU 163187500000 0 ((leaves.drop 30934).take 66) 163650000000 0 = true :=
    take_step (n := 2) (t := 66) (b := 30936) rfl rfl ArealUCore.ArealUK.chunk_15467 s68
  have s66 : leavesOK ctxLitU 163175000000 0 ((leaves.drop 30932).take 68) 163650000000 0 = true :=
    take_step (n := 2) (t := 68) (b := 30934) rfl rfl ArealUCore.ArealUK.chunk_15466 s67
  have s65 : leavesOK ctxLitU 163162500000 0 ((leaves.drop 30930).take 70) 163650000000 0 = true :=
    take_step (n := 2) (t := 70) (b := 30932) rfl rfl ArealUCore.ArealUK.chunk_15465 s66
  have s64 : leavesOK ctxLitU 163150000000 0 ((leaves.drop 30928).take 72) 163650000000 0 = true :=
    take_step (n := 2) (t := 72) (b := 30930) rfl rfl ArealUCore.ArealUK.chunk_15464 s65
  have s63 : leavesOK ctxLitU 163137500000 0 ((leaves.drop 30926).take 74) 163650000000 0 = true :=
    take_step (n := 2) (t := 74) (b := 30928) rfl rfl ArealUCore.ArealUK.chunk_15463 s64
  have s62 : leavesOK ctxLitU 163125000000 0 ((leaves.drop 30924).take 76) 163650000000 0 = true :=
    take_step (n := 2) (t := 76) (b := 30926) rfl rfl ArealUCore.ArealUK.chunk_15462 s63
  have s61 : leavesOK ctxLitU 163112500000 0 ((leaves.drop 30922).take 78) 163650000000 0 = true :=
    take_step (n := 2) (t := 78) (b := 30924) rfl rfl ArealUCore.ArealUK.chunk_15461 s62
  have s60 : leavesOK ctxLitU 163100000000 0 ((leaves.drop 30920).take 80) 163650000000 0 = true :=
    take_step (n := 2) (t := 80) (b := 30922) rfl rfl ArealUCore.ArealUK.chunk_15460 s61
  have s59 : leavesOK ctxLitU 326175000000 1 ((leaves.drop 30918).take 82) 163650000000 0 = true :=
    take_step (n := 2) (t := 82) (b := 30920) rfl rfl ArealUCore.ArealUK.chunk_15459 s60
  have s58 : leavesOK ctxLitU 163068750000 0 ((leaves.drop 30916).take 84) 163650000000 0 = true :=
    take_step (n := 2) (t := 84) (b := 30918) rfl rfl ArealUCore.ArealUK.chunk_15458 s59
  have s57 : leavesOK ctxLitU 163056250000 0 ((leaves.drop 30914).take 86) 163650000000 0 = true :=
    take_step (n := 2) (t := 86) (b := 30916) rfl rfl ArealUCore.ArealUK.chunk_15457 s58
  have s56 : leavesOK ctxLitU 163043750000 0 ((leaves.drop 30912).take 88) 163650000000 0 = true :=
    take_step (n := 2) (t := 88) (b := 30914) rfl rfl ArealUCore.ArealUK.chunk_15456 s57
  have s55 : leavesOK ctxLitU 163031250000 0 ((leaves.drop 30910).take 90) 163650000000 0 = true :=
    take_step (n := 2) (t := 90) (b := 30912) rfl rfl ArealUCore.ArealUK.chunk_15455 s56
  have s54 : leavesOK ctxLitU 163012500000 0 ((leaves.drop 30908).take 92) 163650000000 0 = true :=
    take_step (n := 2) (t := 92) (b := 30910) rfl rfl ArealUCore.ArealUK.chunk_15454 s55
  have s53 : leavesOK ctxLitU 162987500000 0 ((leaves.drop 30906).take 94) 163650000000 0 = true :=
    take_step (n := 2) (t := 94) (b := 30908) rfl rfl ArealUCore.ArealUK.chunk_15453 s54
  have s52 : leavesOK ctxLitU 162968750000 0 ((leaves.drop 30904).take 96) 163650000000 0 = true :=
    take_step (n := 2) (t := 96) (b := 30906) rfl rfl ArealUCore.ArealUK.chunk_15452 s53
  have s51 : leavesOK ctxLitU 162956250000 0 ((leaves.drop 30902).take 98) 163650000000 0 = true :=
    take_step (n := 2) (t := 98) (b := 30904) rfl rfl ArealUCore.ArealUK.chunk_15451 s52
  have s50 : leavesOK ctxLitU 162937500000 0 ((leaves.drop 30900).take 100) 163650000000 0 = true :=
    take_step (n := 2) (t := 100) (b := 30902) rfl rfl ArealUCore.ArealUK.chunk_15450 s51
  have s49 : leavesOK ctxLitU 325825000000 1 ((leaves.drop 30898).take 102) 163650000000 0 = true :=
    take_step (n := 2) (t := 102) (b := 30900) rfl rfl ArealUCore.ArealUK.chunk_15449 s50
  have s48 : leavesOK ctxLitU 325787500000 1 ((leaves.drop 30896).take 104) 163650000000 0 = true :=
    take_step (n := 2) (t := 104) (b := 30898) rfl rfl ArealUCore.ArealUK.chunk_15448 s49
  have s47 : leavesOK ctxLitU 325762500000 1 ((leaves.drop 30894).take 106) 163650000000 0 = true :=
    take_step (n := 2) (t := 106) (b := 30896) rfl rfl ArealUCore.ArealUK.chunk_15447 s48
  have s46 : leavesOK ctxLitU 162868750000 0 ((leaves.drop 30892).take 108) 163650000000 0 = true :=
    take_step (n := 2) (t := 108) (b := 30894) rfl rfl ArealUCore.ArealUK.chunk_15446 s47
  have s45 : leavesOK ctxLitU 162856250000 0 ((leaves.drop 30890).take 110) 163650000000 0 = true :=
    take_step (n := 2) (t := 110) (b := 30892) rfl rfl ArealUCore.ArealUK.chunk_15445 s46
  have s44 : leavesOK ctxLitU 162843750000 0 ((leaves.drop 30888).take 112) 163650000000 0 = true :=
    take_step (n := 2) (t := 112) (b := 30890) rfl rfl ArealUCore.ArealUK.chunk_15444 s45
  have s43 : leavesOK ctxLitU 162831250000 0 ((leaves.drop 30886).take 114) 163650000000 0 = true :=
    take_step (n := 2) (t := 114) (b := 30888) rfl rfl ArealUCore.ArealUK.chunk_15443 s44
  have s42 : leavesOK ctxLitU 162818750000 0 ((leaves.drop 30884).take 116) 163650000000 0 = true :=
    take_step (n := 2) (t := 116) (b := 30886) rfl rfl ArealUCore.ArealUK.chunk_15442 s43
  have s41 : leavesOK ctxLitU 162806250000 0 ((leaves.drop 30882).take 118) 163650000000 0 = true :=
    take_step (n := 2) (t := 118) (b := 30884) rfl rfl ArealUCore.ArealUK.chunk_15441 s42
  have s40 : leavesOK ctxLitU 162793750000 0 ((leaves.drop 30880).take 120) 163650000000 0 = true :=
    take_step (n := 2) (t := 120) (b := 30882) rfl rfl ArealUCore.ArealUK.chunk_15440 s41
  have s39 : leavesOK ctxLitU 162781250000 0 ((leaves.drop 30878).take 122) 163650000000 0 = true :=
    take_step (n := 2) (t := 122) (b := 30880) rfl rfl ArealUCore.ArealUK.chunk_15439 s40
  have s38 : leavesOK ctxLitU 162768750000 0 ((leaves.drop 30876).take 124) 163650000000 0 = true :=
    take_step (n := 2) (t := 124) (b := 30878) rfl rfl ArealUCore.ArealUK.chunk_15438 s39
  have s37 : leavesOK ctxLitU 162756250000 0 ((leaves.drop 30874).take 126) 163650000000 0 = true :=
    take_step (n := 2) (t := 126) (b := 30876) rfl rfl ArealUCore.ArealUK.chunk_15437 s38
  have s36 : leavesOK ctxLitU 162743750000 0 ((leaves.drop 30872).take 128) 163650000000 0 = true :=
    take_step (n := 2) (t := 128) (b := 30874) rfl rfl ArealUCore.ArealUK.chunk_15436 s37
  have s35 : leavesOK ctxLitU 162731250000 0 ((leaves.drop 30870).take 130) 163650000000 0 = true :=
    take_step (n := 2) (t := 130) (b := 30872) rfl rfl ArealUCore.ArealUK.chunk_15435 s36
  have s34 : leavesOK ctxLitU 162712500000 0 ((leaves.drop 30868).take 132) 163650000000 0 = true :=
    take_step (n := 2) (t := 132) (b := 30870) rfl rfl ArealUCore.ArealUK.chunk_15434 s35
  have s33 : leavesOK ctxLitU 162687500000 0 ((leaves.drop 30866).take 134) 163650000000 0 = true :=
    take_step (n := 2) (t := 134) (b := 30868) rfl rfl ArealUCore.ArealUK.chunk_15433 s34
  have s32 : leavesOK ctxLitU 162668750000 0 ((leaves.drop 30864).take 136) 163650000000 0 = true :=
    take_step (n := 2) (t := 136) (b := 30866) rfl rfl ArealUCore.ArealUK.chunk_15432 s33
  have s31 : leavesOK ctxLitU 162656250000 0 ((leaves.drop 30862).take 138) 163650000000 0 = true :=
    take_step (n := 2) (t := 138) (b := 30864) rfl rfl ArealUCore.ArealUK.chunk_15431 s32
  have s30 : leavesOK ctxLitU 162643750000 0 ((leaves.drop 30860).take 140) 163650000000 0 = true :=
    take_step (n := 2) (t := 140) (b := 30862) rfl rfl ArealUCore.ArealUK.chunk_15430 s31
  have s29 : leavesOK ctxLitU 162631250000 0 ((leaves.drop 30858).take 142) 163650000000 0 = true :=
    take_step (n := 2) (t := 142) (b := 30860) rfl rfl ArealUCore.ArealUK.chunk_15429 s30
  have s28 : leavesOK ctxLitU 162612500000 0 ((leaves.drop 30856).take 144) 163650000000 0 = true :=
    take_step (n := 2) (t := 144) (b := 30858) rfl rfl ArealUCore.ArealUK.chunk_15428 s29
  have s27 : leavesOK ctxLitU 162593750000 0 ((leaves.drop 30854).take 146) 163650000000 0 = true :=
    take_step (n := 2) (t := 146) (b := 30856) rfl rfl ArealUCore.ArealUK.chunk_15427 s28
  have s26 : leavesOK ctxLitU 162581250000 0 ((leaves.drop 30852).take 148) 163650000000 0 = true :=
    take_step (n := 2) (t := 148) (b := 30854) rfl rfl ArealUCore.ArealUK.chunk_15426 s27
  have s25 : leavesOK ctxLitU 162562500000 0 ((leaves.drop 30850).take 150) 163650000000 0 = true :=
    take_step (n := 2) (t := 150) (b := 30852) rfl rfl ArealUCore.ArealUK.chunk_15425 s26
  have s24 : leavesOK ctxLitU 162543750000 0 ((leaves.drop 30848).take 152) 163650000000 0 = true :=
    take_step (n := 2) (t := 152) (b := 30850) rfl rfl ArealUCore.ArealUK.chunk_15424 s25
  have s23 : leavesOK ctxLitU 162531250000 0 ((leaves.drop 30846).take 154) 163650000000 0 = true :=
    take_step (n := 2) (t := 154) (b := 30848) rfl rfl ArealUCore.ArealUK.chunk_15423 s24
  have s22 : leavesOK ctxLitU 325037500000 1 ((leaves.drop 30844).take 156) 163650000000 0 = true :=
    take_step (n := 2) (t := 156) (b := 30846) rfl rfl ArealUCore.ArealUK.chunk_15422 s23
  have s21 : leavesOK ctxLitU 325012500000 1 ((leaves.drop 30842).take 158) 163650000000 0 = true :=
    take_step (n := 2) (t := 158) (b := 30844) rfl rfl ArealUCore.ArealUK.chunk_15421 s22
  have s20 : leavesOK ctxLitU 162487500000 0 ((leaves.drop 30840).take 160) 163650000000 0 = true :=
    take_step (n := 2) (t := 160) (b := 30842) rfl rfl ArealUCore.ArealUK.chunk_15420 s21
  have s19 : leavesOK ctxLitU 162468750000 0 ((leaves.drop 30838).take 162) 163650000000 0 = true :=
    take_step (n := 2) (t := 162) (b := 30840) rfl rfl ArealUCore.ArealUK.chunk_15419 s20
  have s18 : leavesOK ctxLitU 162456250000 0 ((leaves.drop 30836).take 164) 163650000000 0 = true :=
    take_step (n := 2) (t := 164) (b := 30838) rfl rfl ArealUCore.ArealUK.chunk_15418 s19
  have s17 : leavesOK ctxLitU 162443750000 0 ((leaves.drop 30834).take 166) 163650000000 0 = true :=
    take_step (n := 2) (t := 166) (b := 30836) rfl rfl ArealUCore.ArealUK.chunk_15417 s18
  have s16 : leavesOK ctxLitU 162431250000 0 ((leaves.drop 30832).take 168) 163650000000 0 = true :=
    take_step (n := 2) (t := 168) (b := 30834) rfl rfl ArealUCore.ArealUK.chunk_15416 s17
  have s15 : leavesOK ctxLitU 162412500000 0 ((leaves.drop 30830).take 170) 163650000000 0 = true :=
    take_step (n := 2) (t := 170) (b := 30832) rfl rfl ArealUCore.ArealUK.chunk_15415 s16
  have s14 : leavesOK ctxLitU 162387500000 0 ((leaves.drop 30828).take 172) 163650000000 0 = true :=
    take_step (n := 2) (t := 172) (b := 30830) rfl rfl ArealUCore.ArealUK.chunk_15414 s15
  have s13 : leavesOK ctxLitU 162368750000 0 ((leaves.drop 30826).take 174) 163650000000 0 = true :=
    take_step (n := 2) (t := 174) (b := 30828) rfl rfl ArealUCore.ArealUK.chunk_15413 s14
  have s12 : leavesOK ctxLitU 162356250000 0 ((leaves.drop 30824).take 176) 163650000000 0 = true :=
    take_step (n := 2) (t := 176) (b := 30826) rfl rfl ArealUCore.ArealUK.chunk_15412 s13
  have s11 : leavesOK ctxLitU 162343750000 0 ((leaves.drop 30822).take 178) 163650000000 0 = true :=
    take_step (n := 2) (t := 178) (b := 30824) rfl rfl ArealUCore.ArealUK.chunk_15411 s12
  have s10 : leavesOK ctxLitU 162331250000 0 ((leaves.drop 30820).take 180) 163650000000 0 = true :=
    take_step (n := 2) (t := 180) (b := 30822) rfl rfl ArealUCore.ArealUK.chunk_15410 s11
  have s9 : leavesOK ctxLitU 162312500000 0 ((leaves.drop 30818).take 182) 163650000000 0 = true :=
    take_step (n := 2) (t := 182) (b := 30820) rfl rfl ArealUCore.ArealUK.chunk_15409 s10
  have s8 : leavesOK ctxLitU 324587500000 1 ((leaves.drop 30816).take 184) 163650000000 0 = true :=
    take_step (n := 2) (t := 184) (b := 30818) rfl rfl ArealUCore.ArealUK.chunk_15408 s9
  have s7 : leavesOK ctxLitU 324562500000 1 ((leaves.drop 30814).take 186) 163650000000 0 = true :=
    take_step (n := 2) (t := 186) (b := 30816) rfl rfl ArealUCore.ArealUK.chunk_15407 s8
  have s6 : leavesOK ctxLitU 162268750000 0 ((leaves.drop 30812).take 188) 163650000000 0 = true :=
    take_step (n := 2) (t := 188) (b := 30814) rfl rfl ArealUCore.ArealUK.chunk_15406 s7
  have s5 : leavesOK ctxLitU 162256250000 0 ((leaves.drop 30810).take 190) 163650000000 0 = true :=
    take_step (n := 2) (t := 190) (b := 30812) rfl rfl ArealUCore.ArealUK.chunk_15405 s6
  have s4 : leavesOK ctxLitU 162243750000 0 ((leaves.drop 30808).take 192) 163650000000 0 = true :=
    take_step (n := 2) (t := 192) (b := 30810) rfl rfl ArealUCore.ArealUK.chunk_15404 s5
  have s3 : leavesOK ctxLitU 162231250000 0 ((leaves.drop 30806).take 194) 163650000000 0 = true :=
    take_step (n := 2) (t := 194) (b := 30808) rfl rfl ArealUCore.ArealUK.chunk_15403 s4
  have s2 : leavesOK ctxLitU 162218750000 0 ((leaves.drop 30804).take 196) 163650000000 0 = true :=
    take_step (n := 2) (t := 196) (b := 30806) rfl rfl ArealUCore.ArealUK.chunk_15402 s3
  have s1 : leavesOK ctxLitU 162206250000 0 ((leaves.drop 30802).take 198) 163650000000 0 = true :=
    take_step (n := 2) (t := 198) (b := 30804) rfl rfl ArealUCore.ArealUK.chunk_15401 s2
  have s0 : leavesOK ctxLitU 324387500000 1 ((leaves.drop 30800).take 200) 163650000000 0 = true :=
    take_step (n := 2) (t := 200) (b := 30802) rfl rfl ArealUCore.ArealUK.chunk_15400 s1
  exact s0

end Areal.UCert

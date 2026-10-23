import ArealUK.Chunk13400
import ArealUK.Chunk13401
import ArealUK.Chunk13402
import ArealUK.Chunk13403
import ArealUK.Chunk13404
import ArealUK.Chunk13405
import ArealUK.Chunk13406
import ArealUK.Chunk13407
import ArealUK.Chunk13408
import ArealUK.Chunk13409
import ArealUK.Chunk13410
import ArealUK.Chunk13411
import ArealUK.Chunk13412
import ArealUK.Chunk13413
import ArealUK.Chunk13414
import ArealUK.Chunk13415
import ArealUK.Chunk13416
import ArealUK.Chunk13417
import ArealUK.Chunk13418
import ArealUK.Chunk13419
import ArealUK.Chunk13420
import ArealUK.Chunk13421
import ArealUK.Chunk13422
import ArealUK.Chunk13423
import ArealUK.Chunk13424
import ArealUK.Chunk13425
import ArealUK.Chunk13426
import ArealUK.Chunk13427
import ArealUK.Chunk13428
import ArealUK.Chunk13429
import ArealUK.Chunk13430
import ArealUK.Chunk13431
import ArealUK.Chunk13432
import ArealUK.Chunk13433
import ArealUK.Chunk13434
import ArealUK.Chunk13435
import ArealUK.Chunk13436
import ArealUK.Chunk13437
import ArealUK.Chunk13438
import ArealUK.Chunk13439
import ArealUK.Chunk13440
import ArealUK.Chunk13441
import ArealUK.Chunk13442
import ArealUK.Chunk13443
import ArealUK.Chunk13444
import ArealUK.Chunk13445
import ArealUK.Chunk13446
import ArealUK.Chunk13447
import ArealUK.Chunk13448
import ArealUK.Chunk13449
import ArealUK.Chunk13450
import ArealUK.Chunk13451
import ArealUK.Chunk13452
import ArealUK.Chunk13453
import ArealUK.Chunk13454
import ArealUK.Chunk13455
import ArealUK.Chunk13456
import ArealUK.Chunk13457
import ArealUK.Chunk13458
import ArealUK.Chunk13459
import ArealUK.Chunk13460
import ArealUK.Chunk13461
import ArealUK.Chunk13462
import ArealUK.Chunk13463
import ArealUK.Chunk13464
import ArealUK.Chunk13465
import ArealUK.Chunk13466
import ArealUK.Chunk13467
import ArealUK.Chunk13468
import ArealUK.Chunk13469
import ArealUK.Chunk13470
import ArealUK.Chunk13471
import ArealUK.Chunk13472
import ArealUK.Chunk13473
import ArealUK.Chunk13474
import ArealUK.Chunk13475
import ArealUK.Chunk13476
import ArealUK.Chunk13477
import ArealUK.Chunk13478
import ArealUK.Chunk13479
import ArealUK.Chunk13480
import ArealUK.Chunk13481
import ArealUK.Chunk13482
import ArealUK.Chunk13483
import ArealUK.Chunk13484
import ArealUK.Chunk13485
import ArealUK.Chunk13486
import ArealUK.Chunk13487
import ArealUK.Chunk13488
import ArealUK.Chunk13489
import ArealUK.Chunk13490
import ArealUK.Chunk13491
import ArealUK.Chunk13492
import ArealUK.Chunk13493
import ArealUK.Chunk13494
import ArealUK.Chunk13495
import ArealUK.Chunk13496
import ArealUK.Chunk13497
import ArealUK.Chunk13498
import ArealUK.Chunk13499
import Areal.UCert.LeavesKGen

/-! Group 134 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_134 : leavesOK ctxLitU 136737500000 0 ((leaves.drop 26800).take 200) 137943750000 0 = true := by
  have s99 := ArealUCore.ArealUK.chunk_13499
  have s98 : leavesOK ctxLitU 275837500000 1 ((leaves.drop 26996).take 4) 137943750000 0 = true :=
    take_step (n := 2) (t := 4) (b := 26998) rfl rfl ArealUCore.ArealUK.chunk_13498 s99
  have s97 : leavesOK ctxLitU 275812500000 1 ((leaves.drop 26994).take 6) 137943750000 0 = true :=
    take_step (n := 2) (t := 6) (b := 26996) rfl rfl ArealUCore.ArealUK.chunk_13497 s98
  have s96 : leavesOK ctxLitU 275787500000 1 ((leaves.drop 26992).take 8) 137943750000 0 = true :=
    take_step (n := 2) (t := 8) (b := 26994) rfl rfl ArealUCore.ArealUK.chunk_13496 s97
  have s95 : leavesOK ctxLitU 275762500000 1 ((leaves.drop 26990).take 10) 137943750000 0 = true :=
    take_step (n := 2) (t := 10) (b := 26992) rfl rfl ArealUCore.ArealUK.chunk_13495 s96
  have s94 : leavesOK ctxLitU 137868750000 0 ((leaves.drop 26988).take 12) 137943750000 0 = true :=
    take_step (n := 2) (t := 12) (b := 26990) rfl rfl ArealUCore.ArealUK.chunk_13494 s95
  have s93 : leavesOK ctxLitU 137856250000 0 ((leaves.drop 26986).take 14) 137943750000 0 = true :=
    take_step (n := 2) (t := 14) (b := 26988) rfl rfl ArealUCore.ArealUK.chunk_13493 s94
  have s92 : leavesOK ctxLitU 137843750000 0 ((leaves.drop 26984).take 16) 137943750000 0 = true :=
    take_step (n := 2) (t := 16) (b := 26986) rfl rfl ArealUCore.ArealUK.chunk_13492 s93
  have s91 : leavesOK ctxLitU 137831250000 0 ((leaves.drop 26982).take 18) 137943750000 0 = true :=
    take_step (n := 2) (t := 18) (b := 26984) rfl rfl ArealUCore.ArealUK.chunk_13491 s92
  have s90 : leavesOK ctxLitU 275637500000 1 ((leaves.drop 26980).take 20) 137943750000 0 = true :=
    take_step (n := 2) (t := 20) (b := 26982) rfl rfl ArealUCore.ArealUK.chunk_13490 s91
  have s89 : leavesOK ctxLitU 275612500000 1 ((leaves.drop 26978).take 22) 137943750000 0 = true :=
    take_step (n := 2) (t := 22) (b := 26980) rfl rfl ArealUCore.ArealUK.chunk_13489 s90
  have s88 : leavesOK ctxLitU 275587500000 1 ((leaves.drop 26976).take 24) 137943750000 0 = true :=
    take_step (n := 2) (t := 24) (b := 26978) rfl rfl ArealUCore.ArealUK.chunk_13488 s89
  have s87 : leavesOK ctxLitU 275562500000 1 ((leaves.drop 26974).take 26) 137943750000 0 = true :=
    take_step (n := 2) (t := 26) (b := 26976) rfl rfl ArealUCore.ArealUK.chunk_13487 s88
  have s86 : leavesOK ctxLitU 137768750000 0 ((leaves.drop 26972).take 28) 137943750000 0 = true :=
    take_step (n := 2) (t := 28) (b := 26974) rfl rfl ArealUCore.ArealUK.chunk_13486 s87
  have s85 : leavesOK ctxLitU 137756250000 0 ((leaves.drop 26970).take 30) 137943750000 0 = true :=
    take_step (n := 2) (t := 30) (b := 26972) rfl rfl ArealUCore.ArealUK.chunk_13485 s86
  have s84 : leavesOK ctxLitU 137743750000 0 ((leaves.drop 26968).take 32) 137943750000 0 = true :=
    take_step (n := 2) (t := 32) (b := 26970) rfl rfl ArealUCore.ArealUK.chunk_13484 s85
  have s83 : leavesOK ctxLitU 137731250000 0 ((leaves.drop 26966).take 34) 137943750000 0 = true :=
    take_step (n := 2) (t := 34) (b := 26968) rfl rfl ArealUCore.ArealUK.chunk_13483 s84
  have s82 : leavesOK ctxLitU 275437500000 1 ((leaves.drop 26964).take 36) 137943750000 0 = true :=
    take_step (n := 2) (t := 36) (b := 26966) rfl rfl ArealUCore.ArealUK.chunk_13482 s83
  have s81 : leavesOK ctxLitU 275412500000 1 ((leaves.drop 26962).take 38) 137943750000 0 = true :=
    take_step (n := 2) (t := 38) (b := 26964) rfl rfl ArealUCore.ArealUK.chunk_13481 s82
  have s80 : leavesOK ctxLitU 275387500000 1 ((leaves.drop 26960).take 40) 137943750000 0 = true :=
    take_step (n := 2) (t := 40) (b := 26962) rfl rfl ArealUCore.ArealUK.chunk_13480 s81
  have s79 : leavesOK ctxLitU 275362500000 1 ((leaves.drop 26958).take 42) 137943750000 0 = true :=
    take_step (n := 2) (t := 42) (b := 26960) rfl rfl ArealUCore.ArealUK.chunk_13479 s80
  have s78 : leavesOK ctxLitU 137668750000 0 ((leaves.drop 26956).take 44) 137943750000 0 = true :=
    take_step (n := 2) (t := 44) (b := 26958) rfl rfl ArealUCore.ArealUK.chunk_13478 s79
  have s77 : leavesOK ctxLitU 137656250000 0 ((leaves.drop 26954).take 46) 137943750000 0 = true :=
    take_step (n := 2) (t := 46) (b := 26956) rfl rfl ArealUCore.ArealUK.chunk_13477 s78
  have s76 : leavesOK ctxLitU 137643750000 0 ((leaves.drop 26952).take 48) 137943750000 0 = true :=
    take_step (n := 2) (t := 48) (b := 26954) rfl rfl ArealUCore.ArealUK.chunk_13476 s77
  have s75 : leavesOK ctxLitU 137631250000 0 ((leaves.drop 26950).take 50) 137943750000 0 = true :=
    take_step (n := 2) (t := 50) (b := 26952) rfl rfl ArealUCore.ArealUK.chunk_13475 s76
  have s74 : leavesOK ctxLitU 275237500000 1 ((leaves.drop 26948).take 52) 137943750000 0 = true :=
    take_step (n := 2) (t := 52) (b := 26950) rfl rfl ArealUCore.ArealUK.chunk_13474 s75
  have s73 : leavesOK ctxLitU 275212500000 1 ((leaves.drop 26946).take 54) 137943750000 0 = true :=
    take_step (n := 2) (t := 54) (b := 26948) rfl rfl ArealUCore.ArealUK.chunk_13473 s74
  have s72 : leavesOK ctxLitU 550375000000 2 ((leaves.drop 26944).take 56) 137943750000 0 = true :=
    take_step (n := 2) (t := 56) (b := 26946) rfl rfl ArealUCore.ArealUK.chunk_13472 s73
  have s71 : leavesOK ctxLitU 550325000000 2 ((leaves.drop 26942).take 58) 137943750000 0 = true :=
    take_step (n := 2) (t := 58) (b := 26944) rfl rfl ArealUCore.ArealUK.chunk_13471 s72
  have s70 : leavesOK ctxLitU 550275000000 2 ((leaves.drop 26940).take 60) 137943750000 0 = true :=
    take_step (n := 2) (t := 60) (b := 26942) rfl rfl ArealUCore.ArealUK.chunk_13470 s71
  have s69 : leavesOK ctxLitU 550225000000 2 ((leaves.drop 26938).take 62) 137943750000 0 = true :=
    take_step (n := 2) (t := 62) (b := 26940) rfl rfl ArealUCore.ArealUK.chunk_13469 s70
  have s68 : leavesOK ctxLitU 275087500000 1 ((leaves.drop 26936).take 64) 137943750000 0 = true :=
    take_step (n := 2) (t := 64) (b := 26938) rfl rfl ArealUCore.ArealUK.chunk_13468 s69
  have s67 : leavesOK ctxLitU 275062500000 1 ((leaves.drop 26934).take 66) 137943750000 0 = true :=
    take_step (n := 2) (t := 66) (b := 26936) rfl rfl ArealUCore.ArealUK.chunk_13467 s68
  have s66 : leavesOK ctxLitU 137518750000 0 ((leaves.drop 26932).take 68) 137943750000 0 = true :=
    take_step (n := 2) (t := 68) (b := 26934) rfl rfl ArealUCore.ArealUK.chunk_13466 s67
  have s65 : leavesOK ctxLitU 275018750000 1 ((leaves.drop 26930).take 70) 137943750000 0 = true :=
    take_step (n := 2) (t := 70) (b := 26932) rfl rfl ArealUCore.ArealUK.chunk_13465 s66
  have s64 : leavesOK ctxLitU 275006250000 1 ((leaves.drop 26928).take 72) 137943750000 0 = true :=
    take_step (n := 2) (t := 72) (b := 26930) rfl rfl ArealUCore.ArealUK.chunk_13464 s65
  have s63 : leavesOK ctxLitU 274987500000 1 ((leaves.drop 26926).take 74) 137943750000 0 = true :=
    take_step (n := 2) (t := 74) (b := 26928) rfl rfl ArealUCore.ArealUK.chunk_13463 s64
  have s62 : leavesOK ctxLitU 274962500000 1 ((leaves.drop 26924).take 76) 137943750000 0 = true :=
    take_step (n := 2) (t := 76) (b := 26926) rfl rfl ArealUCore.ArealUK.chunk_13462 s63
  have s61 : leavesOK ctxLitU 549875000000 2 ((leaves.drop 26922).take 78) 137943750000 0 = true :=
    take_step (n := 2) (t := 78) (b := 26924) rfl rfl ArealUCore.ArealUK.chunk_13461 s62
  have s60 : leavesOK ctxLitU 549825000000 2 ((leaves.drop 26920).take 80) 137943750000 0 = true :=
    take_step (n := 2) (t := 80) (b := 26922) rfl rfl ArealUCore.ArealUK.chunk_13460 s61
  have s59 : leavesOK ctxLitU 549775000000 2 ((leaves.drop 26918).take 82) 137943750000 0 = true :=
    take_step (n := 2) (t := 82) (b := 26920) rfl rfl ArealUCore.ArealUK.chunk_13459 s60
  have s58 : leavesOK ctxLitU 549725000000 2 ((leaves.drop 26916).take 84) 137943750000 0 = true :=
    take_step (n := 2) (t := 84) (b := 26918) rfl rfl ArealUCore.ArealUK.chunk_13458 s59
  have s57 : leavesOK ctxLitU 549675000000 2 ((leaves.drop 26914).take 86) 137943750000 0 = true :=
    take_step (n := 2) (t := 86) (b := 26916) rfl rfl ArealUCore.ArealUK.chunk_13457 s58
  have s56 : leavesOK ctxLitU 549625000000 2 ((leaves.drop 26912).take 88) 137943750000 0 = true :=
    take_step (n := 2) (t := 88) (b := 26914) rfl rfl ArealUCore.ArealUK.chunk_13456 s57
  have s55 : leavesOK ctxLitU 549575000000 2 ((leaves.drop 26910).take 90) 137943750000 0 = true :=
    take_step (n := 2) (t := 90) (b := 26912) rfl rfl ArealUCore.ArealUK.chunk_13455 s56
  have s54 : leavesOK ctxLitU 549525000000 2 ((leaves.drop 26908).take 92) 137943750000 0 = true :=
    take_step (n := 2) (t := 92) (b := 26910) rfl rfl ArealUCore.ArealUK.chunk_13454 s55
  have s53 : leavesOK ctxLitU 549475000000 2 ((leaves.drop 26906).take 94) 137943750000 0 = true :=
    take_step (n := 2) (t := 94) (b := 26908) rfl rfl ArealUCore.ArealUK.chunk_13453 s54
  have s52 : leavesOK ctxLitU 549425000000 2 ((leaves.drop 26904).take 96) 137943750000 0 = true :=
    take_step (n := 2) (t := 96) (b := 26906) rfl rfl ArealUCore.ArealUK.chunk_13452 s53
  have s51 : leavesOK ctxLitU 549375000000 2 ((leaves.drop 26902).take 98) 137943750000 0 = true :=
    take_step (n := 2) (t := 98) (b := 26904) rfl rfl ArealUCore.ArealUK.chunk_13451 s52
  have s50 : leavesOK ctxLitU 549325000000 2 ((leaves.drop 26900).take 100) 137943750000 0 = true :=
    take_step (n := 2) (t := 100) (b := 26902) rfl rfl ArealUCore.ArealUK.chunk_13450 s51
  have s49 : leavesOK ctxLitU 549275000000 2 ((leaves.drop 26898).take 102) 137943750000 0 = true :=
    take_step (n := 2) (t := 102) (b := 26900) rfl rfl ArealUCore.ArealUK.chunk_13449 s50
  have s48 : leavesOK ctxLitU 549225000000 2 ((leaves.drop 26896).take 104) 137943750000 0 = true :=
    take_step (n := 2) (t := 104) (b := 26898) rfl rfl ArealUCore.ArealUK.chunk_13448 s49
  have s47 : leavesOK ctxLitU 274587500000 1 ((leaves.drop 26894).take 106) 137943750000 0 = true :=
    take_step (n := 2) (t := 106) (b := 26896) rfl rfl ArealUCore.ArealUK.chunk_13447 s48
  have s46 : leavesOK ctxLitU 274562500000 1 ((leaves.drop 26892).take 108) 137943750000 0 = true :=
    take_step (n := 2) (t := 108) (b := 26894) rfl rfl ArealUCore.ArealUK.chunk_13446 s47
  have s45 : leavesOK ctxLitU 137268750000 0 ((leaves.drop 26890).take 110) 137943750000 0 = true :=
    take_step (n := 2) (t := 110) (b := 26892) rfl rfl ArealUCore.ArealUK.chunk_13445 s46
  have s44 : leavesOK ctxLitU 274525000000 1 ((leaves.drop 26888).take 112) 137943750000 0 = true :=
    take_step (n := 2) (t := 112) (b := 26890) rfl rfl ArealUCore.ArealUK.chunk_13444 s45
  have s43 : leavesOK ctxLitU 137250000000 0 ((leaves.drop 26886).take 114) 137943750000 0 = true :=
    take_step (n := 2) (t := 114) (b := 26888) rfl rfl ArealUCore.ArealUK.chunk_13443 s44
  have s42 : leavesOK ctxLitU 137237500000 0 ((leaves.drop 26884).take 116) 137943750000 0 = true :=
    take_step (n := 2) (t := 116) (b := 26886) rfl rfl ArealUCore.ArealUK.chunk_13442 s43
  have s41 : leavesOK ctxLitU 137225000000 0 ((leaves.drop 26882).take 118) 137943750000 0 = true :=
    take_step (n := 2) (t := 118) (b := 26884) rfl rfl ArealUCore.ArealUK.chunk_13441 s42
  have s40 : leavesOK ctxLitU 274425000000 1 ((leaves.drop 26880).take 120) 137943750000 0 = true :=
    take_step (n := 2) (t := 120) (b := 26882) rfl rfl ArealUCore.ArealUK.chunk_13440 s41
  have s39 : leavesOK ctxLitU 274400000000 1 ((leaves.drop 26878).take 122) 137943750000 0 = true :=
    take_step (n := 2) (t := 122) (b := 26880) rfl rfl ArealUCore.ArealUK.chunk_13439 s40
  have s38 : leavesOK ctxLitU 274375000000 1 ((leaves.drop 26876).take 124) 137943750000 0 = true :=
    take_step (n := 2) (t := 124) (b := 26878) rfl rfl ArealUCore.ArealUK.chunk_13438 s39
  have s37 : leavesOK ctxLitU 274350000000 1 ((leaves.drop 26874).take 126) 137943750000 0 = true :=
    take_step (n := 2) (t := 126) (b := 26876) rfl rfl ArealUCore.ArealUK.chunk_13437 s38
  have s36 : leavesOK ctxLitU 137162500000 0 ((leaves.drop 26872).take 128) 137943750000 0 = true :=
    take_step (n := 2) (t := 128) (b := 26874) rfl rfl ArealUCore.ArealUK.chunk_13436 s37
  have s35 : leavesOK ctxLitU 137150000000 0 ((leaves.drop 26870).take 130) 137943750000 0 = true :=
    take_step (n := 2) (t := 130) (b := 26872) rfl rfl ArealUCore.ArealUK.chunk_13435 s36
  have s34 : leavesOK ctxLitU 137137500000 0 ((leaves.drop 26868).take 132) 137943750000 0 = true :=
    take_step (n := 2) (t := 132) (b := 26870) rfl rfl ArealUCore.ArealUK.chunk_13434 s35
  have s33 : leavesOK ctxLitU 274262500000 1 ((leaves.drop 26866).take 134) 137943750000 0 = true :=
    take_step (n := 2) (t := 134) (b := 26868) rfl rfl ArealUCore.ArealUK.chunk_13433 s34
  have s32 : leavesOK ctxLitU 274250000000 1 ((leaves.drop 26864).take 136) 137943750000 0 = true :=
    take_step (n := 2) (t := 136) (b := 26866) rfl rfl ArealUCore.ArealUK.chunk_13432 s33
  have s31 : leavesOK ctxLitU 274225000000 1 ((leaves.drop 26862).take 138) 137943750000 0 = true :=
    take_step (n := 2) (t := 138) (b := 26864) rfl rfl ArealUCore.ArealUK.chunk_13431 s32
  have s30 : leavesOK ctxLitU 548425000000 2 ((leaves.drop 26860).take 140) 137943750000 0 = true :=
    take_step (n := 2) (t := 140) (b := 26862) rfl rfl ArealUCore.ArealUK.chunk_13430 s31
  have s29 : leavesOK ctxLitU 548375000000 2 ((leaves.drop 26858).take 142) 137943750000 0 = true :=
    take_step (n := 2) (t := 142) (b := 26860) rfl rfl ArealUCore.ArealUK.chunk_13429 s30
  have s28 : leavesOK ctxLitU 548325000000 2 ((leaves.drop 26856).take 144) 137943750000 0 = true :=
    take_step (n := 2) (t := 144) (b := 26858) rfl rfl ArealUCore.ArealUK.chunk_13428 s29
  have s27 : leavesOK ctxLitU 548275000000 2 ((leaves.drop 26854).take 146) 137943750000 0 = true :=
    take_step (n := 2) (t := 146) (b := 26856) rfl rfl ArealUCore.ArealUK.chunk_13427 s28
  have s26 : leavesOK ctxLitU 548225000000 2 ((leaves.drop 26852).take 148) 137943750000 0 = true :=
    take_step (n := 2) (t := 148) (b := 26854) rfl rfl ArealUCore.ArealUK.chunk_13426 s27
  have s25 : leavesOK ctxLitU 548175000000 2 ((leaves.drop 26850).take 150) 137943750000 0 = true :=
    take_step (n := 2) (t := 150) (b := 26852) rfl rfl ArealUCore.ArealUK.chunk_13425 s26
  have s24 : leavesOK ctxLitU 548125000000 2 ((leaves.drop 26848).take 152) 137943750000 0 = true :=
    take_step (n := 2) (t := 152) (b := 26850) rfl rfl ArealUCore.ArealUK.chunk_13424 s25
  have s23 : leavesOK ctxLitU 548075000000 2 ((leaves.drop 26846).take 154) 137943750000 0 = true :=
    take_step (n := 2) (t := 154) (b := 26848) rfl rfl ArealUCore.ArealUK.chunk_13423 s24
  have s22 : leavesOK ctxLitU 548025000000 2 ((leaves.drop 26844).take 156) 137943750000 0 = true :=
    take_step (n := 2) (t := 156) (b := 26846) rfl rfl ArealUCore.ArealUK.chunk_13422 s23
  have s21 : leavesOK ctxLitU 273987500000 1 ((leaves.drop 26842).take 158) 137943750000 0 = true :=
    take_step (n := 2) (t := 158) (b := 26844) rfl rfl ArealUCore.ArealUK.chunk_13421 s22
  have s20 : leavesOK ctxLitU 273962500000 1 ((leaves.drop 26840).take 160) 137943750000 0 = true :=
    take_step (n := 2) (t := 160) (b := 26842) rfl rfl ArealUCore.ArealUK.chunk_13420 s21
  have s19 : leavesOK ctxLitU 273943750000 1 ((leaves.drop 26838).take 162) 137943750000 0 = true :=
    take_step (n := 2) (t := 162) (b := 26840) rfl rfl ArealUCore.ArealUK.chunk_13419 s20
  have s18 : leavesOK ctxLitU 136962500000 0 ((leaves.drop 26836).take 164) 137943750000 0 = true :=
    take_step (n := 2) (t := 164) (b := 26838) rfl rfl ArealUCore.ArealUK.chunk_13418 s19
  have s17 : leavesOK ctxLitU 136950000000 0 ((leaves.drop 26834).take 166) 137943750000 0 = true :=
    take_step (n := 2) (t := 166) (b := 26836) rfl rfl ArealUCore.ArealUK.chunk_13417 s18
  have s16 : leavesOK ctxLitU 136937500000 0 ((leaves.drop 26832).take 168) 137943750000 0 = true :=
    take_step (n := 2) (t := 168) (b := 26834) rfl rfl ArealUCore.ArealUK.chunk_13416 s17
  have s15 : leavesOK ctxLitU 136925000000 0 ((leaves.drop 26830).take 170) 137943750000 0 = true :=
    take_step (n := 2) (t := 170) (b := 26832) rfl rfl ArealUCore.ArealUK.chunk_13415 s16
  have s14 : leavesOK ctxLitU 273825000000 1 ((leaves.drop 26828).take 172) 137943750000 0 = true :=
    take_step (n := 2) (t := 172) (b := 26830) rfl rfl ArealUCore.ArealUK.chunk_13414 s15
  have s13 : leavesOK ctxLitU 273800000000 1 ((leaves.drop 26826).take 174) 137943750000 0 = true :=
    take_step (n := 2) (t := 174) (b := 26828) rfl rfl ArealUCore.ArealUK.chunk_13413 s14
  have s12 : leavesOK ctxLitU 547550000000 2 ((leaves.drop 26824).take 176) 137943750000 0 = true :=
    take_step (n := 2) (t := 176) (b := 26826) rfl rfl ArealUCore.ArealUK.chunk_13412 s13
  have s11 : leavesOK ctxLitU 547500000000 2 ((leaves.drop 26822).take 178) 137943750000 0 = true :=
    take_step (n := 2) (t := 178) (b := 26824) rfl rfl ArealUCore.ArealUK.chunk_13411 s12
  have s10 : leavesOK ctxLitU 273725000000 1 ((leaves.drop 26820).take 180) 137943750000 0 = true :=
    take_step (n := 2) (t := 180) (b := 26822) rfl rfl ArealUCore.ArealUK.chunk_13410 s11
  have s9 : leavesOK ctxLitU 273700000000 1 ((leaves.drop 26818).take 182) 137943750000 0 = true :=
    take_step (n := 2) (t := 182) (b := 26820) rfl rfl ArealUCore.ArealUK.chunk_13409 s10
  have s8 : leavesOK ctxLitU 136837500000 0 ((leaves.drop 26816).take 184) 137943750000 0 = true :=
    take_step (n := 2) (t := 184) (b := 26818) rfl rfl ArealUCore.ArealUK.chunk_13408 s9
  have s7 : leavesOK ctxLitU 136825000000 0 ((leaves.drop 26814).take 186) 137943750000 0 = true :=
    take_step (n := 2) (t := 186) (b := 26816) rfl rfl ArealUCore.ArealUK.chunk_13407 s8
  have s6 : leavesOK ctxLitU 136812500000 0 ((leaves.drop 26812).take 188) 137943750000 0 = true :=
    take_step (n := 2) (t := 188) (b := 26814) rfl rfl ArealUCore.ArealUK.chunk_13406 s7
  have s5 : leavesOK ctxLitU 136800000000 0 ((leaves.drop 26810).take 190) 137943750000 0 = true :=
    take_step (n := 2) (t := 190) (b := 26812) rfl rfl ArealUCore.ArealUK.chunk_13405 s6
  have s4 : leavesOK ctxLitU 136787500000 0 ((leaves.drop 26808).take 192) 137943750000 0 = true :=
    take_step (n := 2) (t := 192) (b := 26810) rfl rfl ArealUCore.ArealUK.chunk_13404 s5
  have s3 : leavesOK ctxLitU 136775000000 0 ((leaves.drop 26806).take 194) 137943750000 0 = true :=
    take_step (n := 2) (t := 194) (b := 26808) rfl rfl ArealUCore.ArealUK.chunk_13403 s4
  have s2 : leavesOK ctxLitU 136762500000 0 ((leaves.drop 26804).take 196) 137943750000 0 = true :=
    take_step (n := 2) (t := 196) (b := 26806) rfl rfl ArealUCore.ArealUK.chunk_13402 s3
  have s1 : leavesOK ctxLitU 136750000000 0 ((leaves.drop 26802).take 198) 137943750000 0 = true :=
    take_step (n := 2) (t := 198) (b := 26804) rfl rfl ArealUCore.ArealUK.chunk_13401 s2
  have s0 : leavesOK ctxLitU 136737500000 0 ((leaves.drop 26800).take 200) 137943750000 0 = true :=
    take_step (n := 2) (t := 200) (b := 26802) rfl rfl ArealUCore.ArealUK.chunk_13400 s1
  exact s0

end Areal.UCert

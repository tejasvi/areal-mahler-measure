import ArealUK.Chunk14400
import ArealUK.Chunk14401
import ArealUK.Chunk14402
import ArealUK.Chunk14403
import ArealUK.Chunk14404
import ArealUK.Chunk14405
import ArealUK.Chunk14406
import ArealUK.Chunk14407
import ArealUK.Chunk14408
import ArealUK.Chunk14409
import ArealUK.Chunk14410
import ArealUK.Chunk14411
import ArealUK.Chunk14412
import ArealUK.Chunk14413
import ArealUK.Chunk14414
import ArealUK.Chunk14415
import ArealUK.Chunk14416
import ArealUK.Chunk14417
import ArealUK.Chunk14418
import ArealUK.Chunk14419
import ArealUK.Chunk14420
import ArealUK.Chunk14421
import ArealUK.Chunk14422
import ArealUK.Chunk14423
import ArealUK.Chunk14424
import ArealUK.Chunk14425
import ArealUK.Chunk14426
import ArealUK.Chunk14427
import ArealUK.Chunk14428
import ArealUK.Chunk14429
import ArealUK.Chunk14430
import ArealUK.Chunk14431
import ArealUK.Chunk14432
import ArealUK.Chunk14433
import ArealUK.Chunk14434
import ArealUK.Chunk14435
import ArealUK.Chunk14436
import ArealUK.Chunk14437
import ArealUK.Chunk14438
import ArealUK.Chunk14439
import ArealUK.Chunk14440
import ArealUK.Chunk14441
import ArealUK.Chunk14442
import ArealUK.Chunk14443
import ArealUK.Chunk14444
import ArealUK.Chunk14445
import ArealUK.Chunk14446
import ArealUK.Chunk14447
import ArealUK.Chunk14448
import ArealUK.Chunk14449
import ArealUK.Chunk14450
import ArealUK.Chunk14451
import ArealUK.Chunk14452
import ArealUK.Chunk14453
import ArealUK.Chunk14454
import ArealUK.Chunk14455
import ArealUK.Chunk14456
import ArealUK.Chunk14457
import ArealUK.Chunk14458
import ArealUK.Chunk14459
import ArealUK.Chunk14460
import ArealUK.Chunk14461
import ArealUK.Chunk14462
import ArealUK.Chunk14463
import ArealUK.Chunk14464
import ArealUK.Chunk14465
import ArealUK.Chunk14466
import ArealUK.Chunk14467
import ArealUK.Chunk14468
import ArealUK.Chunk14469
import ArealUK.Chunk14470
import ArealUK.Chunk14471
import ArealUK.Chunk14472
import ArealUK.Chunk14473
import ArealUK.Chunk14474
import ArealUK.Chunk14475
import ArealUK.Chunk14476
import ArealUK.Chunk14477
import ArealUK.Chunk14478
import ArealUK.Chunk14479
import ArealUK.Chunk14480
import ArealUK.Chunk14481
import ArealUK.Chunk14482
import ArealUK.Chunk14483
import ArealUK.Chunk14484
import ArealUK.Chunk14485
import ArealUK.Chunk14486
import ArealUK.Chunk14487
import ArealUK.Chunk14488
import ArealUK.Chunk14489
import ArealUK.Chunk14490
import ArealUK.Chunk14491
import ArealUK.Chunk14492
import ArealUK.Chunk14493
import ArealUK.Chunk14494
import ArealUK.Chunk14495
import ArealUK.Chunk14496
import ArealUK.Chunk14497
import ArealUK.Chunk14498
import ArealUK.Chunk14499
import Areal.UCert.LeavesKGen

/-! Group 144 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_144 : leavesOK ctxLitU 297200000000 1 ((leaves.drop 28800).take 200) 149831250000 0 = true := by
  have s99 := ArealUCore.ArealUK.chunk_14499
  have s98 : leavesOK ctxLitU 299612500000 1 ((leaves.drop 28996).take 4) 149831250000 0 = true :=
    take_step (n := 2) (t := 4) (b := 28998) rfl rfl ArealUCore.ArealUK.chunk_14498 s99
  have s97 : leavesOK ctxLitU 299587500000 1 ((leaves.drop 28994).take 6) 149831250000 0 = true :=
    take_step (n := 2) (t := 6) (b := 28996) rfl rfl ArealUCore.ArealUK.chunk_14497 s98
  have s96 : leavesOK ctxLitU 299562500000 1 ((leaves.drop 28992).take 8) 149831250000 0 = true :=
    take_step (n := 2) (t := 8) (b := 28994) rfl rfl ArealUCore.ArealUK.chunk_14496 s97
  have s95 : leavesOK ctxLitU 149768750000 0 ((leaves.drop 28990).take 10) 149831250000 0 = true :=
    take_step (n := 2) (t := 10) (b := 28992) rfl rfl ArealUCore.ArealUK.chunk_14495 s96
  have s94 : leavesOK ctxLitU 149756250000 0 ((leaves.drop 28988).take 12) 149831250000 0 = true :=
    take_step (n := 2) (t := 12) (b := 28990) rfl rfl ArealUCore.ArealUK.chunk_14494 s95
  have s93 : leavesOK ctxLitU 149743750000 0 ((leaves.drop 28986).take 14) 149831250000 0 = true :=
    take_step (n := 2) (t := 14) (b := 28988) rfl rfl ArealUCore.ArealUK.chunk_14493 s94
  have s92 : leavesOK ctxLitU 149731250000 0 ((leaves.drop 28984).take 16) 149831250000 0 = true :=
    take_step (n := 2) (t := 16) (b := 28986) rfl rfl ArealUCore.ArealUK.chunk_14492 s93
  have s91 : leavesOK ctxLitU 299437500000 1 ((leaves.drop 28982).take 18) 149831250000 0 = true :=
    take_step (n := 2) (t := 18) (b := 28984) rfl rfl ArealUCore.ArealUK.chunk_14491 s92
  have s90 : leavesOK ctxLitU 299412500000 1 ((leaves.drop 28980).take 20) 149831250000 0 = true :=
    take_step (n := 2) (t := 20) (b := 28982) rfl rfl ArealUCore.ArealUK.chunk_14490 s91
  have s89 : leavesOK ctxLitU 299387500000 1 ((leaves.drop 28978).take 22) 149831250000 0 = true :=
    take_step (n := 2) (t := 22) (b := 28980) rfl rfl ArealUCore.ArealUK.chunk_14489 s90
  have s88 : leavesOK ctxLitU 299362500000 1 ((leaves.drop 28976).take 24) 149831250000 0 = true :=
    take_step (n := 2) (t := 24) (b := 28978) rfl rfl ArealUCore.ArealUK.chunk_14488 s89
  have s87 : leavesOK ctxLitU 149668750000 0 ((leaves.drop 28974).take 26) 149831250000 0 = true :=
    take_step (n := 2) (t := 26) (b := 28976) rfl rfl ArealUCore.ArealUK.chunk_14487 s88
  have s86 : leavesOK ctxLitU 149656250000 0 ((leaves.drop 28972).take 28) 149831250000 0 = true :=
    take_step (n := 2) (t := 28) (b := 28974) rfl rfl ArealUCore.ArealUK.chunk_14486 s87
  have s85 : leavesOK ctxLitU 149643750000 0 ((leaves.drop 28970).take 30) 149831250000 0 = true :=
    take_step (n := 2) (t := 30) (b := 28972) rfl rfl ArealUCore.ArealUK.chunk_14485 s86
  have s84 : leavesOK ctxLitU 149631250000 0 ((leaves.drop 28968).take 32) 149831250000 0 = true :=
    take_step (n := 2) (t := 32) (b := 28970) rfl rfl ArealUCore.ArealUK.chunk_14484 s85
  have s83 : leavesOK ctxLitU 299237500000 1 ((leaves.drop 28966).take 34) 149831250000 0 = true :=
    take_step (n := 2) (t := 34) (b := 28968) rfl rfl ArealUCore.ArealUK.chunk_14483 s84
  have s82 : leavesOK ctxLitU 299212500000 1 ((leaves.drop 28964).take 36) 149831250000 0 = true :=
    take_step (n := 2) (t := 36) (b := 28966) rfl rfl ArealUCore.ArealUK.chunk_14482 s83
  have s81 : leavesOK ctxLitU 598375000000 2 ((leaves.drop 28962).take 38) 149831250000 0 = true :=
    take_step (n := 2) (t := 38) (b := 28964) rfl rfl ArealUCore.ArealUK.chunk_14481 s82
  have s80 : leavesOK ctxLitU 598325000000 2 ((leaves.drop 28960).take 40) 149831250000 0 = true :=
    take_step (n := 2) (t := 40) (b := 28962) rfl rfl ArealUCore.ArealUK.chunk_14480 s81
  have s79 : leavesOK ctxLitU 598275000000 2 ((leaves.drop 28958).take 42) 149831250000 0 = true :=
    take_step (n := 2) (t := 42) (b := 28960) rfl rfl ArealUCore.ArealUK.chunk_14479 s80
  have s78 : leavesOK ctxLitU 299100000000 1 ((leaves.drop 28956).take 44) 149831250000 0 = true :=
    take_step (n := 2) (t := 44) (b := 28958) rfl rfl ArealUCore.ArealUK.chunk_14478 s79
  have s77 : leavesOK ctxLitU 299050000000 1 ((leaves.drop 28954).take 46) 149831250000 0 = true :=
    take_step (n := 2) (t := 46) (b := 28956) rfl rfl ArealUCore.ArealUK.chunk_14477 s78
  have s76 : leavesOK ctxLitU 598050000000 2 ((leaves.drop 28952).take 48) 149831250000 0 = true :=
    take_step (n := 2) (t := 48) (b := 28954) rfl rfl ArealUCore.ArealUK.chunk_14476 s77
  have s75 : leavesOK ctxLitU 598000000000 2 ((leaves.drop 28950).take 50) 149831250000 0 = true :=
    take_step (n := 2) (t := 50) (b := 28952) rfl rfl ArealUCore.ArealUK.chunk_14475 s76
  have s74 : leavesOK ctxLitU 597950000000 2 ((leaves.drop 28948).take 52) 149831250000 0 = true :=
    take_step (n := 2) (t := 52) (b := 28950) rfl rfl ArealUCore.ArealUK.chunk_14474 s75
  have s73 : leavesOK ctxLitU 597900000000 2 ((leaves.drop 28946).take 54) 149831250000 0 = true :=
    take_step (n := 2) (t := 54) (b := 28948) rfl rfl ArealUCore.ArealUK.chunk_14473 s74
  have s72 : leavesOK ctxLitU 298925000000 1 ((leaves.drop 28944).take 56) 149831250000 0 = true :=
    take_step (n := 2) (t := 56) (b := 28946) rfl rfl ArealUCore.ArealUK.chunk_14472 s73
  have s71 : leavesOK ctxLitU 298900000000 1 ((leaves.drop 28942).take 58) 149831250000 0 = true :=
    take_step (n := 2) (t := 58) (b := 28944) rfl rfl ArealUCore.ArealUK.chunk_14471 s72
  have s70 : leavesOK ctxLitU 149437500000 0 ((leaves.drop 28940).take 60) 149831250000 0 = true :=
    take_step (n := 2) (t := 60) (b := 28942) rfl rfl ArealUCore.ArealUK.chunk_14470 s71
  have s69 : leavesOK ctxLitU 298862500000 1 ((leaves.drop 28938).take 62) 149831250000 0 = true :=
    take_step (n := 2) (t := 62) (b := 28940) rfl rfl ArealUCore.ArealUK.chunk_14469 s70
  have s68 : leavesOK ctxLitU 298850000000 1 ((leaves.drop 28936).take 64) 149831250000 0 = true :=
    take_step (n := 2) (t := 64) (b := 28938) rfl rfl ArealUCore.ArealUK.chunk_14468 s69
  have s67 : leavesOK ctxLitU 298825000000 1 ((leaves.drop 28934).take 66) 149831250000 0 = true :=
    take_step (n := 2) (t := 66) (b := 28936) rfl rfl ArealUCore.ArealUK.chunk_14467 s68
  have s66 : leavesOK ctxLitU 298800000000 1 ((leaves.drop 28932).take 68) 149831250000 0 = true :=
    take_step (n := 2) (t := 68) (b := 28934) rfl rfl ArealUCore.ArealUK.chunk_14466 s67
  have s65 : leavesOK ctxLitU 298775000000 1 ((leaves.drop 28930).take 70) 149831250000 0 = true :=
    take_step (n := 2) (t := 70) (b := 28932) rfl rfl ArealUCore.ArealUK.chunk_14465 s66
  have s64 : leavesOK ctxLitU 298750000000 1 ((leaves.drop 28928).take 72) 149831250000 0 = true :=
    take_step (n := 2) (t := 72) (b := 28930) rfl rfl ArealUCore.ArealUK.chunk_14464 s65
  have s63 : leavesOK ctxLitU 298737500000 1 ((leaves.drop 28926).take 74) 149831250000 0 = true :=
    take_step (n := 2) (t := 74) (b := 28928) rfl rfl ArealUCore.ArealUK.chunk_14463 s64
  have s62 : leavesOK ctxLitU 298725000000 1 ((leaves.drop 28924).take 76) 149831250000 0 = true :=
    take_step (n := 2) (t := 76) (b := 28926) rfl rfl ArealUCore.ArealUK.chunk_14462 s63
  have s61 : leavesOK ctxLitU 149350000000 0 ((leaves.drop 28922).take 78) 149831250000 0 = true :=
    take_step (n := 2) (t := 78) (b := 28924) rfl rfl ArealUCore.ArealUK.chunk_14461 s62
  have s60 : leavesOK ctxLitU 298675000000 1 ((leaves.drop 28920).take 80) 149831250000 0 = true :=
    take_step (n := 2) (t := 80) (b := 28922) rfl rfl ArealUCore.ArealUK.chunk_14460 s61
  have s59 : leavesOK ctxLitU 298650000000 1 ((leaves.drop 28918).take 82) 149831250000 0 = true :=
    take_step (n := 2) (t := 82) (b := 28920) rfl rfl ArealUCore.ArealUK.chunk_14459 s60
  have s58 : leavesOK ctxLitU 597225000000 2 ((leaves.drop 28916).take 84) 149831250000 0 = true :=
    take_step (n := 2) (t := 84) (b := 28918) rfl rfl ArealUCore.ArealUK.chunk_14458 s59
  have s57 : leavesOK ctxLitU 298587500000 1 ((leaves.drop 28914).take 86) 149831250000 0 = true :=
    take_step (n := 2) (t := 86) (b := 28916) rfl rfl ArealUCore.ArealUK.chunk_14457 s58
  have s56 : leavesOK ctxLitU 298562500000 1 ((leaves.drop 28912).take 88) 149831250000 0 = true :=
    take_step (n := 2) (t := 88) (b := 28914) rfl rfl ArealUCore.ArealUK.chunk_14456 s57
  have s55 : leavesOK ctxLitU 149268750000 0 ((leaves.drop 28910).take 90) 149831250000 0 = true :=
    take_step (n := 2) (t := 90) (b := 28912) rfl rfl ArealUCore.ArealUK.chunk_14455 s56
  have s54 : leavesOK ctxLitU 149256250000 0 ((leaves.drop 28908).take 92) 149831250000 0 = true :=
    take_step (n := 2) (t := 92) (b := 28910) rfl rfl ArealUCore.ArealUK.chunk_14454 s55
  have s53 : leavesOK ctxLitU 149243750000 0 ((leaves.drop 28906).take 94) 149831250000 0 = true :=
    take_step (n := 2) (t := 94) (b := 28908) rfl rfl ArealUCore.ArealUK.chunk_14453 s54
  have s52 : leavesOK ctxLitU 149231250000 0 ((leaves.drop 28904).take 96) 149831250000 0 = true :=
    take_step (n := 2) (t := 96) (b := 28906) rfl rfl ArealUCore.ArealUK.chunk_14452 s53
  have s51 : leavesOK ctxLitU 298437500000 1 ((leaves.drop 28902).take 98) 149831250000 0 = true :=
    take_step (n := 2) (t := 98) (b := 28904) rfl rfl ArealUCore.ArealUK.chunk_14451 s52
  have s50 : leavesOK ctxLitU 298412500000 1 ((leaves.drop 28900).take 100) 149831250000 0 = true :=
    take_step (n := 2) (t := 100) (b := 28902) rfl rfl ArealUCore.ArealUK.chunk_14450 s51
  have s49 : leavesOK ctxLitU 298387500000 1 ((leaves.drop 28898).take 102) 149831250000 0 = true :=
    take_step (n := 2) (t := 102) (b := 28900) rfl rfl ArealUCore.ArealUK.chunk_14449 s50
  have s48 : leavesOK ctxLitU 298362500000 1 ((leaves.drop 28896).take 104) 149831250000 0 = true :=
    take_step (n := 2) (t := 104) (b := 28898) rfl rfl ArealUCore.ArealUK.chunk_14448 s49
  have s47 : leavesOK ctxLitU 298343750000 1 ((leaves.drop 28894).take 106) 149831250000 0 = true :=
    take_step (n := 2) (t := 106) (b := 28896) rfl rfl ArealUCore.ArealUK.chunk_14447 s48
  have s46 : leavesOK ctxLitU 298331250000 1 ((leaves.drop 28892).take 108) 149831250000 0 = true :=
    take_step (n := 2) (t := 108) (b := 28894) rfl rfl ArealUCore.ArealUK.chunk_14446 s47
  have s45 : leavesOK ctxLitU 149156250000 0 ((leaves.drop 28890).take 110) 149831250000 0 = true :=
    take_step (n := 2) (t := 110) (b := 28892) rfl rfl ArealUCore.ArealUK.chunk_14445 s46
  have s44 : leavesOK ctxLitU 298287500000 1 ((leaves.drop 28888).take 112) 149831250000 0 = true :=
    take_step (n := 2) (t := 112) (b := 28890) rfl rfl ArealUCore.ArealUK.chunk_14444 s45
  have s43 : leavesOK ctxLitU 298262500000 1 ((leaves.drop 28886).take 114) 149831250000 0 = true :=
    take_step (n := 2) (t := 114) (b := 28888) rfl rfl ArealUCore.ArealUK.chunk_14443 s44
  have s42 : leavesOK ctxLitU 298225000000 1 ((leaves.drop 28884).take 116) 149831250000 0 = true :=
    take_step (n := 2) (t := 116) (b := 28886) rfl rfl ArealUCore.ArealUK.chunk_14442 s43
  have s41 : leavesOK ctxLitU 596400000000 2 ((leaves.drop 28882).take 118) 149831250000 0 = true :=
    take_step (n := 2) (t := 118) (b := 28884) rfl rfl ArealUCore.ArealUK.chunk_14441 s42
  have s40 : leavesOK ctxLitU 298175000000 1 ((leaves.drop 28880).take 120) 149831250000 0 = true :=
    take_step (n := 2) (t := 120) (b := 28882) rfl rfl ArealUCore.ArealUK.chunk_14440 s41
  have s39 : leavesOK ctxLitU 149068750000 0 ((leaves.drop 28878).take 122) 149831250000 0 = true :=
    take_step (n := 2) (t := 122) (b := 28880) rfl rfl ArealUCore.ArealUK.chunk_14439 s40
  have s38 : leavesOK ctxLitU 149056250000 0 ((leaves.drop 28876).take 124) 149831250000 0 = true :=
    take_step (n := 2) (t := 124) (b := 28878) rfl rfl ArealUCore.ArealUK.chunk_14438 s39
  have s37 : leavesOK ctxLitU 149043750000 0 ((leaves.drop 28874).take 126) 149831250000 0 = true :=
    take_step (n := 2) (t := 126) (b := 28876) rfl rfl ArealUCore.ArealUK.chunk_14437 s38
  have s36 : leavesOK ctxLitU 149031250000 0 ((leaves.drop 28872).take 128) 149831250000 0 = true :=
    take_step (n := 2) (t := 128) (b := 28874) rfl rfl ArealUCore.ArealUK.chunk_14436 s37
  have s35 : leavesOK ctxLitU 298037500000 1 ((leaves.drop 28870).take 130) 149831250000 0 = true :=
    take_step (n := 2) (t := 130) (b := 28872) rfl rfl ArealUCore.ArealUK.chunk_14435 s36
  have s34 : leavesOK ctxLitU 298012500000 1 ((leaves.drop 28868).take 132) 149831250000 0 = true :=
    take_step (n := 2) (t := 132) (b := 28870) rfl rfl ArealUCore.ArealUK.chunk_14434 s35
  have s33 : leavesOK ctxLitU 297987500000 1 ((leaves.drop 28866).take 134) 149831250000 0 = true :=
    take_step (n := 2) (t := 134) (b := 28868) rfl rfl ArealUCore.ArealUK.chunk_14433 s34
  have s32 : leavesOK ctxLitU 297962500000 1 ((leaves.drop 28864).take 136) 149831250000 0 = true :=
    take_step (n := 2) (t := 136) (b := 28866) rfl rfl ArealUCore.ArealUK.chunk_14432 s33
  have s31 : leavesOK ctxLitU 148968750000 0 ((leaves.drop 28862).take 138) 149831250000 0 = true :=
    take_step (n := 2) (t := 138) (b := 28864) rfl rfl ArealUCore.ArealUK.chunk_14431 s32
  have s30 : leavesOK ctxLitU 148956250000 0 ((leaves.drop 28860).take 140) 149831250000 0 = true :=
    take_step (n := 2) (t := 140) (b := 28862) rfl rfl ArealUCore.ArealUK.chunk_14430 s31
  have s29 : leavesOK ctxLitU 148943750000 0 ((leaves.drop 28858).take 142) 149831250000 0 = true :=
    take_step (n := 2) (t := 142) (b := 28860) rfl rfl ArealUCore.ArealUK.chunk_14429 s30
  have s28 : leavesOK ctxLitU 148931250000 0 ((leaves.drop 28856).take 144) 149831250000 0 = true :=
    take_step (n := 2) (t := 144) (b := 28858) rfl rfl ArealUCore.ArealUK.chunk_14428 s29
  have s27 : leavesOK ctxLitU 297837500000 1 ((leaves.drop 28854).take 146) 149831250000 0 = true :=
    take_step (n := 2) (t := 146) (b := 28856) rfl rfl ArealUCore.ArealUK.chunk_14427 s28
  have s26 : leavesOK ctxLitU 297812500000 1 ((leaves.drop 28852).take 148) 149831250000 0 = true :=
    take_step (n := 2) (t := 148) (b := 28854) rfl rfl ArealUCore.ArealUK.chunk_14426 s27
  have s25 : leavesOK ctxLitU 297787500000 1 ((leaves.drop 28850).take 150) 149831250000 0 = true :=
    take_step (n := 2) (t := 150) (b := 28852) rfl rfl ArealUCore.ArealUK.chunk_14425 s26
  have s24 : leavesOK ctxLitU 297762500000 1 ((leaves.drop 28848).take 152) 149831250000 0 = true :=
    take_step (n := 2) (t := 152) (b := 28850) rfl rfl ArealUCore.ArealUK.chunk_14424 s25
  have s23 : leavesOK ctxLitU 148868750000 0 ((leaves.drop 28846).take 154) 149831250000 0 = true :=
    take_step (n := 2) (t := 154) (b := 28848) rfl rfl ArealUCore.ArealUK.chunk_14423 s24
  have s22 : leavesOK ctxLitU 148856250000 0 ((leaves.drop 28844).take 156) 149831250000 0 = true :=
    take_step (n := 2) (t := 156) (b := 28846) rfl rfl ArealUCore.ArealUK.chunk_14422 s23
  have s21 : leavesOK ctxLitU 148843750000 0 ((leaves.drop 28842).take 158) 149831250000 0 = true :=
    take_step (n := 2) (t := 158) (b := 28844) rfl rfl ArealUCore.ArealUK.chunk_14421 s22
  have s20 : leavesOK ctxLitU 297668750000 1 ((leaves.drop 28840).take 160) 149831250000 0 = true :=
    take_step (n := 2) (t := 160) (b := 28842) rfl rfl ArealUCore.ArealUK.chunk_14420 s21
  have s19 : leavesOK ctxLitU 297656250000 1 ((leaves.drop 28838).take 162) 149831250000 0 = true :=
    take_step (n := 2) (t := 162) (b := 28840) rfl rfl ArealUCore.ArealUK.chunk_14419 s20
  have s18 : leavesOK ctxLitU 297637500000 1 ((leaves.drop 28836).take 164) 149831250000 0 = true :=
    take_step (n := 2) (t := 164) (b := 28838) rfl rfl ArealUCore.ArealUK.chunk_14418 s19
  have s17 : leavesOK ctxLitU 297612500000 1 ((leaves.drop 28834).take 166) 149831250000 0 = true :=
    take_step (n := 2) (t := 166) (b := 28836) rfl rfl ArealUCore.ArealUK.chunk_14417 s18
  have s16 : leavesOK ctxLitU 595175000000 2 ((leaves.drop 28832).take 168) 149831250000 0 = true :=
    take_step (n := 2) (t := 168) (b := 28834) rfl rfl ArealUCore.ArealUK.chunk_14416 s17
  have s15 : leavesOK ctxLitU 595125000000 2 ((leaves.drop 28830).take 170) 149831250000 0 = true :=
    take_step (n := 2) (t := 170) (b := 28832) rfl rfl ArealUCore.ArealUK.chunk_14415 s16
  have s14 : leavesOK ctxLitU 595075000000 2 ((leaves.drop 28828).take 172) 149831250000 0 = true :=
    take_step (n := 2) (t := 172) (b := 28830) rfl rfl ArealUCore.ArealUK.chunk_14414 s15
  have s13 : leavesOK ctxLitU 297500000000 1 ((leaves.drop 28826).take 174) 149831250000 0 = true :=
    take_step (n := 2) (t := 174) (b := 28828) rfl rfl ArealUCore.ArealUK.chunk_14413 s14
  have s12 : leavesOK ctxLitU 297450000000 1 ((leaves.drop 28824).take 176) 149831250000 0 = true :=
    take_step (n := 2) (t := 176) (b := 28826) rfl rfl ArealUCore.ArealUK.chunk_14412 s13
  have s11 : leavesOK ctxLitU 594850000000 2 ((leaves.drop 28822).take 178) 149831250000 0 = true :=
    take_step (n := 2) (t := 178) (b := 28824) rfl rfl ArealUCore.ArealUK.chunk_14411 s12
  have s10 : leavesOK ctxLitU 594800000000 2 ((leaves.drop 28820).take 180) 149831250000 0 = true :=
    take_step (n := 2) (t := 180) (b := 28822) rfl rfl ArealUCore.ArealUK.chunk_14410 s11
  have s9 : leavesOK ctxLitU 594762500000 2 ((leaves.drop 28818).take 182) 149831250000 0 = true :=
    take_step (n := 2) (t := 182) (b := 28820) rfl rfl ArealUCore.ArealUK.chunk_14409 s10
  have s8 : leavesOK ctxLitU 594737500000 2 ((leaves.drop 28816).take 184) 149831250000 0 = true :=
    take_step (n := 2) (t := 184) (b := 28818) rfl rfl ArealUCore.ArealUK.chunk_14408 s9
  have s7 : leavesOK ctxLitU 297350000000 1 ((leaves.drop 28814).take 186) 149831250000 0 = true :=
    take_step (n := 2) (t := 186) (b := 28816) rfl rfl ArealUCore.ArealUK.chunk_14407 s8
  have s6 : leavesOK ctxLitU 148662500000 0 ((leaves.drop 28812).take 188) 149831250000 0 = true :=
    take_step (n := 2) (t := 188) (b := 28814) rfl rfl ArealUCore.ArealUK.chunk_14406 s7
  have s5 : leavesOK ctxLitU 148650000000 0 ((leaves.drop 28810).take 190) 149831250000 0 = true :=
    take_step (n := 2) (t := 190) (b := 28812) rfl rfl ArealUCore.ArealUK.chunk_14405 s6
  have s4 : leavesOK ctxLitU 148637500000 0 ((leaves.drop 28808).take 192) 149831250000 0 = true :=
    take_step (n := 2) (t := 192) (b := 28810) rfl rfl ArealUCore.ArealUK.chunk_14404 s5
  have s3 : leavesOK ctxLitU 297262500000 1 ((leaves.drop 28806).take 194) 149831250000 0 = true :=
    take_step (n := 2) (t := 194) (b := 28808) rfl rfl ArealUCore.ArealUK.chunk_14403 s4
  have s2 : leavesOK ctxLitU 297250000000 1 ((leaves.drop 28804).take 196) 149831250000 0 = true :=
    take_step (n := 2) (t := 196) (b := 28806) rfl rfl ArealUCore.ArealUK.chunk_14402 s3
  have s1 : leavesOK ctxLitU 297225000000 1 ((leaves.drop 28802).take 198) 149831250000 0 = true :=
    take_step (n := 2) (t := 198) (b := 28804) rfl rfl ArealUCore.ArealUK.chunk_14401 s2
  have s0 : leavesOK ctxLitU 297200000000 1 ((leaves.drop 28800).take 200) 149831250000 0 = true :=
    take_step (n := 2) (t := 200) (b := 28802) rfl rfl ArealUCore.ArealUK.chunk_14400 s1
  exact s0

end Areal.UCert

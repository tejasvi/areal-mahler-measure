import ArealUK.Chunk6400
import ArealUK.Chunk6401
import ArealUK.Chunk6402
import ArealUK.Chunk6403
import ArealUK.Chunk6404
import ArealUK.Chunk6405
import ArealUK.Chunk6406
import ArealUK.Chunk6407
import ArealUK.Chunk6408
import ArealUK.Chunk6409
import ArealUK.Chunk6410
import ArealUK.Chunk6411
import ArealUK.Chunk6412
import ArealUK.Chunk6413
import ArealUK.Chunk6414
import ArealUK.Chunk6415
import ArealUK.Chunk6416
import ArealUK.Chunk6417
import ArealUK.Chunk6418
import ArealUK.Chunk6419
import ArealUK.Chunk6420
import ArealUK.Chunk6421
import ArealUK.Chunk6422
import ArealUK.Chunk6423
import ArealUK.Chunk6424
import ArealUK.Chunk6425
import ArealUK.Chunk6426
import ArealUK.Chunk6427
import ArealUK.Chunk6428
import ArealUK.Chunk6429
import ArealUK.Chunk6430
import ArealUK.Chunk6431
import ArealUK.Chunk6432
import ArealUK.Chunk6433
import ArealUK.Chunk6434
import ArealUK.Chunk6435
import ArealUK.Chunk6436
import ArealUK.Chunk6437
import ArealUK.Chunk6438
import ArealUK.Chunk6439
import ArealUK.Chunk6440
import ArealUK.Chunk6441
import ArealUK.Chunk6442
import ArealUK.Chunk6443
import ArealUK.Chunk6444
import ArealUK.Chunk6445
import ArealUK.Chunk6446
import ArealUK.Chunk6447
import ArealUK.Chunk6448
import ArealUK.Chunk6449
import ArealUK.Chunk6450
import ArealUK.Chunk6451
import ArealUK.Chunk6452
import ArealUK.Chunk6453
import ArealUK.Chunk6454
import ArealUK.Chunk6455
import ArealUK.Chunk6456
import ArealUK.Chunk6457
import ArealUK.Chunk6458
import ArealUK.Chunk6459
import ArealUK.Chunk6460
import ArealUK.Chunk6461
import ArealUK.Chunk6462
import ArealUK.Chunk6463
import ArealUK.Chunk6464
import ArealUK.Chunk6465
import ArealUK.Chunk6466
import ArealUK.Chunk6467
import ArealUK.Chunk6468
import ArealUK.Chunk6469
import ArealUK.Chunk6470
import ArealUK.Chunk6471
import ArealUK.Chunk6472
import ArealUK.Chunk6473
import ArealUK.Chunk6474
import ArealUK.Chunk6475
import ArealUK.Chunk6476
import ArealUK.Chunk6477
import ArealUK.Chunk6478
import ArealUK.Chunk6479
import ArealUK.Chunk6480
import ArealUK.Chunk6481
import ArealUK.Chunk6482
import ArealUK.Chunk6483
import ArealUK.Chunk6484
import ArealUK.Chunk6485
import ArealUK.Chunk6486
import ArealUK.Chunk6487
import ArealUK.Chunk6488
import ArealUK.Chunk6489
import ArealUK.Chunk6490
import ArealUK.Chunk6491
import ArealUK.Chunk6492
import ArealUK.Chunk6493
import ArealUK.Chunk6494
import ArealUK.Chunk6495
import ArealUK.Chunk6496
import ArealUK.Chunk6497
import ArealUK.Chunk6498
import ArealUK.Chunk6499
import Areal.UCert.LeavesKGen

/-! Group 64 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_64 : leavesOK ctxLitU 334525000000 3 ((leaves.drop 12800).take 200) 169762500000 2 = true := by
  have s99 := ArealUCore.ArealUK.chunk_6499
  have s98 : leavesOK ctxLitU 169712500000 2 ((leaves.drop 12996).take 4) 169762500000 2 = true :=
    take_step (n := 2) (t := 4) (b := 12998) rfl rfl ArealUCore.ArealUK.chunk_6498 s99
  have s97 : leavesOK ctxLitU 339375000000 3 ((leaves.drop 12994).take 6) 169762500000 2 = true :=
    take_step (n := 2) (t := 6) (b := 12996) rfl rfl ArealUCore.ArealUK.chunk_6497 s98
  have s96 : leavesOK ctxLitU 339325000000 3 ((leaves.drop 12992).take 8) 169762500000 2 = true :=
    take_step (n := 2) (t := 8) (b := 12994) rfl rfl ArealUCore.ArealUK.chunk_6496 s97
  have s95 : leavesOK ctxLitU 339275000000 3 ((leaves.drop 12990).take 10) 169762500000 2 = true :=
    take_step (n := 2) (t := 10) (b := 12992) rfl rfl ArealUCore.ArealUK.chunk_6495 s96
  have s94 : leavesOK ctxLitU 339225000000 3 ((leaves.drop 12988).take 12) 169762500000 2 = true :=
    take_step (n := 2) (t := 12) (b := 12990) rfl rfl ArealUCore.ArealUK.chunk_6494 s95
  have s93 : leavesOK ctxLitU 339175000000 3 ((leaves.drop 12986).take 14) 169762500000 2 = true :=
    take_step (n := 2) (t := 14) (b := 12988) rfl rfl ArealUCore.ArealUK.chunk_6493 s94
  have s92 : leavesOK ctxLitU 339125000000 3 ((leaves.drop 12984).take 16) 169762500000 2 = true :=
    take_step (n := 2) (t := 16) (b := 12986) rfl rfl ArealUCore.ArealUK.chunk_6492 s93
  have s91 : leavesOK ctxLitU 339075000000 3 ((leaves.drop 12982).take 18) 169762500000 2 = true :=
    take_step (n := 2) (t := 18) (b := 12984) rfl rfl ArealUCore.ArealUK.chunk_6491 s92
  have s90 : leavesOK ctxLitU 339025000000 3 ((leaves.drop 12980).take 20) 169762500000 2 = true :=
    take_step (n := 2) (t := 20) (b := 12982) rfl rfl ArealUCore.ArealUK.chunk_6490 s91
  have s89 : leavesOK ctxLitU 338975000000 3 ((leaves.drop 12978).take 22) 169762500000 2 = true :=
    take_step (n := 2) (t := 22) (b := 12980) rfl rfl ArealUCore.ArealUK.chunk_6489 s90
  have s88 : leavesOK ctxLitU 338925000000 3 ((leaves.drop 12976).take 24) 169762500000 2 = true :=
    take_step (n := 2) (t := 24) (b := 12978) rfl rfl ArealUCore.ArealUK.chunk_6488 s89
  have s87 : leavesOK ctxLitU 338875000000 3 ((leaves.drop 12974).take 26) 169762500000 2 = true :=
    take_step (n := 2) (t := 26) (b := 12976) rfl rfl ArealUCore.ArealUK.chunk_6487 s88
  have s86 : leavesOK ctxLitU 338825000000 3 ((leaves.drop 12972).take 28) 169762500000 2 = true :=
    take_step (n := 2) (t := 28) (b := 12974) rfl rfl ArealUCore.ArealUK.chunk_6486 s87
  have s85 : leavesOK ctxLitU 338775000000 3 ((leaves.drop 12970).take 30) 169762500000 2 = true :=
    take_step (n := 2) (t := 30) (b := 12972) rfl rfl ArealUCore.ArealUK.chunk_6485 s86
  have s84 : leavesOK ctxLitU 338725000000 3 ((leaves.drop 12968).take 32) 169762500000 2 = true :=
    take_step (n := 2) (t := 32) (b := 12970) rfl rfl ArealUCore.ArealUK.chunk_6484 s85
  have s83 : leavesOK ctxLitU 338675000000 3 ((leaves.drop 12966).take 34) 169762500000 2 = true :=
    take_step (n := 2) (t := 34) (b := 12968) rfl rfl ArealUCore.ArealUK.chunk_6483 s84
  have s82 : leavesOK ctxLitU 338625000000 3 ((leaves.drop 12964).take 36) 169762500000 2 = true :=
    take_step (n := 2) (t := 36) (b := 12966) rfl rfl ArealUCore.ArealUK.chunk_6482 s83
  have s81 : leavesOK ctxLitU 338575000000 3 ((leaves.drop 12962).take 38) 169762500000 2 = true :=
    take_step (n := 2) (t := 38) (b := 12964) rfl rfl ArealUCore.ArealUK.chunk_6481 s82
  have s80 : leavesOK ctxLitU 338525000000 3 ((leaves.drop 12960).take 40) 169762500000 2 = true :=
    take_step (n := 2) (t := 40) (b := 12962) rfl rfl ArealUCore.ArealUK.chunk_6480 s81
  have s79 : leavesOK ctxLitU 338475000000 3 ((leaves.drop 12958).take 42) 169762500000 2 = true :=
    take_step (n := 2) (t := 42) (b := 12960) rfl rfl ArealUCore.ArealUK.chunk_6479 s80
  have s78 : leavesOK ctxLitU 338425000000 3 ((leaves.drop 12956).take 44) 169762500000 2 = true :=
    take_step (n := 2) (t := 44) (b := 12958) rfl rfl ArealUCore.ArealUK.chunk_6478 s79
  have s77 : leavesOK ctxLitU 338375000000 3 ((leaves.drop 12954).take 46) 169762500000 2 = true :=
    take_step (n := 2) (t := 46) (b := 12956) rfl rfl ArealUCore.ArealUK.chunk_6477 s78
  have s76 : leavesOK ctxLitU 338325000000 3 ((leaves.drop 12952).take 48) 169762500000 2 = true :=
    take_step (n := 2) (t := 48) (b := 12954) rfl rfl ArealUCore.ArealUK.chunk_6476 s77
  have s75 : leavesOK ctxLitU 338275000000 3 ((leaves.drop 12950).take 50) 169762500000 2 = true :=
    take_step (n := 2) (t := 50) (b := 12952) rfl rfl ArealUCore.ArealUK.chunk_6475 s76
  have s74 : leavesOK ctxLitU 338225000000 3 ((leaves.drop 12948).take 52) 169762500000 2 = true :=
    take_step (n := 2) (t := 52) (b := 12950) rfl rfl ArealUCore.ArealUK.chunk_6474 s75
  have s73 : leavesOK ctxLitU 338175000000 3 ((leaves.drop 12946).take 54) 169762500000 2 = true :=
    take_step (n := 2) (t := 54) (b := 12948) rfl rfl ArealUCore.ArealUK.chunk_6473 s74
  have s72 : leavesOK ctxLitU 338125000000 3 ((leaves.drop 12944).take 56) 169762500000 2 = true :=
    take_step (n := 2) (t := 56) (b := 12946) rfl rfl ArealUCore.ArealUK.chunk_6472 s73
  have s71 : leavesOK ctxLitU 338075000000 3 ((leaves.drop 12942).take 58) 169762500000 2 = true :=
    take_step (n := 2) (t := 58) (b := 12944) rfl rfl ArealUCore.ArealUK.chunk_6471 s72
  have s70 : leavesOK ctxLitU 338025000000 3 ((leaves.drop 12940).take 60) 169762500000 2 = true :=
    take_step (n := 2) (t := 60) (b := 12942) rfl rfl ArealUCore.ArealUK.chunk_6470 s71
  have s69 : leavesOK ctxLitU 337975000000 3 ((leaves.drop 12938).take 62) 169762500000 2 = true :=
    take_step (n := 2) (t := 62) (b := 12940) rfl rfl ArealUCore.ArealUK.chunk_6469 s70
  have s68 : leavesOK ctxLitU 337925000000 3 ((leaves.drop 12936).take 64) 169762500000 2 = true :=
    take_step (n := 2) (t := 64) (b := 12938) rfl rfl ArealUCore.ArealUK.chunk_6468 s69
  have s67 : leavesOK ctxLitU 337875000000 3 ((leaves.drop 12934).take 66) 169762500000 2 = true :=
    take_step (n := 2) (t := 66) (b := 12936) rfl rfl ArealUCore.ArealUK.chunk_6467 s68
  have s66 : leavesOK ctxLitU 337825000000 3 ((leaves.drop 12932).take 68) 169762500000 2 = true :=
    take_step (n := 2) (t := 68) (b := 12934) rfl rfl ArealUCore.ArealUK.chunk_6466 s67
  have s65 : leavesOK ctxLitU 337775000000 3 ((leaves.drop 12930).take 70) 169762500000 2 = true :=
    take_step (n := 2) (t := 70) (b := 12932) rfl rfl ArealUCore.ArealUK.chunk_6465 s66
  have s64 : leavesOK ctxLitU 337725000000 3 ((leaves.drop 12928).take 72) 169762500000 2 = true :=
    take_step (n := 2) (t := 72) (b := 12930) rfl rfl ArealUCore.ArealUK.chunk_6464 s65
  have s63 : leavesOK ctxLitU 337675000000 3 ((leaves.drop 12926).take 74) 169762500000 2 = true :=
    take_step (n := 2) (t := 74) (b := 12928) rfl rfl ArealUCore.ArealUK.chunk_6463 s64
  have s62 : leavesOK ctxLitU 337625000000 3 ((leaves.drop 12924).take 76) 169762500000 2 = true :=
    take_step (n := 2) (t := 76) (b := 12926) rfl rfl ArealUCore.ArealUK.chunk_6462 s63
  have s61 : leavesOK ctxLitU 337575000000 3 ((leaves.drop 12922).take 78) 169762500000 2 = true :=
    take_step (n := 2) (t := 78) (b := 12924) rfl rfl ArealUCore.ArealUK.chunk_6461 s62
  have s60 : leavesOK ctxLitU 337525000000 3 ((leaves.drop 12920).take 80) 169762500000 2 = true :=
    take_step (n := 2) (t := 80) (b := 12922) rfl rfl ArealUCore.ArealUK.chunk_6460 s61
  have s59 : leavesOK ctxLitU 337475000000 3 ((leaves.drop 12918).take 82) 169762500000 2 = true :=
    take_step (n := 2) (t := 82) (b := 12920) rfl rfl ArealUCore.ArealUK.chunk_6459 s60
  have s58 : leavesOK ctxLitU 337425000000 3 ((leaves.drop 12916).take 84) 169762500000 2 = true :=
    take_step (n := 2) (t := 84) (b := 12918) rfl rfl ArealUCore.ArealUK.chunk_6458 s59
  have s57 : leavesOK ctxLitU 337375000000 3 ((leaves.drop 12914).take 86) 169762500000 2 = true :=
    take_step (n := 2) (t := 86) (b := 12916) rfl rfl ArealUCore.ArealUK.chunk_6457 s58
  have s56 : leavesOK ctxLitU 337325000000 3 ((leaves.drop 12912).take 88) 169762500000 2 = true :=
    take_step (n := 2) (t := 88) (b := 12914) rfl rfl ArealUCore.ArealUK.chunk_6456 s57
  have s55 : leavesOK ctxLitU 337275000000 3 ((leaves.drop 12910).take 90) 169762500000 2 = true :=
    take_step (n := 2) (t := 90) (b := 12912) rfl rfl ArealUCore.ArealUK.chunk_6455 s56
  have s54 : leavesOK ctxLitU 337225000000 3 ((leaves.drop 12908).take 92) 169762500000 2 = true :=
    take_step (n := 2) (t := 92) (b := 12910) rfl rfl ArealUCore.ArealUK.chunk_6454 s55
  have s53 : leavesOK ctxLitU 337175000000 3 ((leaves.drop 12906).take 94) 169762500000 2 = true :=
    take_step (n := 2) (t := 94) (b := 12908) rfl rfl ArealUCore.ArealUK.chunk_6453 s54
  have s52 : leavesOK ctxLitU 337125000000 3 ((leaves.drop 12904).take 96) 169762500000 2 = true :=
    take_step (n := 2) (t := 96) (b := 12906) rfl rfl ArealUCore.ArealUK.chunk_6452 s53
  have s51 : leavesOK ctxLitU 337075000000 3 ((leaves.drop 12902).take 98) 169762500000 2 = true :=
    take_step (n := 2) (t := 98) (b := 12904) rfl rfl ArealUCore.ArealUK.chunk_6451 s52
  have s50 : leavesOK ctxLitU 337025000000 3 ((leaves.drop 12900).take 100) 169762500000 2 = true :=
    take_step (n := 2) (t := 100) (b := 12902) rfl rfl ArealUCore.ArealUK.chunk_6450 s51
  have s49 : leavesOK ctxLitU 336975000000 3 ((leaves.drop 12898).take 102) 169762500000 2 = true :=
    take_step (n := 2) (t := 102) (b := 12900) rfl rfl ArealUCore.ArealUK.chunk_6449 s50
  have s48 : leavesOK ctxLitU 336925000000 3 ((leaves.drop 12896).take 104) 169762500000 2 = true :=
    take_step (n := 2) (t := 104) (b := 12898) rfl rfl ArealUCore.ArealUK.chunk_6448 s49
  have s47 : leavesOK ctxLitU 336875000000 3 ((leaves.drop 12894).take 106) 169762500000 2 = true :=
    take_step (n := 2) (t := 106) (b := 12896) rfl rfl ArealUCore.ArealUK.chunk_6447 s48
  have s46 : leavesOK ctxLitU 336825000000 3 ((leaves.drop 12892).take 108) 169762500000 2 = true :=
    take_step (n := 2) (t := 108) (b := 12894) rfl rfl ArealUCore.ArealUK.chunk_6446 s47
  have s45 : leavesOK ctxLitU 336775000000 3 ((leaves.drop 12890).take 110) 169762500000 2 = true :=
    take_step (n := 2) (t := 110) (b := 12892) rfl rfl ArealUCore.ArealUK.chunk_6445 s46
  have s44 : leavesOK ctxLitU 336725000000 3 ((leaves.drop 12888).take 112) 169762500000 2 = true :=
    take_step (n := 2) (t := 112) (b := 12890) rfl rfl ArealUCore.ArealUK.chunk_6444 s45
  have s43 : leavesOK ctxLitU 336675000000 3 ((leaves.drop 12886).take 114) 169762500000 2 = true :=
    take_step (n := 2) (t := 114) (b := 12888) rfl rfl ArealUCore.ArealUK.chunk_6443 s44
  have s42 : leavesOK ctxLitU 336625000000 3 ((leaves.drop 12884).take 116) 169762500000 2 = true :=
    take_step (n := 2) (t := 116) (b := 12886) rfl rfl ArealUCore.ArealUK.chunk_6442 s43
  have s41 : leavesOK ctxLitU 336575000000 3 ((leaves.drop 12882).take 118) 169762500000 2 = true :=
    take_step (n := 2) (t := 118) (b := 12884) rfl rfl ArealUCore.ArealUK.chunk_6441 s42
  have s40 : leavesOK ctxLitU 336525000000 3 ((leaves.drop 12880).take 120) 169762500000 2 = true :=
    take_step (n := 2) (t := 120) (b := 12882) rfl rfl ArealUCore.ArealUK.chunk_6440 s41
  have s39 : leavesOK ctxLitU 336475000000 3 ((leaves.drop 12878).take 122) 169762500000 2 = true :=
    take_step (n := 2) (t := 122) (b := 12880) rfl rfl ArealUCore.ArealUK.chunk_6439 s40
  have s38 : leavesOK ctxLitU 336425000000 3 ((leaves.drop 12876).take 124) 169762500000 2 = true :=
    take_step (n := 2) (t := 124) (b := 12878) rfl rfl ArealUCore.ArealUK.chunk_6438 s39
  have s37 : leavesOK ctxLitU 336375000000 3 ((leaves.drop 12874).take 126) 169762500000 2 = true :=
    take_step (n := 2) (t := 126) (b := 12876) rfl rfl ArealUCore.ArealUK.chunk_6437 s38
  have s36 : leavesOK ctxLitU 336325000000 3 ((leaves.drop 12872).take 128) 169762500000 2 = true :=
    take_step (n := 2) (t := 128) (b := 12874) rfl rfl ArealUCore.ArealUK.chunk_6436 s37
  have s35 : leavesOK ctxLitU 336275000000 3 ((leaves.drop 12870).take 130) 169762500000 2 = true :=
    take_step (n := 2) (t := 130) (b := 12872) rfl rfl ArealUCore.ArealUK.chunk_6435 s36
  have s34 : leavesOK ctxLitU 336225000000 3 ((leaves.drop 12868).take 132) 169762500000 2 = true :=
    take_step (n := 2) (t := 132) (b := 12870) rfl rfl ArealUCore.ArealUK.chunk_6434 s35
  have s33 : leavesOK ctxLitU 336175000000 3 ((leaves.drop 12866).take 134) 169762500000 2 = true :=
    take_step (n := 2) (t := 134) (b := 12868) rfl rfl ArealUCore.ArealUK.chunk_6433 s34
  have s32 : leavesOK ctxLitU 336125000000 3 ((leaves.drop 12864).take 136) 169762500000 2 = true :=
    take_step (n := 2) (t := 136) (b := 12866) rfl rfl ArealUCore.ArealUK.chunk_6432 s33
  have s31 : leavesOK ctxLitU 336075000000 3 ((leaves.drop 12862).take 138) 169762500000 2 = true :=
    take_step (n := 2) (t := 138) (b := 12864) rfl rfl ArealUCore.ArealUK.chunk_6431 s32
  have s30 : leavesOK ctxLitU 336025000000 3 ((leaves.drop 12860).take 140) 169762500000 2 = true :=
    take_step (n := 2) (t := 140) (b := 12862) rfl rfl ArealUCore.ArealUK.chunk_6430 s31
  have s29 : leavesOK ctxLitU 335975000000 3 ((leaves.drop 12858).take 142) 169762500000 2 = true :=
    take_step (n := 2) (t := 142) (b := 12860) rfl rfl ArealUCore.ArealUK.chunk_6429 s30
  have s28 : leavesOK ctxLitU 335925000000 3 ((leaves.drop 12856).take 144) 169762500000 2 = true :=
    take_step (n := 2) (t := 144) (b := 12858) rfl rfl ArealUCore.ArealUK.chunk_6428 s29
  have s27 : leavesOK ctxLitU 335875000000 3 ((leaves.drop 12854).take 146) 169762500000 2 = true :=
    take_step (n := 2) (t := 146) (b := 12856) rfl rfl ArealUCore.ArealUK.chunk_6427 s28
  have s26 : leavesOK ctxLitU 335825000000 3 ((leaves.drop 12852).take 148) 169762500000 2 = true :=
    take_step (n := 2) (t := 148) (b := 12854) rfl rfl ArealUCore.ArealUK.chunk_6426 s27
  have s25 : leavesOK ctxLitU 335775000000 3 ((leaves.drop 12850).take 150) 169762500000 2 = true :=
    take_step (n := 2) (t := 150) (b := 12852) rfl rfl ArealUCore.ArealUK.chunk_6425 s26
  have s24 : leavesOK ctxLitU 335725000000 3 ((leaves.drop 12848).take 152) 169762500000 2 = true :=
    take_step (n := 2) (t := 152) (b := 12850) rfl rfl ArealUCore.ArealUK.chunk_6424 s25
  have s23 : leavesOK ctxLitU 335675000000 3 ((leaves.drop 12846).take 154) 169762500000 2 = true :=
    take_step (n := 2) (t := 154) (b := 12848) rfl rfl ArealUCore.ArealUK.chunk_6423 s24
  have s22 : leavesOK ctxLitU 335625000000 3 ((leaves.drop 12844).take 156) 169762500000 2 = true :=
    take_step (n := 2) (t := 156) (b := 12846) rfl rfl ArealUCore.ArealUK.chunk_6422 s23
  have s21 : leavesOK ctxLitU 335575000000 3 ((leaves.drop 12842).take 158) 169762500000 2 = true :=
    take_step (n := 2) (t := 158) (b := 12844) rfl rfl ArealUCore.ArealUK.chunk_6421 s22
  have s20 : leavesOK ctxLitU 335525000000 3 ((leaves.drop 12840).take 160) 169762500000 2 = true :=
    take_step (n := 2) (t := 160) (b := 12842) rfl rfl ArealUCore.ArealUK.chunk_6420 s21
  have s19 : leavesOK ctxLitU 335475000000 3 ((leaves.drop 12838).take 162) 169762500000 2 = true :=
    take_step (n := 2) (t := 162) (b := 12840) rfl rfl ArealUCore.ArealUK.chunk_6419 s20
  have s18 : leavesOK ctxLitU 335425000000 3 ((leaves.drop 12836).take 164) 169762500000 2 = true :=
    take_step (n := 2) (t := 164) (b := 12838) rfl rfl ArealUCore.ArealUK.chunk_6418 s19
  have s17 : leavesOK ctxLitU 335375000000 3 ((leaves.drop 12834).take 166) 169762500000 2 = true :=
    take_step (n := 2) (t := 166) (b := 12836) rfl rfl ArealUCore.ArealUK.chunk_6417 s18
  have s16 : leavesOK ctxLitU 335325000000 3 ((leaves.drop 12832).take 168) 169762500000 2 = true :=
    take_step (n := 2) (t := 168) (b := 12834) rfl rfl ArealUCore.ArealUK.chunk_6416 s17
  have s15 : leavesOK ctxLitU 335275000000 3 ((leaves.drop 12830).take 170) 169762500000 2 = true :=
    take_step (n := 2) (t := 170) (b := 12832) rfl rfl ArealUCore.ArealUK.chunk_6415 s16
  have s14 : leavesOK ctxLitU 335225000000 3 ((leaves.drop 12828).take 172) 169762500000 2 = true :=
    take_step (n := 2) (t := 172) (b := 12830) rfl rfl ArealUCore.ArealUK.chunk_6414 s15
  have s13 : leavesOK ctxLitU 335175000000 3 ((leaves.drop 12826).take 174) 169762500000 2 = true :=
    take_step (n := 2) (t := 174) (b := 12828) rfl rfl ArealUCore.ArealUK.chunk_6413 s14
  have s12 : leavesOK ctxLitU 335125000000 3 ((leaves.drop 12824).take 176) 169762500000 2 = true :=
    take_step (n := 2) (t := 176) (b := 12826) rfl rfl ArealUCore.ArealUK.chunk_6412 s13
  have s11 : leavesOK ctxLitU 335075000000 3 ((leaves.drop 12822).take 178) 169762500000 2 = true :=
    take_step (n := 2) (t := 178) (b := 12824) rfl rfl ArealUCore.ArealUK.chunk_6411 s12
  have s10 : leavesOK ctxLitU 335025000000 3 ((leaves.drop 12820).take 180) 169762500000 2 = true :=
    take_step (n := 2) (t := 180) (b := 12822) rfl rfl ArealUCore.ArealUK.chunk_6410 s11
  have s9 : leavesOK ctxLitU 334975000000 3 ((leaves.drop 12818).take 182) 169762500000 2 = true :=
    take_step (n := 2) (t := 182) (b := 12820) rfl rfl ArealUCore.ArealUK.chunk_6409 s10
  have s8 : leavesOK ctxLitU 334925000000 3 ((leaves.drop 12816).take 184) 169762500000 2 = true :=
    take_step (n := 2) (t := 184) (b := 12818) rfl rfl ArealUCore.ArealUK.chunk_6408 s9
  have s7 : leavesOK ctxLitU 334875000000 3 ((leaves.drop 12814).take 186) 169762500000 2 = true :=
    take_step (n := 2) (t := 186) (b := 12816) rfl rfl ArealUCore.ArealUK.chunk_6407 s8
  have s6 : leavesOK ctxLitU 334825000000 3 ((leaves.drop 12812).take 188) 169762500000 2 = true :=
    take_step (n := 2) (t := 188) (b := 12814) rfl rfl ArealUCore.ArealUK.chunk_6406 s7
  have s5 : leavesOK ctxLitU 334775000000 3 ((leaves.drop 12810).take 190) 169762500000 2 = true :=
    take_step (n := 2) (t := 190) (b := 12812) rfl rfl ArealUCore.ArealUK.chunk_6405 s6
  have s4 : leavesOK ctxLitU 334725000000 3 ((leaves.drop 12808).take 192) 169762500000 2 = true :=
    take_step (n := 2) (t := 192) (b := 12810) rfl rfl ArealUCore.ArealUK.chunk_6404 s5
  have s3 : leavesOK ctxLitU 334675000000 3 ((leaves.drop 12806).take 194) 169762500000 2 = true :=
    take_step (n := 2) (t := 194) (b := 12808) rfl rfl ArealUCore.ArealUK.chunk_6403 s4
  have s2 : leavesOK ctxLitU 334625000000 3 ((leaves.drop 12804).take 196) 169762500000 2 = true :=
    take_step (n := 2) (t := 196) (b := 12806) rfl rfl ArealUCore.ArealUK.chunk_6402 s3
  have s1 : leavesOK ctxLitU 334575000000 3 ((leaves.drop 12802).take 198) 169762500000 2 = true :=
    take_step (n := 2) (t := 198) (b := 12804) rfl rfl ArealUCore.ArealUK.chunk_6401 s2
  have s0 : leavesOK ctxLitU 334525000000 3 ((leaves.drop 12800).take 200) 169762500000 2 = true :=
    take_step (n := 2) (t := 200) (b := 12802) rfl rfl ArealUCore.ArealUK.chunk_6400 s1
  exact s0

end Areal.UCert

import ArealUK.Chunk9400
import ArealUK.Chunk9401
import ArealUK.Chunk9402
import ArealUK.Chunk9403
import ArealUK.Chunk9404
import ArealUK.Chunk9405
import ArealUK.Chunk9406
import ArealUK.Chunk9407
import ArealUK.Chunk9408
import ArealUK.Chunk9409
import ArealUK.Chunk9410
import ArealUK.Chunk9411
import ArealUK.Chunk9412
import ArealUK.Chunk9413
import ArealUK.Chunk9414
import ArealUK.Chunk9415
import ArealUK.Chunk9416
import ArealUK.Chunk9417
import ArealUK.Chunk9418
import ArealUK.Chunk9419
import ArealUK.Chunk9420
import ArealUK.Chunk9421
import ArealUK.Chunk9422
import ArealUK.Chunk9423
import ArealUK.Chunk9424
import ArealUK.Chunk9425
import ArealUK.Chunk9426
import ArealUK.Chunk9427
import ArealUK.Chunk9428
import ArealUK.Chunk9429
import ArealUK.Chunk9430
import ArealUK.Chunk9431
import ArealUK.Chunk9432
import ArealUK.Chunk9433
import ArealUK.Chunk9434
import ArealUK.Chunk9435
import ArealUK.Chunk9436
import ArealUK.Chunk9437
import ArealUK.Chunk9438
import ArealUK.Chunk9439
import ArealUK.Chunk9440
import ArealUK.Chunk9441
import ArealUK.Chunk9442
import ArealUK.Chunk9443
import ArealUK.Chunk9444
import ArealUK.Chunk9445
import ArealUK.Chunk9446
import ArealUK.Chunk9447
import ArealUK.Chunk9448
import ArealUK.Chunk9449
import ArealUK.Chunk9450
import ArealUK.Chunk9451
import ArealUK.Chunk9452
import ArealUK.Chunk9453
import ArealUK.Chunk9454
import ArealUK.Chunk9455
import ArealUK.Chunk9456
import ArealUK.Chunk9457
import ArealUK.Chunk9458
import ArealUK.Chunk9459
import ArealUK.Chunk9460
import ArealUK.Chunk9461
import ArealUK.Chunk9462
import ArealUK.Chunk9463
import ArealUK.Chunk9464
import ArealUK.Chunk9465
import ArealUK.Chunk9466
import ArealUK.Chunk9467
import ArealUK.Chunk9468
import ArealUK.Chunk9469
import ArealUK.Chunk9470
import ArealUK.Chunk9471
import ArealUK.Chunk9472
import ArealUK.Chunk9473
import ArealUK.Chunk9474
import ArealUK.Chunk9475
import ArealUK.Chunk9476
import ArealUK.Chunk9477
import ArealUK.Chunk9478
import ArealUK.Chunk9479
import ArealUK.Chunk9480
import ArealUK.Chunk9481
import ArealUK.Chunk9482
import ArealUK.Chunk9483
import ArealUK.Chunk9484
import ArealUK.Chunk9485
import ArealUK.Chunk9486
import ArealUK.Chunk9487
import ArealUK.Chunk9488
import ArealUK.Chunk9489
import ArealUK.Chunk9490
import ArealUK.Chunk9491
import ArealUK.Chunk9492
import ArealUK.Chunk9493
import ArealUK.Chunk9494
import ArealUK.Chunk9495
import ArealUK.Chunk9496
import ArealUK.Chunk9497
import ArealUK.Chunk9498
import ArealUK.Chunk9499
import Areal.UCert.LeavesKGen

/-! Group 94 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_94 : leavesOK ctxLitU 324875000000 2 ((leaves.drop 18800).take 200) 329875000000 2 = true := by
  have s99 := ArealUCore.ArealUK.chunk_9499
  have s98 : leavesOK ctxLitU 329775000000 2 ((leaves.drop 18996).take 4) 329875000000 2 = true :=
    take_step (n := 2) (t := 4) (b := 18998) rfl rfl ArealUCore.ArealUK.chunk_9498 s99
  have s97 : leavesOK ctxLitU 329725000000 2 ((leaves.drop 18994).take 6) 329875000000 2 = true :=
    take_step (n := 2) (t := 6) (b := 18996) rfl rfl ArealUCore.ArealUK.chunk_9497 s98
  have s96 : leavesOK ctxLitU 329675000000 2 ((leaves.drop 18992).take 8) 329875000000 2 = true :=
    take_step (n := 2) (t := 8) (b := 18994) rfl rfl ArealUCore.ArealUK.chunk_9496 s97
  have s95 : leavesOK ctxLitU 329625000000 2 ((leaves.drop 18990).take 10) 329875000000 2 = true :=
    take_step (n := 2) (t := 10) (b := 18992) rfl rfl ArealUCore.ArealUK.chunk_9495 s96
  have s94 : leavesOK ctxLitU 329575000000 2 ((leaves.drop 18988).take 12) 329875000000 2 = true :=
    take_step (n := 2) (t := 12) (b := 18990) rfl rfl ArealUCore.ArealUK.chunk_9494 s95
  have s93 : leavesOK ctxLitU 329525000000 2 ((leaves.drop 18986).take 14) 329875000000 2 = true :=
    take_step (n := 2) (t := 14) (b := 18988) rfl rfl ArealUCore.ArealUK.chunk_9493 s94
  have s92 : leavesOK ctxLitU 329475000000 2 ((leaves.drop 18984).take 16) 329875000000 2 = true :=
    take_step (n := 2) (t := 16) (b := 18986) rfl rfl ArealUCore.ArealUK.chunk_9492 s93
  have s91 : leavesOK ctxLitU 329425000000 2 ((leaves.drop 18982).take 18) 329875000000 2 = true :=
    take_step (n := 2) (t := 18) (b := 18984) rfl rfl ArealUCore.ArealUK.chunk_9491 s92
  have s90 : leavesOK ctxLitU 329375000000 2 ((leaves.drop 18980).take 20) 329875000000 2 = true :=
    take_step (n := 2) (t := 20) (b := 18982) rfl rfl ArealUCore.ArealUK.chunk_9490 s91
  have s89 : leavesOK ctxLitU 329325000000 2 ((leaves.drop 18978).take 22) 329875000000 2 = true :=
    take_step (n := 2) (t := 22) (b := 18980) rfl rfl ArealUCore.ArealUK.chunk_9489 s90
  have s88 : leavesOK ctxLitU 329275000000 2 ((leaves.drop 18976).take 24) 329875000000 2 = true :=
    take_step (n := 2) (t := 24) (b := 18978) rfl rfl ArealUCore.ArealUK.chunk_9488 s89
  have s87 : leavesOK ctxLitU 329225000000 2 ((leaves.drop 18974).take 26) 329875000000 2 = true :=
    take_step (n := 2) (t := 26) (b := 18976) rfl rfl ArealUCore.ArealUK.chunk_9487 s88
  have s86 : leavesOK ctxLitU 329175000000 2 ((leaves.drop 18972).take 28) 329875000000 2 = true :=
    take_step (n := 2) (t := 28) (b := 18974) rfl rfl ArealUCore.ArealUK.chunk_9486 s87
  have s85 : leavesOK ctxLitU 329125000000 2 ((leaves.drop 18970).take 30) 329875000000 2 = true :=
    take_step (n := 2) (t := 30) (b := 18972) rfl rfl ArealUCore.ArealUK.chunk_9485 s86
  have s84 : leavesOK ctxLitU 329075000000 2 ((leaves.drop 18968).take 32) 329875000000 2 = true :=
    take_step (n := 2) (t := 32) (b := 18970) rfl rfl ArealUCore.ArealUK.chunk_9484 s85
  have s83 : leavesOK ctxLitU 329025000000 2 ((leaves.drop 18966).take 34) 329875000000 2 = true :=
    take_step (n := 2) (t := 34) (b := 18968) rfl rfl ArealUCore.ArealUK.chunk_9483 s84
  have s82 : leavesOK ctxLitU 328975000000 2 ((leaves.drop 18964).take 36) 329875000000 2 = true :=
    take_step (n := 2) (t := 36) (b := 18966) rfl rfl ArealUCore.ArealUK.chunk_9482 s83
  have s81 : leavesOK ctxLitU 328925000000 2 ((leaves.drop 18962).take 38) 329875000000 2 = true :=
    take_step (n := 2) (t := 38) (b := 18964) rfl rfl ArealUCore.ArealUK.chunk_9481 s82
  have s80 : leavesOK ctxLitU 328875000000 2 ((leaves.drop 18960).take 40) 329875000000 2 = true :=
    take_step (n := 2) (t := 40) (b := 18962) rfl rfl ArealUCore.ArealUK.chunk_9480 s81
  have s79 : leavesOK ctxLitU 328825000000 2 ((leaves.drop 18958).take 42) 329875000000 2 = true :=
    take_step (n := 2) (t := 42) (b := 18960) rfl rfl ArealUCore.ArealUK.chunk_9479 s80
  have s78 : leavesOK ctxLitU 328775000000 2 ((leaves.drop 18956).take 44) 329875000000 2 = true :=
    take_step (n := 2) (t := 44) (b := 18958) rfl rfl ArealUCore.ArealUK.chunk_9478 s79
  have s77 : leavesOK ctxLitU 328725000000 2 ((leaves.drop 18954).take 46) 329875000000 2 = true :=
    take_step (n := 2) (t := 46) (b := 18956) rfl rfl ArealUCore.ArealUK.chunk_9477 s78
  have s76 : leavesOK ctxLitU 328675000000 2 ((leaves.drop 18952).take 48) 329875000000 2 = true :=
    take_step (n := 2) (t := 48) (b := 18954) rfl rfl ArealUCore.ArealUK.chunk_9476 s77
  have s75 : leavesOK ctxLitU 328625000000 2 ((leaves.drop 18950).take 50) 329875000000 2 = true :=
    take_step (n := 2) (t := 50) (b := 18952) rfl rfl ArealUCore.ArealUK.chunk_9475 s76
  have s74 : leavesOK ctxLitU 328575000000 2 ((leaves.drop 18948).take 52) 329875000000 2 = true :=
    take_step (n := 2) (t := 52) (b := 18950) rfl rfl ArealUCore.ArealUK.chunk_9474 s75
  have s73 : leavesOK ctxLitU 328525000000 2 ((leaves.drop 18946).take 54) 329875000000 2 = true :=
    take_step (n := 2) (t := 54) (b := 18948) rfl rfl ArealUCore.ArealUK.chunk_9473 s74
  have s72 : leavesOK ctxLitU 328475000000 2 ((leaves.drop 18944).take 56) 329875000000 2 = true :=
    take_step (n := 2) (t := 56) (b := 18946) rfl rfl ArealUCore.ArealUK.chunk_9472 s73
  have s71 : leavesOK ctxLitU 328425000000 2 ((leaves.drop 18942).take 58) 329875000000 2 = true :=
    take_step (n := 2) (t := 58) (b := 18944) rfl rfl ArealUCore.ArealUK.chunk_9471 s72
  have s70 : leavesOK ctxLitU 328375000000 2 ((leaves.drop 18940).take 60) 329875000000 2 = true :=
    take_step (n := 2) (t := 60) (b := 18942) rfl rfl ArealUCore.ArealUK.chunk_9470 s71
  have s69 : leavesOK ctxLitU 328325000000 2 ((leaves.drop 18938).take 62) 329875000000 2 = true :=
    take_step (n := 2) (t := 62) (b := 18940) rfl rfl ArealUCore.ArealUK.chunk_9469 s70
  have s68 : leavesOK ctxLitU 328275000000 2 ((leaves.drop 18936).take 64) 329875000000 2 = true :=
    take_step (n := 2) (t := 64) (b := 18938) rfl rfl ArealUCore.ArealUK.chunk_9468 s69
  have s67 : leavesOK ctxLitU 328225000000 2 ((leaves.drop 18934).take 66) 329875000000 2 = true :=
    take_step (n := 2) (t := 66) (b := 18936) rfl rfl ArealUCore.ArealUK.chunk_9467 s68
  have s66 : leavesOK ctxLitU 328175000000 2 ((leaves.drop 18932).take 68) 329875000000 2 = true :=
    take_step (n := 2) (t := 68) (b := 18934) rfl rfl ArealUCore.ArealUK.chunk_9466 s67
  have s65 : leavesOK ctxLitU 328125000000 2 ((leaves.drop 18930).take 70) 329875000000 2 = true :=
    take_step (n := 2) (t := 70) (b := 18932) rfl rfl ArealUCore.ArealUK.chunk_9465 s66
  have s64 : leavesOK ctxLitU 328075000000 2 ((leaves.drop 18928).take 72) 329875000000 2 = true :=
    take_step (n := 2) (t := 72) (b := 18930) rfl rfl ArealUCore.ArealUK.chunk_9464 s65
  have s63 : leavesOK ctxLitU 328025000000 2 ((leaves.drop 18926).take 74) 329875000000 2 = true :=
    take_step (n := 2) (t := 74) (b := 18928) rfl rfl ArealUCore.ArealUK.chunk_9463 s64
  have s62 : leavesOK ctxLitU 327975000000 2 ((leaves.drop 18924).take 76) 329875000000 2 = true :=
    take_step (n := 2) (t := 76) (b := 18926) rfl rfl ArealUCore.ArealUK.chunk_9462 s63
  have s61 : leavesOK ctxLitU 327925000000 2 ((leaves.drop 18922).take 78) 329875000000 2 = true :=
    take_step (n := 2) (t := 78) (b := 18924) rfl rfl ArealUCore.ArealUK.chunk_9461 s62
  have s60 : leavesOK ctxLitU 327875000000 2 ((leaves.drop 18920).take 80) 329875000000 2 = true :=
    take_step (n := 2) (t := 80) (b := 18922) rfl rfl ArealUCore.ArealUK.chunk_9460 s61
  have s59 : leavesOK ctxLitU 327825000000 2 ((leaves.drop 18918).take 82) 329875000000 2 = true :=
    take_step (n := 2) (t := 82) (b := 18920) rfl rfl ArealUCore.ArealUK.chunk_9459 s60
  have s58 : leavesOK ctxLitU 327775000000 2 ((leaves.drop 18916).take 84) 329875000000 2 = true :=
    take_step (n := 2) (t := 84) (b := 18918) rfl rfl ArealUCore.ArealUK.chunk_9458 s59
  have s57 : leavesOK ctxLitU 327725000000 2 ((leaves.drop 18914).take 86) 329875000000 2 = true :=
    take_step (n := 2) (t := 86) (b := 18916) rfl rfl ArealUCore.ArealUK.chunk_9457 s58
  have s56 : leavesOK ctxLitU 327675000000 2 ((leaves.drop 18912).take 88) 329875000000 2 = true :=
    take_step (n := 2) (t := 88) (b := 18914) rfl rfl ArealUCore.ArealUK.chunk_9456 s57
  have s55 : leavesOK ctxLitU 327625000000 2 ((leaves.drop 18910).take 90) 329875000000 2 = true :=
    take_step (n := 2) (t := 90) (b := 18912) rfl rfl ArealUCore.ArealUK.chunk_9455 s56
  have s54 : leavesOK ctxLitU 327575000000 2 ((leaves.drop 18908).take 92) 329875000000 2 = true :=
    take_step (n := 2) (t := 92) (b := 18910) rfl rfl ArealUCore.ArealUK.chunk_9454 s55
  have s53 : leavesOK ctxLitU 327525000000 2 ((leaves.drop 18906).take 94) 329875000000 2 = true :=
    take_step (n := 2) (t := 94) (b := 18908) rfl rfl ArealUCore.ArealUK.chunk_9453 s54
  have s52 : leavesOK ctxLitU 327475000000 2 ((leaves.drop 18904).take 96) 329875000000 2 = true :=
    take_step (n := 2) (t := 96) (b := 18906) rfl rfl ArealUCore.ArealUK.chunk_9452 s53
  have s51 : leavesOK ctxLitU 327425000000 2 ((leaves.drop 18902).take 98) 329875000000 2 = true :=
    take_step (n := 2) (t := 98) (b := 18904) rfl rfl ArealUCore.ArealUK.chunk_9451 s52
  have s50 : leavesOK ctxLitU 327375000000 2 ((leaves.drop 18900).take 100) 329875000000 2 = true :=
    take_step (n := 2) (t := 100) (b := 18902) rfl rfl ArealUCore.ArealUK.chunk_9450 s51
  have s49 : leavesOK ctxLitU 327325000000 2 ((leaves.drop 18898).take 102) 329875000000 2 = true :=
    take_step (n := 2) (t := 102) (b := 18900) rfl rfl ArealUCore.ArealUK.chunk_9449 s50
  have s48 : leavesOK ctxLitU 327275000000 2 ((leaves.drop 18896).take 104) 329875000000 2 = true :=
    take_step (n := 2) (t := 104) (b := 18898) rfl rfl ArealUCore.ArealUK.chunk_9448 s49
  have s47 : leavesOK ctxLitU 327225000000 2 ((leaves.drop 18894).take 106) 329875000000 2 = true :=
    take_step (n := 2) (t := 106) (b := 18896) rfl rfl ArealUCore.ArealUK.chunk_9447 s48
  have s46 : leavesOK ctxLitU 327175000000 2 ((leaves.drop 18892).take 108) 329875000000 2 = true :=
    take_step (n := 2) (t := 108) (b := 18894) rfl rfl ArealUCore.ArealUK.chunk_9446 s47
  have s45 : leavesOK ctxLitU 327125000000 2 ((leaves.drop 18890).take 110) 329875000000 2 = true :=
    take_step (n := 2) (t := 110) (b := 18892) rfl rfl ArealUCore.ArealUK.chunk_9445 s46
  have s44 : leavesOK ctxLitU 327075000000 2 ((leaves.drop 18888).take 112) 329875000000 2 = true :=
    take_step (n := 2) (t := 112) (b := 18890) rfl rfl ArealUCore.ArealUK.chunk_9444 s45
  have s43 : leavesOK ctxLitU 327025000000 2 ((leaves.drop 18886).take 114) 329875000000 2 = true :=
    take_step (n := 2) (t := 114) (b := 18888) rfl rfl ArealUCore.ArealUK.chunk_9443 s44
  have s42 : leavesOK ctxLitU 326975000000 2 ((leaves.drop 18884).take 116) 329875000000 2 = true :=
    take_step (n := 2) (t := 116) (b := 18886) rfl rfl ArealUCore.ArealUK.chunk_9442 s43
  have s41 : leavesOK ctxLitU 326925000000 2 ((leaves.drop 18882).take 118) 329875000000 2 = true :=
    take_step (n := 2) (t := 118) (b := 18884) rfl rfl ArealUCore.ArealUK.chunk_9441 s42
  have s40 : leavesOK ctxLitU 326875000000 2 ((leaves.drop 18880).take 120) 329875000000 2 = true :=
    take_step (n := 2) (t := 120) (b := 18882) rfl rfl ArealUCore.ArealUK.chunk_9440 s41
  have s39 : leavesOK ctxLitU 326825000000 2 ((leaves.drop 18878).take 122) 329875000000 2 = true :=
    take_step (n := 2) (t := 122) (b := 18880) rfl rfl ArealUCore.ArealUK.chunk_9439 s40
  have s38 : leavesOK ctxLitU 326775000000 2 ((leaves.drop 18876).take 124) 329875000000 2 = true :=
    take_step (n := 2) (t := 124) (b := 18878) rfl rfl ArealUCore.ArealUK.chunk_9438 s39
  have s37 : leavesOK ctxLitU 326725000000 2 ((leaves.drop 18874).take 126) 329875000000 2 = true :=
    take_step (n := 2) (t := 126) (b := 18876) rfl rfl ArealUCore.ArealUK.chunk_9437 s38
  have s36 : leavesOK ctxLitU 326675000000 2 ((leaves.drop 18872).take 128) 329875000000 2 = true :=
    take_step (n := 2) (t := 128) (b := 18874) rfl rfl ArealUCore.ArealUK.chunk_9436 s37
  have s35 : leavesOK ctxLitU 326625000000 2 ((leaves.drop 18870).take 130) 329875000000 2 = true :=
    take_step (n := 2) (t := 130) (b := 18872) rfl rfl ArealUCore.ArealUK.chunk_9435 s36
  have s34 : leavesOK ctxLitU 326575000000 2 ((leaves.drop 18868).take 132) 329875000000 2 = true :=
    take_step (n := 2) (t := 132) (b := 18870) rfl rfl ArealUCore.ArealUK.chunk_9434 s35
  have s33 : leavesOK ctxLitU 326525000000 2 ((leaves.drop 18866).take 134) 329875000000 2 = true :=
    take_step (n := 2) (t := 134) (b := 18868) rfl rfl ArealUCore.ArealUK.chunk_9433 s34
  have s32 : leavesOK ctxLitU 326475000000 2 ((leaves.drop 18864).take 136) 329875000000 2 = true :=
    take_step (n := 2) (t := 136) (b := 18866) rfl rfl ArealUCore.ArealUK.chunk_9432 s33
  have s31 : leavesOK ctxLitU 326425000000 2 ((leaves.drop 18862).take 138) 329875000000 2 = true :=
    take_step (n := 2) (t := 138) (b := 18864) rfl rfl ArealUCore.ArealUK.chunk_9431 s32
  have s30 : leavesOK ctxLitU 326375000000 2 ((leaves.drop 18860).take 140) 329875000000 2 = true :=
    take_step (n := 2) (t := 140) (b := 18862) rfl rfl ArealUCore.ArealUK.chunk_9430 s31
  have s29 : leavesOK ctxLitU 326325000000 2 ((leaves.drop 18858).take 142) 329875000000 2 = true :=
    take_step (n := 2) (t := 142) (b := 18860) rfl rfl ArealUCore.ArealUK.chunk_9429 s30
  have s28 : leavesOK ctxLitU 326275000000 2 ((leaves.drop 18856).take 144) 329875000000 2 = true :=
    take_step (n := 2) (t := 144) (b := 18858) rfl rfl ArealUCore.ArealUK.chunk_9428 s29
  have s27 : leavesOK ctxLitU 326225000000 2 ((leaves.drop 18854).take 146) 329875000000 2 = true :=
    take_step (n := 2) (t := 146) (b := 18856) rfl rfl ArealUCore.ArealUK.chunk_9427 s28
  have s26 : leavesOK ctxLitU 326175000000 2 ((leaves.drop 18852).take 148) 329875000000 2 = true :=
    take_step (n := 2) (t := 148) (b := 18854) rfl rfl ArealUCore.ArealUK.chunk_9426 s27
  have s25 : leavesOK ctxLitU 326125000000 2 ((leaves.drop 18850).take 150) 329875000000 2 = true :=
    take_step (n := 2) (t := 150) (b := 18852) rfl rfl ArealUCore.ArealUK.chunk_9425 s26
  have s24 : leavesOK ctxLitU 326075000000 2 ((leaves.drop 18848).take 152) 329875000000 2 = true :=
    take_step (n := 2) (t := 152) (b := 18850) rfl rfl ArealUCore.ArealUK.chunk_9424 s25
  have s23 : leavesOK ctxLitU 326025000000 2 ((leaves.drop 18846).take 154) 329875000000 2 = true :=
    take_step (n := 2) (t := 154) (b := 18848) rfl rfl ArealUCore.ArealUK.chunk_9423 s24
  have s22 : leavesOK ctxLitU 325975000000 2 ((leaves.drop 18844).take 156) 329875000000 2 = true :=
    take_step (n := 2) (t := 156) (b := 18846) rfl rfl ArealUCore.ArealUK.chunk_9422 s23
  have s21 : leavesOK ctxLitU 325925000000 2 ((leaves.drop 18842).take 158) 329875000000 2 = true :=
    take_step (n := 2) (t := 158) (b := 18844) rfl rfl ArealUCore.ArealUK.chunk_9421 s22
  have s20 : leavesOK ctxLitU 325875000000 2 ((leaves.drop 18840).take 160) 329875000000 2 = true :=
    take_step (n := 2) (t := 160) (b := 18842) rfl rfl ArealUCore.ArealUK.chunk_9420 s21
  have s19 : leavesOK ctxLitU 325825000000 2 ((leaves.drop 18838).take 162) 329875000000 2 = true :=
    take_step (n := 2) (t := 162) (b := 18840) rfl rfl ArealUCore.ArealUK.chunk_9419 s20
  have s18 : leavesOK ctxLitU 325775000000 2 ((leaves.drop 18836).take 164) 329875000000 2 = true :=
    take_step (n := 2) (t := 164) (b := 18838) rfl rfl ArealUCore.ArealUK.chunk_9418 s19
  have s17 : leavesOK ctxLitU 325725000000 2 ((leaves.drop 18834).take 166) 329875000000 2 = true :=
    take_step (n := 2) (t := 166) (b := 18836) rfl rfl ArealUCore.ArealUK.chunk_9417 s18
  have s16 : leavesOK ctxLitU 325675000000 2 ((leaves.drop 18832).take 168) 329875000000 2 = true :=
    take_step (n := 2) (t := 168) (b := 18834) rfl rfl ArealUCore.ArealUK.chunk_9416 s17
  have s15 : leavesOK ctxLitU 325625000000 2 ((leaves.drop 18830).take 170) 329875000000 2 = true :=
    take_step (n := 2) (t := 170) (b := 18832) rfl rfl ArealUCore.ArealUK.chunk_9415 s16
  have s14 : leavesOK ctxLitU 325575000000 2 ((leaves.drop 18828).take 172) 329875000000 2 = true :=
    take_step (n := 2) (t := 172) (b := 18830) rfl rfl ArealUCore.ArealUK.chunk_9414 s15
  have s13 : leavesOK ctxLitU 325525000000 2 ((leaves.drop 18826).take 174) 329875000000 2 = true :=
    take_step (n := 2) (t := 174) (b := 18828) rfl rfl ArealUCore.ArealUK.chunk_9413 s14
  have s12 : leavesOK ctxLitU 325475000000 2 ((leaves.drop 18824).take 176) 329875000000 2 = true :=
    take_step (n := 2) (t := 176) (b := 18826) rfl rfl ArealUCore.ArealUK.chunk_9412 s13
  have s11 : leavesOK ctxLitU 325425000000 2 ((leaves.drop 18822).take 178) 329875000000 2 = true :=
    take_step (n := 2) (t := 178) (b := 18824) rfl rfl ArealUCore.ArealUK.chunk_9411 s12
  have s10 : leavesOK ctxLitU 325375000000 2 ((leaves.drop 18820).take 180) 329875000000 2 = true :=
    take_step (n := 2) (t := 180) (b := 18822) rfl rfl ArealUCore.ArealUK.chunk_9410 s11
  have s9 : leavesOK ctxLitU 325325000000 2 ((leaves.drop 18818).take 182) 329875000000 2 = true :=
    take_step (n := 2) (t := 182) (b := 18820) rfl rfl ArealUCore.ArealUK.chunk_9409 s10
  have s8 : leavesOK ctxLitU 325275000000 2 ((leaves.drop 18816).take 184) 329875000000 2 = true :=
    take_step (n := 2) (t := 184) (b := 18818) rfl rfl ArealUCore.ArealUK.chunk_9408 s9
  have s7 : leavesOK ctxLitU 325225000000 2 ((leaves.drop 18814).take 186) 329875000000 2 = true :=
    take_step (n := 2) (t := 186) (b := 18816) rfl rfl ArealUCore.ArealUK.chunk_9407 s8
  have s6 : leavesOK ctxLitU 325175000000 2 ((leaves.drop 18812).take 188) 329875000000 2 = true :=
    take_step (n := 2) (t := 188) (b := 18814) rfl rfl ArealUCore.ArealUK.chunk_9406 s7
  have s5 : leavesOK ctxLitU 325125000000 2 ((leaves.drop 18810).take 190) 329875000000 2 = true :=
    take_step (n := 2) (t := 190) (b := 18812) rfl rfl ArealUCore.ArealUK.chunk_9405 s6
  have s4 : leavesOK ctxLitU 325075000000 2 ((leaves.drop 18808).take 192) 329875000000 2 = true :=
    take_step (n := 2) (t := 192) (b := 18810) rfl rfl ArealUCore.ArealUK.chunk_9404 s5
  have s3 : leavesOK ctxLitU 325025000000 2 ((leaves.drop 18806).take 194) 329875000000 2 = true :=
    take_step (n := 2) (t := 194) (b := 18808) rfl rfl ArealUCore.ArealUK.chunk_9403 s4
  have s2 : leavesOK ctxLitU 324975000000 2 ((leaves.drop 18804).take 196) 329875000000 2 = true :=
    take_step (n := 2) (t := 196) (b := 18806) rfl rfl ArealUCore.ArealUK.chunk_9402 s3
  have s1 : leavesOK ctxLitU 324925000000 2 ((leaves.drop 18802).take 198) 329875000000 2 = true :=
    take_step (n := 2) (t := 198) (b := 18804) rfl rfl ArealUCore.ArealUK.chunk_9401 s2
  have s0 : leavesOK ctxLitU 324875000000 2 ((leaves.drop 18800).take 200) 329875000000 2 = true :=
    take_step (n := 2) (t := 200) (b := 18802) rfl rfl ArealUCore.ArealUK.chunk_9400 s1
  exact s0

end Areal.UCert

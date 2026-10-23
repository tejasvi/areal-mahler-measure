import ArealUK.Chunk16400
import ArealUK.Chunk16401
import ArealUK.Chunk16402
import ArealUK.Chunk16403
import ArealUK.Chunk16404
import ArealUK.Chunk16405
import ArealUK.Chunk16406
import ArealUK.Chunk16407
import ArealUK.Chunk16408
import ArealUK.Chunk16409
import ArealUK.Chunk16410
import ArealUK.Chunk16411
import ArealUK.Chunk16412
import ArealUK.Chunk16413
import ArealUK.Chunk16414
import ArealUK.Chunk16415
import ArealUK.Chunk16416
import ArealUK.Chunk16417
import ArealUK.Chunk16418
import ArealUK.Chunk16419
import ArealUK.Chunk16420
import ArealUK.Chunk16421
import ArealUK.Chunk16422
import ArealUK.Chunk16423
import ArealUK.Chunk16424
import ArealUK.Chunk16425
import ArealUK.Chunk16426
import ArealUK.Chunk16427
import ArealUK.Chunk16428
import ArealUK.Chunk16429
import ArealUK.Chunk16430
import ArealUK.Chunk16431
import ArealUK.Chunk16432
import ArealUK.Chunk16433
import ArealUK.Chunk16434
import ArealUK.Chunk16435
import ArealUK.Chunk16436
import ArealUK.Chunk16437
import ArealUK.Chunk16438
import ArealUK.Chunk16439
import ArealUK.Chunk16440
import ArealUK.Chunk16441
import ArealUK.Chunk16442
import ArealUK.Chunk16443
import ArealUK.Chunk16444
import ArealUK.Chunk16445
import ArealUK.Chunk16446
import ArealUK.Chunk16447
import ArealUK.Chunk16448
import ArealUK.Chunk16449
import ArealUK.Chunk16450
import ArealUK.Chunk16451
import ArealUK.Chunk16452
import ArealUK.Chunk16453
import ArealUK.Chunk16454
import ArealUK.Chunk16455
import ArealUK.Chunk16456
import ArealUK.Chunk16457
import ArealUK.Chunk16458
import ArealUK.Chunk16459
import ArealUK.Chunk16460
import ArealUK.Chunk16461
import ArealUK.Chunk16462
import ArealUK.Chunk16463
import ArealUK.Chunk16464
import ArealUK.Chunk16465
import ArealUK.Chunk16466
import ArealUK.Chunk16467
import ArealUK.Chunk16468
import ArealUK.Chunk16469
import ArealUK.Chunk16470
import ArealUK.Chunk16471
import ArealUK.Chunk16472
import ArealUK.Chunk16473
import ArealUK.Chunk16474
import ArealUK.Chunk16475
import ArealUK.Chunk16476
import ArealUK.Chunk16477
import ArealUK.Chunk16478
import ArealUK.Chunk16479
import ArealUK.Chunk16480
import ArealUK.Chunk16481
import ArealUK.Chunk16482
import ArealUK.Chunk16483
import ArealUK.Chunk16484
import ArealUK.Chunk16485
import ArealUK.Chunk16486
import ArealUK.Chunk16487
import ArealUK.Chunk16488
import ArealUK.Chunk16489
import ArealUK.Chunk16490
import ArealUK.Chunk16491
import ArealUK.Chunk16492
import ArealUK.Chunk16493
import ArealUK.Chunk16494
import ArealUK.Chunk16495
import ArealUK.Chunk16496
import ArealUK.Chunk16497
import ArealUK.Chunk16498
import ArealUK.Chunk16499
import Areal.UCert.LeavesKGen

/-! Group 164 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_164 : leavesOK ctxLitU 183300000000 0 ((leaves.drop 32800).take 200) 188300000000 0 = true := by
  have s99 := ArealUCore.ArealUK.chunk_16499
  have s98 : leavesOK ctxLitU 188200000000 0 ((leaves.drop 32996).take 4) 188300000000 0 = true :=
    take_step (n := 2) (t := 4) (b := 32998) rfl rfl ArealUCore.ArealUK.chunk_16498 s99
  have s97 : leavesOK ctxLitU 188150000000 0 ((leaves.drop 32994).take 6) 188300000000 0 = true :=
    take_step (n := 2) (t := 6) (b := 32996) rfl rfl ArealUCore.ArealUK.chunk_16497 s98
  have s96 : leavesOK ctxLitU 188100000000 0 ((leaves.drop 32992).take 8) 188300000000 0 = true :=
    take_step (n := 2) (t := 8) (b := 32994) rfl rfl ArealUCore.ArealUK.chunk_16496 s97
  have s95 : leavesOK ctxLitU 188050000000 0 ((leaves.drop 32990).take 10) 188300000000 0 = true :=
    take_step (n := 2) (t := 10) (b := 32992) rfl rfl ArealUCore.ArealUK.chunk_16495 s96
  have s94 : leavesOK ctxLitU 188000000000 0 ((leaves.drop 32988).take 12) 188300000000 0 = true :=
    take_step (n := 2) (t := 12) (b := 32990) rfl rfl ArealUCore.ArealUK.chunk_16494 s95
  have s93 : leavesOK ctxLitU 187950000000 0 ((leaves.drop 32986).take 14) 188300000000 0 = true :=
    take_step (n := 2) (t := 14) (b := 32988) rfl rfl ArealUCore.ArealUK.chunk_16493 s94
  have s92 : leavesOK ctxLitU 187900000000 0 ((leaves.drop 32984).take 16) 188300000000 0 = true :=
    take_step (n := 2) (t := 16) (b := 32986) rfl rfl ArealUCore.ArealUK.chunk_16492 s93
  have s91 : leavesOK ctxLitU 187850000000 0 ((leaves.drop 32982).take 18) 188300000000 0 = true :=
    take_step (n := 2) (t := 18) (b := 32984) rfl rfl ArealUCore.ArealUK.chunk_16491 s92
  have s90 : leavesOK ctxLitU 187800000000 0 ((leaves.drop 32980).take 20) 188300000000 0 = true :=
    take_step (n := 2) (t := 20) (b := 32982) rfl rfl ArealUCore.ArealUK.chunk_16490 s91
  have s89 : leavesOK ctxLitU 187750000000 0 ((leaves.drop 32978).take 22) 188300000000 0 = true :=
    take_step (n := 2) (t := 22) (b := 32980) rfl rfl ArealUCore.ArealUK.chunk_16489 s90
  have s88 : leavesOK ctxLitU 187700000000 0 ((leaves.drop 32976).take 24) 188300000000 0 = true :=
    take_step (n := 2) (t := 24) (b := 32978) rfl rfl ArealUCore.ArealUK.chunk_16488 s89
  have s87 : leavesOK ctxLitU 187650000000 0 ((leaves.drop 32974).take 26) 188300000000 0 = true :=
    take_step (n := 2) (t := 26) (b := 32976) rfl rfl ArealUCore.ArealUK.chunk_16487 s88
  have s86 : leavesOK ctxLitU 187600000000 0 ((leaves.drop 32972).take 28) 188300000000 0 = true :=
    take_step (n := 2) (t := 28) (b := 32974) rfl rfl ArealUCore.ArealUK.chunk_16486 s87
  have s85 : leavesOK ctxLitU 187550000000 0 ((leaves.drop 32970).take 30) 188300000000 0 = true :=
    take_step (n := 2) (t := 30) (b := 32972) rfl rfl ArealUCore.ArealUK.chunk_16485 s86
  have s84 : leavesOK ctxLitU 187500000000 0 ((leaves.drop 32968).take 32) 188300000000 0 = true :=
    take_step (n := 2) (t := 32) (b := 32970) rfl rfl ArealUCore.ArealUK.chunk_16484 s85
  have s83 : leavesOK ctxLitU 187450000000 0 ((leaves.drop 32966).take 34) 188300000000 0 = true :=
    take_step (n := 2) (t := 34) (b := 32968) rfl rfl ArealUCore.ArealUK.chunk_16483 s84
  have s82 : leavesOK ctxLitU 187400000000 0 ((leaves.drop 32964).take 36) 188300000000 0 = true :=
    take_step (n := 2) (t := 36) (b := 32966) rfl rfl ArealUCore.ArealUK.chunk_16482 s83
  have s81 : leavesOK ctxLitU 187350000000 0 ((leaves.drop 32962).take 38) 188300000000 0 = true :=
    take_step (n := 2) (t := 38) (b := 32964) rfl rfl ArealUCore.ArealUK.chunk_16481 s82
  have s80 : leavesOK ctxLitU 187300000000 0 ((leaves.drop 32960).take 40) 188300000000 0 = true :=
    take_step (n := 2) (t := 40) (b := 32962) rfl rfl ArealUCore.ArealUK.chunk_16480 s81
  have s79 : leavesOK ctxLitU 187250000000 0 ((leaves.drop 32958).take 42) 188300000000 0 = true :=
    take_step (n := 2) (t := 42) (b := 32960) rfl rfl ArealUCore.ArealUK.chunk_16479 s80
  have s78 : leavesOK ctxLitU 187200000000 0 ((leaves.drop 32956).take 44) 188300000000 0 = true :=
    take_step (n := 2) (t := 44) (b := 32958) rfl rfl ArealUCore.ArealUK.chunk_16478 s79
  have s77 : leavesOK ctxLitU 187150000000 0 ((leaves.drop 32954).take 46) 188300000000 0 = true :=
    take_step (n := 2) (t := 46) (b := 32956) rfl rfl ArealUCore.ArealUK.chunk_16477 s78
  have s76 : leavesOK ctxLitU 187100000000 0 ((leaves.drop 32952).take 48) 188300000000 0 = true :=
    take_step (n := 2) (t := 48) (b := 32954) rfl rfl ArealUCore.ArealUK.chunk_16476 s77
  have s75 : leavesOK ctxLitU 187050000000 0 ((leaves.drop 32950).take 50) 188300000000 0 = true :=
    take_step (n := 2) (t := 50) (b := 32952) rfl rfl ArealUCore.ArealUK.chunk_16475 s76
  have s74 : leavesOK ctxLitU 187000000000 0 ((leaves.drop 32948).take 52) 188300000000 0 = true :=
    take_step (n := 2) (t := 52) (b := 32950) rfl rfl ArealUCore.ArealUK.chunk_16474 s75
  have s73 : leavesOK ctxLitU 186950000000 0 ((leaves.drop 32946).take 54) 188300000000 0 = true :=
    take_step (n := 2) (t := 54) (b := 32948) rfl rfl ArealUCore.ArealUK.chunk_16473 s74
  have s72 : leavesOK ctxLitU 186900000000 0 ((leaves.drop 32944).take 56) 188300000000 0 = true :=
    take_step (n := 2) (t := 56) (b := 32946) rfl rfl ArealUCore.ArealUK.chunk_16472 s73
  have s71 : leavesOK ctxLitU 186850000000 0 ((leaves.drop 32942).take 58) 188300000000 0 = true :=
    take_step (n := 2) (t := 58) (b := 32944) rfl rfl ArealUCore.ArealUK.chunk_16471 s72
  have s70 : leavesOK ctxLitU 186800000000 0 ((leaves.drop 32940).take 60) 188300000000 0 = true :=
    take_step (n := 2) (t := 60) (b := 32942) rfl rfl ArealUCore.ArealUK.chunk_16470 s71
  have s69 : leavesOK ctxLitU 186750000000 0 ((leaves.drop 32938).take 62) 188300000000 0 = true :=
    take_step (n := 2) (t := 62) (b := 32940) rfl rfl ArealUCore.ArealUK.chunk_16469 s70
  have s68 : leavesOK ctxLitU 186700000000 0 ((leaves.drop 32936).take 64) 188300000000 0 = true :=
    take_step (n := 2) (t := 64) (b := 32938) rfl rfl ArealUCore.ArealUK.chunk_16468 s69
  have s67 : leavesOK ctxLitU 186650000000 0 ((leaves.drop 32934).take 66) 188300000000 0 = true :=
    take_step (n := 2) (t := 66) (b := 32936) rfl rfl ArealUCore.ArealUK.chunk_16467 s68
  have s66 : leavesOK ctxLitU 186600000000 0 ((leaves.drop 32932).take 68) 188300000000 0 = true :=
    take_step (n := 2) (t := 68) (b := 32934) rfl rfl ArealUCore.ArealUK.chunk_16466 s67
  have s65 : leavesOK ctxLitU 186550000000 0 ((leaves.drop 32930).take 70) 188300000000 0 = true :=
    take_step (n := 2) (t := 70) (b := 32932) rfl rfl ArealUCore.ArealUK.chunk_16465 s66
  have s64 : leavesOK ctxLitU 186500000000 0 ((leaves.drop 32928).take 72) 188300000000 0 = true :=
    take_step (n := 2) (t := 72) (b := 32930) rfl rfl ArealUCore.ArealUK.chunk_16464 s65
  have s63 : leavesOK ctxLitU 186450000000 0 ((leaves.drop 32926).take 74) 188300000000 0 = true :=
    take_step (n := 2) (t := 74) (b := 32928) rfl rfl ArealUCore.ArealUK.chunk_16463 s64
  have s62 : leavesOK ctxLitU 186400000000 0 ((leaves.drop 32924).take 76) 188300000000 0 = true :=
    take_step (n := 2) (t := 76) (b := 32926) rfl rfl ArealUCore.ArealUK.chunk_16462 s63
  have s61 : leavesOK ctxLitU 186350000000 0 ((leaves.drop 32922).take 78) 188300000000 0 = true :=
    take_step (n := 2) (t := 78) (b := 32924) rfl rfl ArealUCore.ArealUK.chunk_16461 s62
  have s60 : leavesOK ctxLitU 186300000000 0 ((leaves.drop 32920).take 80) 188300000000 0 = true :=
    take_step (n := 2) (t := 80) (b := 32922) rfl rfl ArealUCore.ArealUK.chunk_16460 s61
  have s59 : leavesOK ctxLitU 186250000000 0 ((leaves.drop 32918).take 82) 188300000000 0 = true :=
    take_step (n := 2) (t := 82) (b := 32920) rfl rfl ArealUCore.ArealUK.chunk_16459 s60
  have s58 : leavesOK ctxLitU 186200000000 0 ((leaves.drop 32916).take 84) 188300000000 0 = true :=
    take_step (n := 2) (t := 84) (b := 32918) rfl rfl ArealUCore.ArealUK.chunk_16458 s59
  have s57 : leavesOK ctxLitU 186150000000 0 ((leaves.drop 32914).take 86) 188300000000 0 = true :=
    take_step (n := 2) (t := 86) (b := 32916) rfl rfl ArealUCore.ArealUK.chunk_16457 s58
  have s56 : leavesOK ctxLitU 186100000000 0 ((leaves.drop 32912).take 88) 188300000000 0 = true :=
    take_step (n := 2) (t := 88) (b := 32914) rfl rfl ArealUCore.ArealUK.chunk_16456 s57
  have s55 : leavesOK ctxLitU 186050000000 0 ((leaves.drop 32910).take 90) 188300000000 0 = true :=
    take_step (n := 2) (t := 90) (b := 32912) rfl rfl ArealUCore.ArealUK.chunk_16455 s56
  have s54 : leavesOK ctxLitU 186000000000 0 ((leaves.drop 32908).take 92) 188300000000 0 = true :=
    take_step (n := 2) (t := 92) (b := 32910) rfl rfl ArealUCore.ArealUK.chunk_16454 s55
  have s53 : leavesOK ctxLitU 185950000000 0 ((leaves.drop 32906).take 94) 188300000000 0 = true :=
    take_step (n := 2) (t := 94) (b := 32908) rfl rfl ArealUCore.ArealUK.chunk_16453 s54
  have s52 : leavesOK ctxLitU 185900000000 0 ((leaves.drop 32904).take 96) 188300000000 0 = true :=
    take_step (n := 2) (t := 96) (b := 32906) rfl rfl ArealUCore.ArealUK.chunk_16452 s53
  have s51 : leavesOK ctxLitU 185850000000 0 ((leaves.drop 32902).take 98) 188300000000 0 = true :=
    take_step (n := 2) (t := 98) (b := 32904) rfl rfl ArealUCore.ArealUK.chunk_16451 s52
  have s50 : leavesOK ctxLitU 185800000000 0 ((leaves.drop 32900).take 100) 188300000000 0 = true :=
    take_step (n := 2) (t := 100) (b := 32902) rfl rfl ArealUCore.ArealUK.chunk_16450 s51
  have s49 : leavesOK ctxLitU 185750000000 0 ((leaves.drop 32898).take 102) 188300000000 0 = true :=
    take_step (n := 2) (t := 102) (b := 32900) rfl rfl ArealUCore.ArealUK.chunk_16449 s50
  have s48 : leavesOK ctxLitU 185700000000 0 ((leaves.drop 32896).take 104) 188300000000 0 = true :=
    take_step (n := 2) (t := 104) (b := 32898) rfl rfl ArealUCore.ArealUK.chunk_16448 s49
  have s47 : leavesOK ctxLitU 185650000000 0 ((leaves.drop 32894).take 106) 188300000000 0 = true :=
    take_step (n := 2) (t := 106) (b := 32896) rfl rfl ArealUCore.ArealUK.chunk_16447 s48
  have s46 : leavesOK ctxLitU 185600000000 0 ((leaves.drop 32892).take 108) 188300000000 0 = true :=
    take_step (n := 2) (t := 108) (b := 32894) rfl rfl ArealUCore.ArealUK.chunk_16446 s47
  have s45 : leavesOK ctxLitU 185550000000 0 ((leaves.drop 32890).take 110) 188300000000 0 = true :=
    take_step (n := 2) (t := 110) (b := 32892) rfl rfl ArealUCore.ArealUK.chunk_16445 s46
  have s44 : leavesOK ctxLitU 185500000000 0 ((leaves.drop 32888).take 112) 188300000000 0 = true :=
    take_step (n := 2) (t := 112) (b := 32890) rfl rfl ArealUCore.ArealUK.chunk_16444 s45
  have s43 : leavesOK ctxLitU 185450000000 0 ((leaves.drop 32886).take 114) 188300000000 0 = true :=
    take_step (n := 2) (t := 114) (b := 32888) rfl rfl ArealUCore.ArealUK.chunk_16443 s44
  have s42 : leavesOK ctxLitU 185400000000 0 ((leaves.drop 32884).take 116) 188300000000 0 = true :=
    take_step (n := 2) (t := 116) (b := 32886) rfl rfl ArealUCore.ArealUK.chunk_16442 s43
  have s41 : leavesOK ctxLitU 185350000000 0 ((leaves.drop 32882).take 118) 188300000000 0 = true :=
    take_step (n := 2) (t := 118) (b := 32884) rfl rfl ArealUCore.ArealUK.chunk_16441 s42
  have s40 : leavesOK ctxLitU 185300000000 0 ((leaves.drop 32880).take 120) 188300000000 0 = true :=
    take_step (n := 2) (t := 120) (b := 32882) rfl rfl ArealUCore.ArealUK.chunk_16440 s41
  have s39 : leavesOK ctxLitU 185250000000 0 ((leaves.drop 32878).take 122) 188300000000 0 = true :=
    take_step (n := 2) (t := 122) (b := 32880) rfl rfl ArealUCore.ArealUK.chunk_16439 s40
  have s38 : leavesOK ctxLitU 185200000000 0 ((leaves.drop 32876).take 124) 188300000000 0 = true :=
    take_step (n := 2) (t := 124) (b := 32878) rfl rfl ArealUCore.ArealUK.chunk_16438 s39
  have s37 : leavesOK ctxLitU 185150000000 0 ((leaves.drop 32874).take 126) 188300000000 0 = true :=
    take_step (n := 2) (t := 126) (b := 32876) rfl rfl ArealUCore.ArealUK.chunk_16437 s38
  have s36 : leavesOK ctxLitU 185100000000 0 ((leaves.drop 32872).take 128) 188300000000 0 = true :=
    take_step (n := 2) (t := 128) (b := 32874) rfl rfl ArealUCore.ArealUK.chunk_16436 s37
  have s35 : leavesOK ctxLitU 185050000000 0 ((leaves.drop 32870).take 130) 188300000000 0 = true :=
    take_step (n := 2) (t := 130) (b := 32872) rfl rfl ArealUCore.ArealUK.chunk_16435 s36
  have s34 : leavesOK ctxLitU 185000000000 0 ((leaves.drop 32868).take 132) 188300000000 0 = true :=
    take_step (n := 2) (t := 132) (b := 32870) rfl rfl ArealUCore.ArealUK.chunk_16434 s35
  have s33 : leavesOK ctxLitU 184950000000 0 ((leaves.drop 32866).take 134) 188300000000 0 = true :=
    take_step (n := 2) (t := 134) (b := 32868) rfl rfl ArealUCore.ArealUK.chunk_16433 s34
  have s32 : leavesOK ctxLitU 184900000000 0 ((leaves.drop 32864).take 136) 188300000000 0 = true :=
    take_step (n := 2) (t := 136) (b := 32866) rfl rfl ArealUCore.ArealUK.chunk_16432 s33
  have s31 : leavesOK ctxLitU 184850000000 0 ((leaves.drop 32862).take 138) 188300000000 0 = true :=
    take_step (n := 2) (t := 138) (b := 32864) rfl rfl ArealUCore.ArealUK.chunk_16431 s32
  have s30 : leavesOK ctxLitU 184800000000 0 ((leaves.drop 32860).take 140) 188300000000 0 = true :=
    take_step (n := 2) (t := 140) (b := 32862) rfl rfl ArealUCore.ArealUK.chunk_16430 s31
  have s29 : leavesOK ctxLitU 184750000000 0 ((leaves.drop 32858).take 142) 188300000000 0 = true :=
    take_step (n := 2) (t := 142) (b := 32860) rfl rfl ArealUCore.ArealUK.chunk_16429 s30
  have s28 : leavesOK ctxLitU 184700000000 0 ((leaves.drop 32856).take 144) 188300000000 0 = true :=
    take_step (n := 2) (t := 144) (b := 32858) rfl rfl ArealUCore.ArealUK.chunk_16428 s29
  have s27 : leavesOK ctxLitU 184650000000 0 ((leaves.drop 32854).take 146) 188300000000 0 = true :=
    take_step (n := 2) (t := 146) (b := 32856) rfl rfl ArealUCore.ArealUK.chunk_16427 s28
  have s26 : leavesOK ctxLitU 184600000000 0 ((leaves.drop 32852).take 148) 188300000000 0 = true :=
    take_step (n := 2) (t := 148) (b := 32854) rfl rfl ArealUCore.ArealUK.chunk_16426 s27
  have s25 : leavesOK ctxLitU 184550000000 0 ((leaves.drop 32850).take 150) 188300000000 0 = true :=
    take_step (n := 2) (t := 150) (b := 32852) rfl rfl ArealUCore.ArealUK.chunk_16425 s26
  have s24 : leavesOK ctxLitU 184500000000 0 ((leaves.drop 32848).take 152) 188300000000 0 = true :=
    take_step (n := 2) (t := 152) (b := 32850) rfl rfl ArealUCore.ArealUK.chunk_16424 s25
  have s23 : leavesOK ctxLitU 184450000000 0 ((leaves.drop 32846).take 154) 188300000000 0 = true :=
    take_step (n := 2) (t := 154) (b := 32848) rfl rfl ArealUCore.ArealUK.chunk_16423 s24
  have s22 : leavesOK ctxLitU 184400000000 0 ((leaves.drop 32844).take 156) 188300000000 0 = true :=
    take_step (n := 2) (t := 156) (b := 32846) rfl rfl ArealUCore.ArealUK.chunk_16422 s23
  have s21 : leavesOK ctxLitU 184350000000 0 ((leaves.drop 32842).take 158) 188300000000 0 = true :=
    take_step (n := 2) (t := 158) (b := 32844) rfl rfl ArealUCore.ArealUK.chunk_16421 s22
  have s20 : leavesOK ctxLitU 184300000000 0 ((leaves.drop 32840).take 160) 188300000000 0 = true :=
    take_step (n := 2) (t := 160) (b := 32842) rfl rfl ArealUCore.ArealUK.chunk_16420 s21
  have s19 : leavesOK ctxLitU 184250000000 0 ((leaves.drop 32838).take 162) 188300000000 0 = true :=
    take_step (n := 2) (t := 162) (b := 32840) rfl rfl ArealUCore.ArealUK.chunk_16419 s20
  have s18 : leavesOK ctxLitU 184200000000 0 ((leaves.drop 32836).take 164) 188300000000 0 = true :=
    take_step (n := 2) (t := 164) (b := 32838) rfl rfl ArealUCore.ArealUK.chunk_16418 s19
  have s17 : leavesOK ctxLitU 184150000000 0 ((leaves.drop 32834).take 166) 188300000000 0 = true :=
    take_step (n := 2) (t := 166) (b := 32836) rfl rfl ArealUCore.ArealUK.chunk_16417 s18
  have s16 : leavesOK ctxLitU 184100000000 0 ((leaves.drop 32832).take 168) 188300000000 0 = true :=
    take_step (n := 2) (t := 168) (b := 32834) rfl rfl ArealUCore.ArealUK.chunk_16416 s17
  have s15 : leavesOK ctxLitU 184050000000 0 ((leaves.drop 32830).take 170) 188300000000 0 = true :=
    take_step (n := 2) (t := 170) (b := 32832) rfl rfl ArealUCore.ArealUK.chunk_16415 s16
  have s14 : leavesOK ctxLitU 184000000000 0 ((leaves.drop 32828).take 172) 188300000000 0 = true :=
    take_step (n := 2) (t := 172) (b := 32830) rfl rfl ArealUCore.ArealUK.chunk_16414 s15
  have s13 : leavesOK ctxLitU 183950000000 0 ((leaves.drop 32826).take 174) 188300000000 0 = true :=
    take_step (n := 2) (t := 174) (b := 32828) rfl rfl ArealUCore.ArealUK.chunk_16413 s14
  have s12 : leavesOK ctxLitU 183900000000 0 ((leaves.drop 32824).take 176) 188300000000 0 = true :=
    take_step (n := 2) (t := 176) (b := 32826) rfl rfl ArealUCore.ArealUK.chunk_16412 s13
  have s11 : leavesOK ctxLitU 183850000000 0 ((leaves.drop 32822).take 178) 188300000000 0 = true :=
    take_step (n := 2) (t := 178) (b := 32824) rfl rfl ArealUCore.ArealUK.chunk_16411 s12
  have s10 : leavesOK ctxLitU 183800000000 0 ((leaves.drop 32820).take 180) 188300000000 0 = true :=
    take_step (n := 2) (t := 180) (b := 32822) rfl rfl ArealUCore.ArealUK.chunk_16410 s11
  have s9 : leavesOK ctxLitU 183750000000 0 ((leaves.drop 32818).take 182) 188300000000 0 = true :=
    take_step (n := 2) (t := 182) (b := 32820) rfl rfl ArealUCore.ArealUK.chunk_16409 s10
  have s8 : leavesOK ctxLitU 183700000000 0 ((leaves.drop 32816).take 184) 188300000000 0 = true :=
    take_step (n := 2) (t := 184) (b := 32818) rfl rfl ArealUCore.ArealUK.chunk_16408 s9
  have s7 : leavesOK ctxLitU 183650000000 0 ((leaves.drop 32814).take 186) 188300000000 0 = true :=
    take_step (n := 2) (t := 186) (b := 32816) rfl rfl ArealUCore.ArealUK.chunk_16407 s8
  have s6 : leavesOK ctxLitU 183600000000 0 ((leaves.drop 32812).take 188) 188300000000 0 = true :=
    take_step (n := 2) (t := 188) (b := 32814) rfl rfl ArealUCore.ArealUK.chunk_16406 s7
  have s5 : leavesOK ctxLitU 183550000000 0 ((leaves.drop 32810).take 190) 188300000000 0 = true :=
    take_step (n := 2) (t := 190) (b := 32812) rfl rfl ArealUCore.ArealUK.chunk_16405 s6
  have s4 : leavesOK ctxLitU 183500000000 0 ((leaves.drop 32808).take 192) 188300000000 0 = true :=
    take_step (n := 2) (t := 192) (b := 32810) rfl rfl ArealUCore.ArealUK.chunk_16404 s5
  have s3 : leavesOK ctxLitU 183450000000 0 ((leaves.drop 32806).take 194) 188300000000 0 = true :=
    take_step (n := 2) (t := 194) (b := 32808) rfl rfl ArealUCore.ArealUK.chunk_16403 s4
  have s2 : leavesOK ctxLitU 183400000000 0 ((leaves.drop 32804).take 196) 188300000000 0 = true :=
    take_step (n := 2) (t := 196) (b := 32806) rfl rfl ArealUCore.ArealUK.chunk_16402 s3
  have s1 : leavesOK ctxLitU 183350000000 0 ((leaves.drop 32802).take 198) 188300000000 0 = true :=
    take_step (n := 2) (t := 198) (b := 32804) rfl rfl ArealUCore.ArealUK.chunk_16401 s2
  have s0 : leavesOK ctxLitU 183300000000 0 ((leaves.drop 32800).take 200) 188300000000 0 = true :=
    take_step (n := 2) (t := 200) (b := 32802) rfl rfl ArealUCore.ArealUK.chunk_16400 s1
  exact s0

end Areal.UCert

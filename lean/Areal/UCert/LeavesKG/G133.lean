import ArealUK.Chunk13300
import ArealUK.Chunk13301
import ArealUK.Chunk13302
import ArealUK.Chunk13303
import ArealUK.Chunk13304
import ArealUK.Chunk13305
import ArealUK.Chunk13306
import ArealUK.Chunk13307
import ArealUK.Chunk13308
import ArealUK.Chunk13309
import ArealUK.Chunk13310
import ArealUK.Chunk13311
import ArealUK.Chunk13312
import ArealUK.Chunk13313
import ArealUK.Chunk13314
import ArealUK.Chunk13315
import ArealUK.Chunk13316
import ArealUK.Chunk13317
import ArealUK.Chunk13318
import ArealUK.Chunk13319
import ArealUK.Chunk13320
import ArealUK.Chunk13321
import ArealUK.Chunk13322
import ArealUK.Chunk13323
import ArealUK.Chunk13324
import ArealUK.Chunk13325
import ArealUK.Chunk13326
import ArealUK.Chunk13327
import ArealUK.Chunk13328
import ArealUK.Chunk13329
import ArealUK.Chunk13330
import ArealUK.Chunk13331
import ArealUK.Chunk13332
import ArealUK.Chunk13333
import ArealUK.Chunk13334
import ArealUK.Chunk13335
import ArealUK.Chunk13336
import ArealUK.Chunk13337
import ArealUK.Chunk13338
import ArealUK.Chunk13339
import ArealUK.Chunk13340
import ArealUK.Chunk13341
import ArealUK.Chunk13342
import ArealUK.Chunk13343
import ArealUK.Chunk13344
import ArealUK.Chunk13345
import ArealUK.Chunk13346
import ArealUK.Chunk13347
import ArealUK.Chunk13348
import ArealUK.Chunk13349
import ArealUK.Chunk13350
import ArealUK.Chunk13351
import ArealUK.Chunk13352
import ArealUK.Chunk13353
import ArealUK.Chunk13354
import ArealUK.Chunk13355
import ArealUK.Chunk13356
import ArealUK.Chunk13357
import ArealUK.Chunk13358
import ArealUK.Chunk13359
import ArealUK.Chunk13360
import ArealUK.Chunk13361
import ArealUK.Chunk13362
import ArealUK.Chunk13363
import ArealUK.Chunk13364
import ArealUK.Chunk13365
import ArealUK.Chunk13366
import ArealUK.Chunk13367
import ArealUK.Chunk13368
import ArealUK.Chunk13369
import ArealUK.Chunk13370
import ArealUK.Chunk13371
import ArealUK.Chunk13372
import ArealUK.Chunk13373
import ArealUK.Chunk13374
import ArealUK.Chunk13375
import ArealUK.Chunk13376
import ArealUK.Chunk13377
import ArealUK.Chunk13378
import ArealUK.Chunk13379
import ArealUK.Chunk13380
import ArealUK.Chunk13381
import ArealUK.Chunk13382
import ArealUK.Chunk13383
import ArealUK.Chunk13384
import ArealUK.Chunk13385
import ArealUK.Chunk13386
import ArealUK.Chunk13387
import ArealUK.Chunk13388
import ArealUK.Chunk13389
import ArealUK.Chunk13390
import ArealUK.Chunk13391
import ArealUK.Chunk13392
import ArealUK.Chunk13393
import ArealUK.Chunk13394
import ArealUK.Chunk13395
import ArealUK.Chunk13396
import ArealUK.Chunk13397
import ArealUK.Chunk13398
import ArealUK.Chunk13399
import Areal.UCert.LeavesKGen

/-! Group 133 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_133 : leavesOK ctxLitU 542475000000 2 ((leaves.drop 26600).take 200) 136737500000 0 = true := by
  have s99 := ArealUCore.ArealUK.chunk_13399
  have s98 : leavesOK ctxLitU 273425000000 1 ((leaves.drop 26796).take 4) 136737500000 0 = true :=
    take_step (n := 2) (t := 4) (b := 26798) rfl rfl ArealUCore.ArealUK.chunk_13398 s99
  have s97 : leavesOK ctxLitU 273400000000 1 ((leaves.drop 26794).take 6) 136737500000 0 = true :=
    take_step (n := 2) (t := 6) (b := 26796) rfl rfl ArealUCore.ArealUK.chunk_13397 s98
  have s96 : leavesOK ctxLitU 273375000000 1 ((leaves.drop 26792).take 8) 136737500000 0 = true :=
    take_step (n := 2) (t := 8) (b := 26794) rfl rfl ArealUCore.ArealUK.chunk_13396 s97
  have s95 : leavesOK ctxLitU 273350000000 1 ((leaves.drop 26790).take 10) 136737500000 0 = true :=
    take_step (n := 2) (t := 10) (b := 26792) rfl rfl ArealUCore.ArealUK.chunk_13395 s96
  have s94 : leavesOK ctxLitU 136662500000 0 ((leaves.drop 26788).take 12) 136737500000 0 = true :=
    take_step (n := 2) (t := 12) (b := 26790) rfl rfl ArealUCore.ArealUK.chunk_13394 s95
  have s93 : leavesOK ctxLitU 136650000000 0 ((leaves.drop 26786).take 14) 136737500000 0 = true :=
    take_step (n := 2) (t := 14) (b := 26788) rfl rfl ArealUCore.ArealUK.chunk_13393 s94
  have s92 : leavesOK ctxLitU 136637500000 0 ((leaves.drop 26784).take 16) 136737500000 0 = true :=
    take_step (n := 2) (t := 16) (b := 26786) rfl rfl ArealUCore.ArealUK.chunk_13392 s93
  have s91 : leavesOK ctxLitU 273256250000 1 ((leaves.drop 26782).take 18) 136737500000 0 = true :=
    take_step (n := 2) (t := 18) (b := 26784) rfl rfl ArealUCore.ArealUK.chunk_13391 s92
  have s90 : leavesOK ctxLitU 273237500000 1 ((leaves.drop 26780).take 20) 136737500000 0 = true :=
    take_step (n := 2) (t := 20) (b := 26782) rfl rfl ArealUCore.ArealUK.chunk_13390 s91
  have s89 : leavesOK ctxLitU 273212500000 1 ((leaves.drop 26778).take 22) 136737500000 0 = true :=
    take_step (n := 2) (t := 22) (b := 26780) rfl rfl ArealUCore.ArealUK.chunk_13389 s90
  have s88 : leavesOK ctxLitU 273187500000 1 ((leaves.drop 26776).take 24) 136737500000 0 = true :=
    take_step (n := 2) (t := 24) (b := 26778) rfl rfl ArealUCore.ArealUK.chunk_13388 s89
  have s87 : leavesOK ctxLitU 273162500000 1 ((leaves.drop 26774).take 26) 136737500000 0 = true :=
    take_step (n := 2) (t := 26) (b := 26776) rfl rfl ArealUCore.ArealUK.chunk_13387 s88
  have s86 : leavesOK ctxLitU 273143750000 1 ((leaves.drop 26772).take 28) 136737500000 0 = true :=
    take_step (n := 2) (t := 28) (b := 26774) rfl rfl ArealUCore.ArealUK.chunk_13386 s87
  have s85 : leavesOK ctxLitU 273131250000 1 ((leaves.drop 26770).take 30) 136737500000 0 = true :=
    take_step (n := 2) (t := 30) (b := 26772) rfl rfl ArealUCore.ArealUK.chunk_13385 s86
  have s84 : leavesOK ctxLitU 136556250000 0 ((leaves.drop 26768).take 32) 136737500000 0 = true :=
    take_step (n := 2) (t := 32) (b := 26770) rfl rfl ArealUCore.ArealUK.chunk_13384 s85
  have s83 : leavesOK ctxLitU 273087500000 1 ((leaves.drop 26766).take 34) 136737500000 0 = true :=
    take_step (n := 2) (t := 34) (b := 26768) rfl rfl ArealUCore.ArealUK.chunk_13383 s84
  have s82 : leavesOK ctxLitU 273062500000 1 ((leaves.drop 26764).take 36) 136737500000 0 = true :=
    take_step (n := 2) (t := 36) (b := 26766) rfl rfl ArealUCore.ArealUK.chunk_13382 s83
  have s81 : leavesOK ctxLitU 546075000000 2 ((leaves.drop 26762).take 38) 136737500000 0 = true :=
    take_step (n := 2) (t := 38) (b := 26764) rfl rfl ArealUCore.ArealUK.chunk_13381 s82
  have s80 : leavesOK ctxLitU 546025000000 2 ((leaves.drop 26760).take 40) 136737500000 0 = true :=
    take_step (n := 2) (t := 40) (b := 26762) rfl rfl ArealUCore.ArealUK.chunk_13380 s81
  have s79 : leavesOK ctxLitU 545975000000 2 ((leaves.drop 26758).take 42) 136737500000 0 = true :=
    take_step (n := 2) (t := 42) (b := 26760) rfl rfl ArealUCore.ArealUK.chunk_13379 s80
  have s78 : leavesOK ctxLitU 545925000000 2 ((leaves.drop 26756).take 44) 136737500000 0 = true :=
    take_step (n := 2) (t := 44) (b := 26758) rfl rfl ArealUCore.ArealUK.chunk_13378 s79
  have s77 : leavesOK ctxLitU 272937500000 1 ((leaves.drop 26754).take 46) 136737500000 0 = true :=
    take_step (n := 2) (t := 46) (b := 26756) rfl rfl ArealUCore.ArealUK.chunk_13377 s78
  have s76 : leavesOK ctxLitU 272912500000 1 ((leaves.drop 26752).take 48) 136737500000 0 = true :=
    take_step (n := 2) (t := 48) (b := 26754) rfl rfl ArealUCore.ArealUK.chunk_13376 s77
  have s75 : leavesOK ctxLitU 136443750000 0 ((leaves.drop 26750).take 50) 136737500000 0 = true :=
    take_step (n := 2) (t := 50) (b := 26752) rfl rfl ArealUCore.ArealUK.chunk_13375 s76
  have s74 : leavesOK ctxLitU 136431250000 0 ((leaves.drop 26748).take 52) 136737500000 0 = true :=
    take_step (n := 2) (t := 52) (b := 26750) rfl rfl ArealUCore.ArealUK.chunk_13374 s75
  have s73 : leavesOK ctxLitU 272837500000 1 ((leaves.drop 26746).take 54) 136737500000 0 = true :=
    take_step (n := 2) (t := 54) (b := 26748) rfl rfl ArealUCore.ArealUK.chunk_13373 s74
  have s72 : leavesOK ctxLitU 272812500000 1 ((leaves.drop 26744).take 56) 136737500000 0 = true :=
    take_step (n := 2) (t := 56) (b := 26746) rfl rfl ArealUCore.ArealUK.chunk_13372 s73
  have s71 : leavesOK ctxLitU 272787500000 1 ((leaves.drop 26742).take 58) 136737500000 0 = true :=
    take_step (n := 2) (t := 58) (b := 26744) rfl rfl ArealUCore.ArealUK.chunk_13371 s72
  have s70 : leavesOK ctxLitU 272762500000 1 ((leaves.drop 26740).take 60) 136737500000 0 = true :=
    take_step (n := 2) (t := 60) (b := 26742) rfl rfl ArealUCore.ArealUK.chunk_13370 s71
  have s69 : leavesOK ctxLitU 136368750000 0 ((leaves.drop 26738).take 62) 136737500000 0 = true :=
    take_step (n := 2) (t := 62) (b := 26740) rfl rfl ArealUCore.ArealUK.chunk_13369 s70
  have s68 : leavesOK ctxLitU 136356250000 0 ((leaves.drop 26736).take 64) 136737500000 0 = true :=
    take_step (n := 2) (t := 64) (b := 26738) rfl rfl ArealUCore.ArealUK.chunk_13368 s69
  have s67 : leavesOK ctxLitU 136343750000 0 ((leaves.drop 26734).take 66) 136737500000 0 = true :=
    take_step (n := 2) (t := 66) (b := 26736) rfl rfl ArealUCore.ArealUK.chunk_13367 s68
  have s66 : leavesOK ctxLitU 136331250000 0 ((leaves.drop 26732).take 68) 136737500000 0 = true :=
    take_step (n := 2) (t := 68) (b := 26734) rfl rfl ArealUCore.ArealUK.chunk_13366 s67
  have s65 : leavesOK ctxLitU 272637500000 1 ((leaves.drop 26730).take 70) 136737500000 0 = true :=
    take_step (n := 2) (t := 70) (b := 26732) rfl rfl ArealUCore.ArealUK.chunk_13365 s66
  have s64 : leavesOK ctxLitU 272612500000 1 ((leaves.drop 26728).take 72) 136737500000 0 = true :=
    take_step (n := 2) (t := 72) (b := 26730) rfl rfl ArealUCore.ArealUK.chunk_13364 s65
  have s63 : leavesOK ctxLitU 272587500000 1 ((leaves.drop 26726).take 74) 136737500000 0 = true :=
    take_step (n := 2) (t := 74) (b := 26728) rfl rfl ArealUCore.ArealUK.chunk_13363 s64
  have s62 : leavesOK ctxLitU 545150000000 2 ((leaves.drop 26724).take 76) 136737500000 0 = true :=
    take_step (n := 2) (t := 76) (b := 26726) rfl rfl ArealUCore.ArealUK.chunk_13362 s63
  have s61 : leavesOK ctxLitU 272550000000 1 ((leaves.drop 26722).take 78) 136737500000 0 = true :=
    take_step (n := 2) (t := 78) (b := 26724) rfl rfl ArealUCore.ArealUK.chunk_13361 s62
  have s60 : leavesOK ctxLitU 136262500000 0 ((leaves.drop 26720).take 80) 136737500000 0 = true :=
    take_step (n := 2) (t := 80) (b := 26722) rfl rfl ArealUCore.ArealUK.chunk_13360 s61
  have s59 : leavesOK ctxLitU 136250000000 0 ((leaves.drop 26718).take 82) 136737500000 0 = true :=
    take_step (n := 2) (t := 82) (b := 26720) rfl rfl ArealUCore.ArealUK.chunk_13359 s60
  have s58 : leavesOK ctxLitU 136237500000 0 ((leaves.drop 26716).take 84) 136737500000 0 = true :=
    take_step (n := 2) (t := 84) (b := 26718) rfl rfl ArealUCore.ArealUK.chunk_13358 s59
  have s57 : leavesOK ctxLitU 136225000000 0 ((leaves.drop 26714).take 86) 136737500000 0 = true :=
    take_step (n := 2) (t := 86) (b := 26716) rfl rfl ArealUCore.ArealUK.chunk_13357 s58
  have s56 : leavesOK ctxLitU 272425000000 1 ((leaves.drop 26712).take 88) 136737500000 0 = true :=
    take_step (n := 2) (t := 88) (b := 26714) rfl rfl ArealUCore.ArealUK.chunk_13356 s57
  have s55 : leavesOK ctxLitU 272400000000 1 ((leaves.drop 26710).take 90) 136737500000 0 = true :=
    take_step (n := 2) (t := 90) (b := 26712) rfl rfl ArealUCore.ArealUK.chunk_13355 s56
  have s54 : leavesOK ctxLitU 544750000000 2 ((leaves.drop 26708).take 92) 136737500000 0 = true :=
    take_step (n := 2) (t := 92) (b := 26710) rfl rfl ArealUCore.ArealUK.chunk_13354 s55
  have s53 : leavesOK ctxLitU 544700000000 2 ((leaves.drop 26706).take 94) 136737500000 0 = true :=
    take_step (n := 2) (t := 94) (b := 26708) rfl rfl ArealUCore.ArealUK.chunk_13353 s54
  have s52 : leavesOK ctxLitU 544650000000 2 ((leaves.drop 26704).take 96) 136737500000 0 = true :=
    take_step (n := 2) (t := 96) (b := 26706) rfl rfl ArealUCore.ArealUK.chunk_13352 s53
  have s51 : leavesOK ctxLitU 544600000000 2 ((leaves.drop 26702).take 98) 136737500000 0 = true :=
    take_step (n := 2) (t := 98) (b := 26704) rfl rfl ArealUCore.ArealUK.chunk_13351 s52
  have s50 : leavesOK ctxLitU 544550000000 2 ((leaves.drop 26700).take 100) 136737500000 0 = true :=
    take_step (n := 2) (t := 100) (b := 26702) rfl rfl ArealUCore.ArealUK.chunk_13350 s51
  have s49 : leavesOK ctxLitU 544500000000 2 ((leaves.drop 26698).take 102) 136737500000 0 = true :=
    take_step (n := 2) (t := 102) (b := 26700) rfl rfl ArealUCore.ArealUK.chunk_13349 s50
  have s48 : leavesOK ctxLitU 544450000000 2 ((leaves.drop 26696).take 104) 136737500000 0 = true :=
    take_step (n := 2) (t := 104) (b := 26698) rfl rfl ArealUCore.ArealUK.chunk_13348 s49
  have s47 : leavesOK ctxLitU 544400000000 2 ((leaves.drop 26694).take 106) 136737500000 0 = true :=
    take_step (n := 2) (t := 106) (b := 26696) rfl rfl ArealUCore.ArealUK.chunk_13347 s48
  have s46 : leavesOK ctxLitU 544362500000 2 ((leaves.drop 26692).take 108) 136737500000 0 = true :=
    take_step (n := 2) (t := 108) (b := 26694) rfl rfl ArealUCore.ArealUK.chunk_13346 s47
  have s45 : leavesOK ctxLitU 544337500000 2 ((leaves.drop 26690).take 110) 136737500000 0 = true :=
    take_step (n := 2) (t := 110) (b := 26692) rfl rfl ArealUCore.ArealUK.chunk_13345 s46
  have s44 : leavesOK ctxLitU 272150000000 1 ((leaves.drop 26688).take 112) 136737500000 0 = true :=
    take_step (n := 2) (t := 112) (b := 26690) rfl rfl ArealUCore.ArealUK.chunk_13344 s45
  have s43 : leavesOK ctxLitU 136062500000 0 ((leaves.drop 26686).take 114) 136737500000 0 = true :=
    take_step (n := 2) (t := 114) (b := 26688) rfl rfl ArealUCore.ArealUK.chunk_13343 s44
  have s42 : leavesOK ctxLitU 136050000000 0 ((leaves.drop 26684).take 116) 136737500000 0 = true :=
    take_step (n := 2) (t := 116) (b := 26686) rfl rfl ArealUCore.ArealUK.chunk_13342 s43
  have s41 : leavesOK ctxLitU 136037500000 0 ((leaves.drop 26682).take 118) 136737500000 0 = true :=
    take_step (n := 2) (t := 118) (b := 26684) rfl rfl ArealUCore.ArealUK.chunk_13341 s42
  have s40 : leavesOK ctxLitU 272062500000 1 ((leaves.drop 26680).take 120) 136737500000 0 = true :=
    take_step (n := 2) (t := 120) (b := 26682) rfl rfl ArealUCore.ArealUK.chunk_13340 s41
  have s39 : leavesOK ctxLitU 272050000000 1 ((leaves.drop 26678).take 122) 136737500000 0 = true :=
    take_step (n := 2) (t := 122) (b := 26680) rfl rfl ArealUCore.ArealUK.chunk_13339 s40
  have s38 : leavesOK ctxLitU 272025000000 1 ((leaves.drop 26676).take 124) 136737500000 0 = true :=
    take_step (n := 2) (t := 124) (b := 26678) rfl rfl ArealUCore.ArealUK.chunk_13338 s39
  have s37 : leavesOK ctxLitU 272000000000 1 ((leaves.drop 26674).take 126) 136737500000 0 = true :=
    take_step (n := 2) (t := 126) (b := 26676) rfl rfl ArealUCore.ArealUK.chunk_13337 s38
  have s36 : leavesOK ctxLitU 271975000000 1 ((leaves.drop 26672).take 128) 136737500000 0 = true :=
    take_step (n := 2) (t := 128) (b := 26674) rfl rfl ArealUCore.ArealUK.chunk_13336 s37
  have s35 : leavesOK ctxLitU 271950000000 1 ((leaves.drop 26670).take 130) 136737500000 0 = true :=
    take_step (n := 2) (t := 130) (b := 26672) rfl rfl ArealUCore.ArealUK.chunk_13335 s36
  have s34 : leavesOK ctxLitU 271937500000 1 ((leaves.drop 26668).take 132) 136737500000 0 = true :=
    take_step (n := 2) (t := 132) (b := 26670) rfl rfl ArealUCore.ArealUK.chunk_13334 s35
  have s33 : leavesOK ctxLitU 135956250000 0 ((leaves.drop 26666).take 134) 136737500000 0 = true :=
    take_step (n := 2) (t := 134) (b := 26668) rfl rfl ArealUCore.ArealUK.chunk_13333 s34
  have s32 : leavesOK ctxLitU 135943750000 0 ((leaves.drop 26664).take 136) 136737500000 0 = true :=
    take_step (n := 2) (t := 136) (b := 26666) rfl rfl ArealUCore.ArealUK.chunk_13332 s33
  have s31 : leavesOK ctxLitU 271868750000 1 ((leaves.drop 26662).take 138) 136737500000 0 = true :=
    take_step (n := 2) (t := 138) (b := 26664) rfl rfl ArealUCore.ArealUK.chunk_13331 s32
  have s30 : leavesOK ctxLitU 271856250000 1 ((leaves.drop 26660).take 140) 136737500000 0 = true :=
    take_step (n := 2) (t := 140) (b := 26662) rfl rfl ArealUCore.ArealUK.chunk_13330 s31
  have s29 : leavesOK ctxLitU 271837500000 1 ((leaves.drop 26658).take 142) 136737500000 0 = true :=
    take_step (n := 2) (t := 142) (b := 26660) rfl rfl ArealUCore.ArealUK.chunk_13329 s30
  have s28 : leavesOK ctxLitU 271812500000 1 ((leaves.drop 26656).take 144) 136737500000 0 = true :=
    take_step (n := 2) (t := 144) (b := 26658) rfl rfl ArealUCore.ArealUK.chunk_13328 s29
  have s27 : leavesOK ctxLitU 271787500000 1 ((leaves.drop 26654).take 146) 136737500000 0 = true :=
    take_step (n := 2) (t := 146) (b := 26656) rfl rfl ArealUCore.ArealUK.chunk_13327 s28
  have s26 : leavesOK ctxLitU 271762500000 1 ((leaves.drop 26652).take 148) 136737500000 0 = true :=
    take_step (n := 2) (t := 148) (b := 26654) rfl rfl ArealUCore.ArealUK.chunk_13326 s27
  have s25 : leavesOK ctxLitU 271743750000 1 ((leaves.drop 26650).take 150) 136737500000 0 = true :=
    take_step (n := 2) (t := 150) (b := 26652) rfl rfl ArealUCore.ArealUK.chunk_13325 s26
  have s24 : leavesOK ctxLitU 271731250000 1 ((leaves.drop 26648).take 152) 136737500000 0 = true :=
    take_step (n := 2) (t := 152) (b := 26650) rfl rfl ArealUCore.ArealUK.chunk_13324 s25
  have s23 : leavesOK ctxLitU 135856250000 0 ((leaves.drop 26646).take 154) 136737500000 0 = true :=
    take_step (n := 2) (t := 154) (b := 26648) rfl rfl ArealUCore.ArealUK.chunk_13323 s24
  have s22 : leavesOK ctxLitU 135843750000 0 ((leaves.drop 26644).take 156) 136737500000 0 = true :=
    take_step (n := 2) (t := 156) (b := 26646) rfl rfl ArealUCore.ArealUK.chunk_13322 s23
  have s21 : leavesOK ctxLitU 271668750000 1 ((leaves.drop 26642).take 158) 136737500000 0 = true :=
    take_step (n := 2) (t := 158) (b := 26644) rfl rfl ArealUCore.ArealUK.chunk_13321 s22
  have s20 : leavesOK ctxLitU 271656250000 1 ((leaves.drop 26640).take 160) 136737500000 0 = true :=
    take_step (n := 2) (t := 160) (b := 26642) rfl rfl ArealUCore.ArealUK.chunk_13320 s21
  have s19 : leavesOK ctxLitU 271637500000 1 ((leaves.drop 26638).take 162) 136737500000 0 = true :=
    take_step (n := 2) (t := 162) (b := 26640) rfl rfl ArealUCore.ArealUK.chunk_13319 s20
  have s18 : leavesOK ctxLitU 271612500000 1 ((leaves.drop 26636).take 164) 136737500000 0 = true :=
    take_step (n := 2) (t := 164) (b := 26638) rfl rfl ArealUCore.ArealUK.chunk_13318 s19
  have s17 : leavesOK ctxLitU 271587500000 1 ((leaves.drop 26634).take 166) 136737500000 0 = true :=
    take_step (n := 2) (t := 166) (b := 26636) rfl rfl ArealUCore.ArealUK.chunk_13317 s18
  have s16 : leavesOK ctxLitU 271562500000 1 ((leaves.drop 26632).take 168) 136737500000 0 = true :=
    take_step (n := 2) (t := 168) (b := 26634) rfl rfl ArealUCore.ArealUK.chunk_13316 s17
  have s15 : leavesOK ctxLitU 271543750000 1 ((leaves.drop 26630).take 170) 136737500000 0 = true :=
    take_step (n := 2) (t := 170) (b := 26632) rfl rfl ArealUCore.ArealUK.chunk_13315 s16
  have s14 : leavesOK ctxLitU 271531250000 1 ((leaves.drop 26628).take 172) 136737500000 0 = true :=
    take_step (n := 2) (t := 172) (b := 26630) rfl rfl ArealUCore.ArealUK.chunk_13314 s15
  have s13 : leavesOK ctxLitU 135756250000 0 ((leaves.drop 26626).take 174) 136737500000 0 = true :=
    take_step (n := 2) (t := 174) (b := 26628) rfl rfl ArealUCore.ArealUK.chunk_13313 s14
  have s12 : leavesOK ctxLitU 135743750000 0 ((leaves.drop 26624).take 176) 136737500000 0 = true :=
    take_step (n := 2) (t := 176) (b := 26626) rfl rfl ArealUCore.ArealUK.chunk_13312 s13
  have s11 : leavesOK ctxLitU 271468750000 1 ((leaves.drop 26622).take 178) 136737500000 0 = true :=
    take_step (n := 2) (t := 178) (b := 26624) rfl rfl ArealUCore.ArealUK.chunk_13311 s12
  have s10 : leavesOK ctxLitU 271456250000 1 ((leaves.drop 26620).take 180) 136737500000 0 = true :=
    take_step (n := 2) (t := 180) (b := 26622) rfl rfl ArealUCore.ArealUK.chunk_13310 s11
  have s9 : leavesOK ctxLitU 271437500000 1 ((leaves.drop 26618).take 182) 136737500000 0 = true :=
    take_step (n := 2) (t := 182) (b := 26620) rfl rfl ArealUCore.ArealUK.chunk_13309 s10
  have s8 : leavesOK ctxLitU 271412500000 1 ((leaves.drop 26616).take 184) 136737500000 0 = true :=
    take_step (n := 2) (t := 184) (b := 26618) rfl rfl ArealUCore.ArealUK.chunk_13308 s9
  have s7 : leavesOK ctxLitU 271387500000 1 ((leaves.drop 26614).take 186) 136737500000 0 = true :=
    take_step (n := 2) (t := 186) (b := 26616) rfl rfl ArealUCore.ArealUK.chunk_13307 s8
  have s6 : leavesOK ctxLitU 271362500000 1 ((leaves.drop 26612).take 188) 136737500000 0 = true :=
    take_step (n := 2) (t := 188) (b := 26614) rfl rfl ArealUCore.ArealUK.chunk_13306 s7
  have s5 : leavesOK ctxLitU 271343750000 1 ((leaves.drop 26610).take 190) 136737500000 0 = true :=
    take_step (n := 2) (t := 190) (b := 26612) rfl rfl ArealUCore.ArealUK.chunk_13305 s6
  have s4 : leavesOK ctxLitU 271331250000 1 ((leaves.drop 26608).take 192) 136737500000 0 = true :=
    take_step (n := 2) (t := 192) (b := 26610) rfl rfl ArealUCore.ArealUK.chunk_13304 s5
  have s3 : leavesOK ctxLitU 135656250000 0 ((leaves.drop 26606).take 194) 136737500000 0 = true :=
    take_step (n := 2) (t := 194) (b := 26608) rfl rfl ArealUCore.ArealUK.chunk_13303 s4
  have s2 : leavesOK ctxLitU 271287500000 1 ((leaves.drop 26604).take 196) 136737500000 0 = true :=
    take_step (n := 2) (t := 196) (b := 26606) rfl rfl ArealUCore.ArealUK.chunk_13302 s3
  have s1 : leavesOK ctxLitU 271262500000 1 ((leaves.drop 26602).take 198) 136737500000 0 = true :=
    take_step (n := 2) (t := 198) (b := 26604) rfl rfl ArealUCore.ArealUK.chunk_13301 s2
  have s0 : leavesOK ctxLitU 542475000000 2 ((leaves.drop 26600).take 200) 136737500000 0 = true :=
    take_step (n := 2) (t := 200) (b := 26602) rfl rfl ArealUCore.ArealUK.chunk_13300 s1
  exact s0

end Areal.UCert

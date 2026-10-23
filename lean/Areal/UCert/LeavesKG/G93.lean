import ArealUK.Chunk9300
import ArealUK.Chunk9301
import ArealUK.Chunk9302
import ArealUK.Chunk9303
import ArealUK.Chunk9304
import ArealUK.Chunk9305
import ArealUK.Chunk9306
import ArealUK.Chunk9307
import ArealUK.Chunk9308
import ArealUK.Chunk9309
import ArealUK.Chunk9310
import ArealUK.Chunk9311
import ArealUK.Chunk9312
import ArealUK.Chunk9313
import ArealUK.Chunk9314
import ArealUK.Chunk9315
import ArealUK.Chunk9316
import ArealUK.Chunk9317
import ArealUK.Chunk9318
import ArealUK.Chunk9319
import ArealUK.Chunk9320
import ArealUK.Chunk9321
import ArealUK.Chunk9322
import ArealUK.Chunk9323
import ArealUK.Chunk9324
import ArealUK.Chunk9325
import ArealUK.Chunk9326
import ArealUK.Chunk9327
import ArealUK.Chunk9328
import ArealUK.Chunk9329
import ArealUK.Chunk9330
import ArealUK.Chunk9331
import ArealUK.Chunk9332
import ArealUK.Chunk9333
import ArealUK.Chunk9334
import ArealUK.Chunk9335
import ArealUK.Chunk9336
import ArealUK.Chunk9337
import ArealUK.Chunk9338
import ArealUK.Chunk9339
import ArealUK.Chunk9340
import ArealUK.Chunk9341
import ArealUK.Chunk9342
import ArealUK.Chunk9343
import ArealUK.Chunk9344
import ArealUK.Chunk9345
import ArealUK.Chunk9346
import ArealUK.Chunk9347
import ArealUK.Chunk9348
import ArealUK.Chunk9349
import ArealUK.Chunk9350
import ArealUK.Chunk9351
import ArealUK.Chunk9352
import ArealUK.Chunk9353
import ArealUK.Chunk9354
import ArealUK.Chunk9355
import ArealUK.Chunk9356
import ArealUK.Chunk9357
import ArealUK.Chunk9358
import ArealUK.Chunk9359
import ArealUK.Chunk9360
import ArealUK.Chunk9361
import ArealUK.Chunk9362
import ArealUK.Chunk9363
import ArealUK.Chunk9364
import ArealUK.Chunk9365
import ArealUK.Chunk9366
import ArealUK.Chunk9367
import ArealUK.Chunk9368
import ArealUK.Chunk9369
import ArealUK.Chunk9370
import ArealUK.Chunk9371
import ArealUK.Chunk9372
import ArealUK.Chunk9373
import ArealUK.Chunk9374
import ArealUK.Chunk9375
import ArealUK.Chunk9376
import ArealUK.Chunk9377
import ArealUK.Chunk9378
import ArealUK.Chunk9379
import ArealUK.Chunk9380
import ArealUK.Chunk9381
import ArealUK.Chunk9382
import ArealUK.Chunk9383
import ArealUK.Chunk9384
import ArealUK.Chunk9385
import ArealUK.Chunk9386
import ArealUK.Chunk9387
import ArealUK.Chunk9388
import ArealUK.Chunk9389
import ArealUK.Chunk9390
import ArealUK.Chunk9391
import ArealUK.Chunk9392
import ArealUK.Chunk9393
import ArealUK.Chunk9394
import ArealUK.Chunk9395
import ArealUK.Chunk9396
import ArealUK.Chunk9397
import ArealUK.Chunk9398
import ArealUK.Chunk9399
import Areal.UCert.LeavesKGen

/-! Group 93 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_93 : leavesOK ctxLitU 319875000000 2 ((leaves.drop 18600).take 200) 324875000000 2 = true := by
  have s99 := ArealUCore.ArealUK.chunk_9399
  have s98 : leavesOK ctxLitU 324775000000 2 ((leaves.drop 18796).take 4) 324875000000 2 = true :=
    take_step (n := 2) (t := 4) (b := 18798) rfl rfl ArealUCore.ArealUK.chunk_9398 s99
  have s97 : leavesOK ctxLitU 324725000000 2 ((leaves.drop 18794).take 6) 324875000000 2 = true :=
    take_step (n := 2) (t := 6) (b := 18796) rfl rfl ArealUCore.ArealUK.chunk_9397 s98
  have s96 : leavesOK ctxLitU 324675000000 2 ((leaves.drop 18792).take 8) 324875000000 2 = true :=
    take_step (n := 2) (t := 8) (b := 18794) rfl rfl ArealUCore.ArealUK.chunk_9396 s97
  have s95 : leavesOK ctxLitU 324625000000 2 ((leaves.drop 18790).take 10) 324875000000 2 = true :=
    take_step (n := 2) (t := 10) (b := 18792) rfl rfl ArealUCore.ArealUK.chunk_9395 s96
  have s94 : leavesOK ctxLitU 324575000000 2 ((leaves.drop 18788).take 12) 324875000000 2 = true :=
    take_step (n := 2) (t := 12) (b := 18790) rfl rfl ArealUCore.ArealUK.chunk_9394 s95
  have s93 : leavesOK ctxLitU 324525000000 2 ((leaves.drop 18786).take 14) 324875000000 2 = true :=
    take_step (n := 2) (t := 14) (b := 18788) rfl rfl ArealUCore.ArealUK.chunk_9393 s94
  have s92 : leavesOK ctxLitU 324475000000 2 ((leaves.drop 18784).take 16) 324875000000 2 = true :=
    take_step (n := 2) (t := 16) (b := 18786) rfl rfl ArealUCore.ArealUK.chunk_9392 s93
  have s91 : leavesOK ctxLitU 324425000000 2 ((leaves.drop 18782).take 18) 324875000000 2 = true :=
    take_step (n := 2) (t := 18) (b := 18784) rfl rfl ArealUCore.ArealUK.chunk_9391 s92
  have s90 : leavesOK ctxLitU 324375000000 2 ((leaves.drop 18780).take 20) 324875000000 2 = true :=
    take_step (n := 2) (t := 20) (b := 18782) rfl rfl ArealUCore.ArealUK.chunk_9390 s91
  have s89 : leavesOK ctxLitU 324325000000 2 ((leaves.drop 18778).take 22) 324875000000 2 = true :=
    take_step (n := 2) (t := 22) (b := 18780) rfl rfl ArealUCore.ArealUK.chunk_9389 s90
  have s88 : leavesOK ctxLitU 324275000000 2 ((leaves.drop 18776).take 24) 324875000000 2 = true :=
    take_step (n := 2) (t := 24) (b := 18778) rfl rfl ArealUCore.ArealUK.chunk_9388 s89
  have s87 : leavesOK ctxLitU 324225000000 2 ((leaves.drop 18774).take 26) 324875000000 2 = true :=
    take_step (n := 2) (t := 26) (b := 18776) rfl rfl ArealUCore.ArealUK.chunk_9387 s88
  have s86 : leavesOK ctxLitU 324175000000 2 ((leaves.drop 18772).take 28) 324875000000 2 = true :=
    take_step (n := 2) (t := 28) (b := 18774) rfl rfl ArealUCore.ArealUK.chunk_9386 s87
  have s85 : leavesOK ctxLitU 324125000000 2 ((leaves.drop 18770).take 30) 324875000000 2 = true :=
    take_step (n := 2) (t := 30) (b := 18772) rfl rfl ArealUCore.ArealUK.chunk_9385 s86
  have s84 : leavesOK ctxLitU 324075000000 2 ((leaves.drop 18768).take 32) 324875000000 2 = true :=
    take_step (n := 2) (t := 32) (b := 18770) rfl rfl ArealUCore.ArealUK.chunk_9384 s85
  have s83 : leavesOK ctxLitU 324025000000 2 ((leaves.drop 18766).take 34) 324875000000 2 = true :=
    take_step (n := 2) (t := 34) (b := 18768) rfl rfl ArealUCore.ArealUK.chunk_9383 s84
  have s82 : leavesOK ctxLitU 323975000000 2 ((leaves.drop 18764).take 36) 324875000000 2 = true :=
    take_step (n := 2) (t := 36) (b := 18766) rfl rfl ArealUCore.ArealUK.chunk_9382 s83
  have s81 : leavesOK ctxLitU 323925000000 2 ((leaves.drop 18762).take 38) 324875000000 2 = true :=
    take_step (n := 2) (t := 38) (b := 18764) rfl rfl ArealUCore.ArealUK.chunk_9381 s82
  have s80 : leavesOK ctxLitU 323875000000 2 ((leaves.drop 18760).take 40) 324875000000 2 = true :=
    take_step (n := 2) (t := 40) (b := 18762) rfl rfl ArealUCore.ArealUK.chunk_9380 s81
  have s79 : leavesOK ctxLitU 323825000000 2 ((leaves.drop 18758).take 42) 324875000000 2 = true :=
    take_step (n := 2) (t := 42) (b := 18760) rfl rfl ArealUCore.ArealUK.chunk_9379 s80
  have s78 : leavesOK ctxLitU 323775000000 2 ((leaves.drop 18756).take 44) 324875000000 2 = true :=
    take_step (n := 2) (t := 44) (b := 18758) rfl rfl ArealUCore.ArealUK.chunk_9378 s79
  have s77 : leavesOK ctxLitU 323725000000 2 ((leaves.drop 18754).take 46) 324875000000 2 = true :=
    take_step (n := 2) (t := 46) (b := 18756) rfl rfl ArealUCore.ArealUK.chunk_9377 s78
  have s76 : leavesOK ctxLitU 323675000000 2 ((leaves.drop 18752).take 48) 324875000000 2 = true :=
    take_step (n := 2) (t := 48) (b := 18754) rfl rfl ArealUCore.ArealUK.chunk_9376 s77
  have s75 : leavesOK ctxLitU 323625000000 2 ((leaves.drop 18750).take 50) 324875000000 2 = true :=
    take_step (n := 2) (t := 50) (b := 18752) rfl rfl ArealUCore.ArealUK.chunk_9375 s76
  have s74 : leavesOK ctxLitU 323575000000 2 ((leaves.drop 18748).take 52) 324875000000 2 = true :=
    take_step (n := 2) (t := 52) (b := 18750) rfl rfl ArealUCore.ArealUK.chunk_9374 s75
  have s73 : leavesOK ctxLitU 323525000000 2 ((leaves.drop 18746).take 54) 324875000000 2 = true :=
    take_step (n := 2) (t := 54) (b := 18748) rfl rfl ArealUCore.ArealUK.chunk_9373 s74
  have s72 : leavesOK ctxLitU 323475000000 2 ((leaves.drop 18744).take 56) 324875000000 2 = true :=
    take_step (n := 2) (t := 56) (b := 18746) rfl rfl ArealUCore.ArealUK.chunk_9372 s73
  have s71 : leavesOK ctxLitU 323425000000 2 ((leaves.drop 18742).take 58) 324875000000 2 = true :=
    take_step (n := 2) (t := 58) (b := 18744) rfl rfl ArealUCore.ArealUK.chunk_9371 s72
  have s70 : leavesOK ctxLitU 323375000000 2 ((leaves.drop 18740).take 60) 324875000000 2 = true :=
    take_step (n := 2) (t := 60) (b := 18742) rfl rfl ArealUCore.ArealUK.chunk_9370 s71
  have s69 : leavesOK ctxLitU 323325000000 2 ((leaves.drop 18738).take 62) 324875000000 2 = true :=
    take_step (n := 2) (t := 62) (b := 18740) rfl rfl ArealUCore.ArealUK.chunk_9369 s70
  have s68 : leavesOK ctxLitU 323275000000 2 ((leaves.drop 18736).take 64) 324875000000 2 = true :=
    take_step (n := 2) (t := 64) (b := 18738) rfl rfl ArealUCore.ArealUK.chunk_9368 s69
  have s67 : leavesOK ctxLitU 323225000000 2 ((leaves.drop 18734).take 66) 324875000000 2 = true :=
    take_step (n := 2) (t := 66) (b := 18736) rfl rfl ArealUCore.ArealUK.chunk_9367 s68
  have s66 : leavesOK ctxLitU 323175000000 2 ((leaves.drop 18732).take 68) 324875000000 2 = true :=
    take_step (n := 2) (t := 68) (b := 18734) rfl rfl ArealUCore.ArealUK.chunk_9366 s67
  have s65 : leavesOK ctxLitU 323125000000 2 ((leaves.drop 18730).take 70) 324875000000 2 = true :=
    take_step (n := 2) (t := 70) (b := 18732) rfl rfl ArealUCore.ArealUK.chunk_9365 s66
  have s64 : leavesOK ctxLitU 323075000000 2 ((leaves.drop 18728).take 72) 324875000000 2 = true :=
    take_step (n := 2) (t := 72) (b := 18730) rfl rfl ArealUCore.ArealUK.chunk_9364 s65
  have s63 : leavesOK ctxLitU 323025000000 2 ((leaves.drop 18726).take 74) 324875000000 2 = true :=
    take_step (n := 2) (t := 74) (b := 18728) rfl rfl ArealUCore.ArealUK.chunk_9363 s64
  have s62 : leavesOK ctxLitU 322975000000 2 ((leaves.drop 18724).take 76) 324875000000 2 = true :=
    take_step (n := 2) (t := 76) (b := 18726) rfl rfl ArealUCore.ArealUK.chunk_9362 s63
  have s61 : leavesOK ctxLitU 322925000000 2 ((leaves.drop 18722).take 78) 324875000000 2 = true :=
    take_step (n := 2) (t := 78) (b := 18724) rfl rfl ArealUCore.ArealUK.chunk_9361 s62
  have s60 : leavesOK ctxLitU 322875000000 2 ((leaves.drop 18720).take 80) 324875000000 2 = true :=
    take_step (n := 2) (t := 80) (b := 18722) rfl rfl ArealUCore.ArealUK.chunk_9360 s61
  have s59 : leavesOK ctxLitU 322825000000 2 ((leaves.drop 18718).take 82) 324875000000 2 = true :=
    take_step (n := 2) (t := 82) (b := 18720) rfl rfl ArealUCore.ArealUK.chunk_9359 s60
  have s58 : leavesOK ctxLitU 322775000000 2 ((leaves.drop 18716).take 84) 324875000000 2 = true :=
    take_step (n := 2) (t := 84) (b := 18718) rfl rfl ArealUCore.ArealUK.chunk_9358 s59
  have s57 : leavesOK ctxLitU 322725000000 2 ((leaves.drop 18714).take 86) 324875000000 2 = true :=
    take_step (n := 2) (t := 86) (b := 18716) rfl rfl ArealUCore.ArealUK.chunk_9357 s58
  have s56 : leavesOK ctxLitU 322675000000 2 ((leaves.drop 18712).take 88) 324875000000 2 = true :=
    take_step (n := 2) (t := 88) (b := 18714) rfl rfl ArealUCore.ArealUK.chunk_9356 s57
  have s55 : leavesOK ctxLitU 322625000000 2 ((leaves.drop 18710).take 90) 324875000000 2 = true :=
    take_step (n := 2) (t := 90) (b := 18712) rfl rfl ArealUCore.ArealUK.chunk_9355 s56
  have s54 : leavesOK ctxLitU 322575000000 2 ((leaves.drop 18708).take 92) 324875000000 2 = true :=
    take_step (n := 2) (t := 92) (b := 18710) rfl rfl ArealUCore.ArealUK.chunk_9354 s55
  have s53 : leavesOK ctxLitU 322525000000 2 ((leaves.drop 18706).take 94) 324875000000 2 = true :=
    take_step (n := 2) (t := 94) (b := 18708) rfl rfl ArealUCore.ArealUK.chunk_9353 s54
  have s52 : leavesOK ctxLitU 322475000000 2 ((leaves.drop 18704).take 96) 324875000000 2 = true :=
    take_step (n := 2) (t := 96) (b := 18706) rfl rfl ArealUCore.ArealUK.chunk_9352 s53
  have s51 : leavesOK ctxLitU 322425000000 2 ((leaves.drop 18702).take 98) 324875000000 2 = true :=
    take_step (n := 2) (t := 98) (b := 18704) rfl rfl ArealUCore.ArealUK.chunk_9351 s52
  have s50 : leavesOK ctxLitU 322375000000 2 ((leaves.drop 18700).take 100) 324875000000 2 = true :=
    take_step (n := 2) (t := 100) (b := 18702) rfl rfl ArealUCore.ArealUK.chunk_9350 s51
  have s49 : leavesOK ctxLitU 322325000000 2 ((leaves.drop 18698).take 102) 324875000000 2 = true :=
    take_step (n := 2) (t := 102) (b := 18700) rfl rfl ArealUCore.ArealUK.chunk_9349 s50
  have s48 : leavesOK ctxLitU 322275000000 2 ((leaves.drop 18696).take 104) 324875000000 2 = true :=
    take_step (n := 2) (t := 104) (b := 18698) rfl rfl ArealUCore.ArealUK.chunk_9348 s49
  have s47 : leavesOK ctxLitU 322225000000 2 ((leaves.drop 18694).take 106) 324875000000 2 = true :=
    take_step (n := 2) (t := 106) (b := 18696) rfl rfl ArealUCore.ArealUK.chunk_9347 s48
  have s46 : leavesOK ctxLitU 322175000000 2 ((leaves.drop 18692).take 108) 324875000000 2 = true :=
    take_step (n := 2) (t := 108) (b := 18694) rfl rfl ArealUCore.ArealUK.chunk_9346 s47
  have s45 : leavesOK ctxLitU 322125000000 2 ((leaves.drop 18690).take 110) 324875000000 2 = true :=
    take_step (n := 2) (t := 110) (b := 18692) rfl rfl ArealUCore.ArealUK.chunk_9345 s46
  have s44 : leavesOK ctxLitU 322075000000 2 ((leaves.drop 18688).take 112) 324875000000 2 = true :=
    take_step (n := 2) (t := 112) (b := 18690) rfl rfl ArealUCore.ArealUK.chunk_9344 s45
  have s43 : leavesOK ctxLitU 322025000000 2 ((leaves.drop 18686).take 114) 324875000000 2 = true :=
    take_step (n := 2) (t := 114) (b := 18688) rfl rfl ArealUCore.ArealUK.chunk_9343 s44
  have s42 : leavesOK ctxLitU 321975000000 2 ((leaves.drop 18684).take 116) 324875000000 2 = true :=
    take_step (n := 2) (t := 116) (b := 18686) rfl rfl ArealUCore.ArealUK.chunk_9342 s43
  have s41 : leavesOK ctxLitU 321925000000 2 ((leaves.drop 18682).take 118) 324875000000 2 = true :=
    take_step (n := 2) (t := 118) (b := 18684) rfl rfl ArealUCore.ArealUK.chunk_9341 s42
  have s40 : leavesOK ctxLitU 321875000000 2 ((leaves.drop 18680).take 120) 324875000000 2 = true :=
    take_step (n := 2) (t := 120) (b := 18682) rfl rfl ArealUCore.ArealUK.chunk_9340 s41
  have s39 : leavesOK ctxLitU 321825000000 2 ((leaves.drop 18678).take 122) 324875000000 2 = true :=
    take_step (n := 2) (t := 122) (b := 18680) rfl rfl ArealUCore.ArealUK.chunk_9339 s40
  have s38 : leavesOK ctxLitU 321775000000 2 ((leaves.drop 18676).take 124) 324875000000 2 = true :=
    take_step (n := 2) (t := 124) (b := 18678) rfl rfl ArealUCore.ArealUK.chunk_9338 s39
  have s37 : leavesOK ctxLitU 321725000000 2 ((leaves.drop 18674).take 126) 324875000000 2 = true :=
    take_step (n := 2) (t := 126) (b := 18676) rfl rfl ArealUCore.ArealUK.chunk_9337 s38
  have s36 : leavesOK ctxLitU 321675000000 2 ((leaves.drop 18672).take 128) 324875000000 2 = true :=
    take_step (n := 2) (t := 128) (b := 18674) rfl rfl ArealUCore.ArealUK.chunk_9336 s37
  have s35 : leavesOK ctxLitU 321625000000 2 ((leaves.drop 18670).take 130) 324875000000 2 = true :=
    take_step (n := 2) (t := 130) (b := 18672) rfl rfl ArealUCore.ArealUK.chunk_9335 s36
  have s34 : leavesOK ctxLitU 321575000000 2 ((leaves.drop 18668).take 132) 324875000000 2 = true :=
    take_step (n := 2) (t := 132) (b := 18670) rfl rfl ArealUCore.ArealUK.chunk_9334 s35
  have s33 : leavesOK ctxLitU 321525000000 2 ((leaves.drop 18666).take 134) 324875000000 2 = true :=
    take_step (n := 2) (t := 134) (b := 18668) rfl rfl ArealUCore.ArealUK.chunk_9333 s34
  have s32 : leavesOK ctxLitU 321475000000 2 ((leaves.drop 18664).take 136) 324875000000 2 = true :=
    take_step (n := 2) (t := 136) (b := 18666) rfl rfl ArealUCore.ArealUK.chunk_9332 s33
  have s31 : leavesOK ctxLitU 321425000000 2 ((leaves.drop 18662).take 138) 324875000000 2 = true :=
    take_step (n := 2) (t := 138) (b := 18664) rfl rfl ArealUCore.ArealUK.chunk_9331 s32
  have s30 : leavesOK ctxLitU 321375000000 2 ((leaves.drop 18660).take 140) 324875000000 2 = true :=
    take_step (n := 2) (t := 140) (b := 18662) rfl rfl ArealUCore.ArealUK.chunk_9330 s31
  have s29 : leavesOK ctxLitU 321325000000 2 ((leaves.drop 18658).take 142) 324875000000 2 = true :=
    take_step (n := 2) (t := 142) (b := 18660) rfl rfl ArealUCore.ArealUK.chunk_9329 s30
  have s28 : leavesOK ctxLitU 321275000000 2 ((leaves.drop 18656).take 144) 324875000000 2 = true :=
    take_step (n := 2) (t := 144) (b := 18658) rfl rfl ArealUCore.ArealUK.chunk_9328 s29
  have s27 : leavesOK ctxLitU 321225000000 2 ((leaves.drop 18654).take 146) 324875000000 2 = true :=
    take_step (n := 2) (t := 146) (b := 18656) rfl rfl ArealUCore.ArealUK.chunk_9327 s28
  have s26 : leavesOK ctxLitU 321175000000 2 ((leaves.drop 18652).take 148) 324875000000 2 = true :=
    take_step (n := 2) (t := 148) (b := 18654) rfl rfl ArealUCore.ArealUK.chunk_9326 s27
  have s25 : leavesOK ctxLitU 321125000000 2 ((leaves.drop 18650).take 150) 324875000000 2 = true :=
    take_step (n := 2) (t := 150) (b := 18652) rfl rfl ArealUCore.ArealUK.chunk_9325 s26
  have s24 : leavesOK ctxLitU 321075000000 2 ((leaves.drop 18648).take 152) 324875000000 2 = true :=
    take_step (n := 2) (t := 152) (b := 18650) rfl rfl ArealUCore.ArealUK.chunk_9324 s25
  have s23 : leavesOK ctxLitU 321025000000 2 ((leaves.drop 18646).take 154) 324875000000 2 = true :=
    take_step (n := 2) (t := 154) (b := 18648) rfl rfl ArealUCore.ArealUK.chunk_9323 s24
  have s22 : leavesOK ctxLitU 320975000000 2 ((leaves.drop 18644).take 156) 324875000000 2 = true :=
    take_step (n := 2) (t := 156) (b := 18646) rfl rfl ArealUCore.ArealUK.chunk_9322 s23
  have s21 : leavesOK ctxLitU 320925000000 2 ((leaves.drop 18642).take 158) 324875000000 2 = true :=
    take_step (n := 2) (t := 158) (b := 18644) rfl rfl ArealUCore.ArealUK.chunk_9321 s22
  have s20 : leavesOK ctxLitU 320875000000 2 ((leaves.drop 18640).take 160) 324875000000 2 = true :=
    take_step (n := 2) (t := 160) (b := 18642) rfl rfl ArealUCore.ArealUK.chunk_9320 s21
  have s19 : leavesOK ctxLitU 320825000000 2 ((leaves.drop 18638).take 162) 324875000000 2 = true :=
    take_step (n := 2) (t := 162) (b := 18640) rfl rfl ArealUCore.ArealUK.chunk_9319 s20
  have s18 : leavesOK ctxLitU 320775000000 2 ((leaves.drop 18636).take 164) 324875000000 2 = true :=
    take_step (n := 2) (t := 164) (b := 18638) rfl rfl ArealUCore.ArealUK.chunk_9318 s19
  have s17 : leavesOK ctxLitU 320725000000 2 ((leaves.drop 18634).take 166) 324875000000 2 = true :=
    take_step (n := 2) (t := 166) (b := 18636) rfl rfl ArealUCore.ArealUK.chunk_9317 s18
  have s16 : leavesOK ctxLitU 320675000000 2 ((leaves.drop 18632).take 168) 324875000000 2 = true :=
    take_step (n := 2) (t := 168) (b := 18634) rfl rfl ArealUCore.ArealUK.chunk_9316 s17
  have s15 : leavesOK ctxLitU 320625000000 2 ((leaves.drop 18630).take 170) 324875000000 2 = true :=
    take_step (n := 2) (t := 170) (b := 18632) rfl rfl ArealUCore.ArealUK.chunk_9315 s16
  have s14 : leavesOK ctxLitU 320575000000 2 ((leaves.drop 18628).take 172) 324875000000 2 = true :=
    take_step (n := 2) (t := 172) (b := 18630) rfl rfl ArealUCore.ArealUK.chunk_9314 s15
  have s13 : leavesOK ctxLitU 320525000000 2 ((leaves.drop 18626).take 174) 324875000000 2 = true :=
    take_step (n := 2) (t := 174) (b := 18628) rfl rfl ArealUCore.ArealUK.chunk_9313 s14
  have s12 : leavesOK ctxLitU 320475000000 2 ((leaves.drop 18624).take 176) 324875000000 2 = true :=
    take_step (n := 2) (t := 176) (b := 18626) rfl rfl ArealUCore.ArealUK.chunk_9312 s13
  have s11 : leavesOK ctxLitU 320425000000 2 ((leaves.drop 18622).take 178) 324875000000 2 = true :=
    take_step (n := 2) (t := 178) (b := 18624) rfl rfl ArealUCore.ArealUK.chunk_9311 s12
  have s10 : leavesOK ctxLitU 320375000000 2 ((leaves.drop 18620).take 180) 324875000000 2 = true :=
    take_step (n := 2) (t := 180) (b := 18622) rfl rfl ArealUCore.ArealUK.chunk_9310 s11
  have s9 : leavesOK ctxLitU 320325000000 2 ((leaves.drop 18618).take 182) 324875000000 2 = true :=
    take_step (n := 2) (t := 182) (b := 18620) rfl rfl ArealUCore.ArealUK.chunk_9309 s10
  have s8 : leavesOK ctxLitU 320275000000 2 ((leaves.drop 18616).take 184) 324875000000 2 = true :=
    take_step (n := 2) (t := 184) (b := 18618) rfl rfl ArealUCore.ArealUK.chunk_9308 s9
  have s7 : leavesOK ctxLitU 320225000000 2 ((leaves.drop 18614).take 186) 324875000000 2 = true :=
    take_step (n := 2) (t := 186) (b := 18616) rfl rfl ArealUCore.ArealUK.chunk_9307 s8
  have s6 : leavesOK ctxLitU 320175000000 2 ((leaves.drop 18612).take 188) 324875000000 2 = true :=
    take_step (n := 2) (t := 188) (b := 18614) rfl rfl ArealUCore.ArealUK.chunk_9306 s7
  have s5 : leavesOK ctxLitU 320125000000 2 ((leaves.drop 18610).take 190) 324875000000 2 = true :=
    take_step (n := 2) (t := 190) (b := 18612) rfl rfl ArealUCore.ArealUK.chunk_9305 s6
  have s4 : leavesOK ctxLitU 320075000000 2 ((leaves.drop 18608).take 192) 324875000000 2 = true :=
    take_step (n := 2) (t := 192) (b := 18610) rfl rfl ArealUCore.ArealUK.chunk_9304 s5
  have s3 : leavesOK ctxLitU 320025000000 2 ((leaves.drop 18606).take 194) 324875000000 2 = true :=
    take_step (n := 2) (t := 194) (b := 18608) rfl rfl ArealUCore.ArealUK.chunk_9303 s4
  have s2 : leavesOK ctxLitU 319975000000 2 ((leaves.drop 18604).take 196) 324875000000 2 = true :=
    take_step (n := 2) (t := 196) (b := 18606) rfl rfl ArealUCore.ArealUK.chunk_9302 s3
  have s1 : leavesOK ctxLitU 319925000000 2 ((leaves.drop 18602).take 198) 324875000000 2 = true :=
    take_step (n := 2) (t := 198) (b := 18604) rfl rfl ArealUCore.ArealUK.chunk_9301 s2
  have s0 : leavesOK ctxLitU 319875000000 2 ((leaves.drop 18600).take 200) 324875000000 2 = true :=
    take_step (n := 2) (t := 200) (b := 18602) rfl rfl ArealUCore.ArealUK.chunk_9300 s1
  exact s0

end Areal.UCert

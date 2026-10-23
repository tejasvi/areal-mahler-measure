import ArealUK.Chunk6300
import ArealUK.Chunk6301
import ArealUK.Chunk6302
import ArealUK.Chunk6303
import ArealUK.Chunk6304
import ArealUK.Chunk6305
import ArealUK.Chunk6306
import ArealUK.Chunk6307
import ArealUK.Chunk6308
import ArealUK.Chunk6309
import ArealUK.Chunk6310
import ArealUK.Chunk6311
import ArealUK.Chunk6312
import ArealUK.Chunk6313
import ArealUK.Chunk6314
import ArealUK.Chunk6315
import ArealUK.Chunk6316
import ArealUK.Chunk6317
import ArealUK.Chunk6318
import ArealUK.Chunk6319
import ArealUK.Chunk6320
import ArealUK.Chunk6321
import ArealUK.Chunk6322
import ArealUK.Chunk6323
import ArealUK.Chunk6324
import ArealUK.Chunk6325
import ArealUK.Chunk6326
import ArealUK.Chunk6327
import ArealUK.Chunk6328
import ArealUK.Chunk6329
import ArealUK.Chunk6330
import ArealUK.Chunk6331
import ArealUK.Chunk6332
import ArealUK.Chunk6333
import ArealUK.Chunk6334
import ArealUK.Chunk6335
import ArealUK.Chunk6336
import ArealUK.Chunk6337
import ArealUK.Chunk6338
import ArealUK.Chunk6339
import ArealUK.Chunk6340
import ArealUK.Chunk6341
import ArealUK.Chunk6342
import ArealUK.Chunk6343
import ArealUK.Chunk6344
import ArealUK.Chunk6345
import ArealUK.Chunk6346
import ArealUK.Chunk6347
import ArealUK.Chunk6348
import ArealUK.Chunk6349
import ArealUK.Chunk6350
import ArealUK.Chunk6351
import ArealUK.Chunk6352
import ArealUK.Chunk6353
import ArealUK.Chunk6354
import ArealUK.Chunk6355
import ArealUK.Chunk6356
import ArealUK.Chunk6357
import ArealUK.Chunk6358
import ArealUK.Chunk6359
import ArealUK.Chunk6360
import ArealUK.Chunk6361
import ArealUK.Chunk6362
import ArealUK.Chunk6363
import ArealUK.Chunk6364
import ArealUK.Chunk6365
import ArealUK.Chunk6366
import ArealUK.Chunk6367
import ArealUK.Chunk6368
import ArealUK.Chunk6369
import ArealUK.Chunk6370
import ArealUK.Chunk6371
import ArealUK.Chunk6372
import ArealUK.Chunk6373
import ArealUK.Chunk6374
import ArealUK.Chunk6375
import ArealUK.Chunk6376
import ArealUK.Chunk6377
import ArealUK.Chunk6378
import ArealUK.Chunk6379
import ArealUK.Chunk6380
import ArealUK.Chunk6381
import ArealUK.Chunk6382
import ArealUK.Chunk6383
import ArealUK.Chunk6384
import ArealUK.Chunk6385
import ArealUK.Chunk6386
import ArealUK.Chunk6387
import ArealUK.Chunk6388
import ArealUK.Chunk6389
import ArealUK.Chunk6390
import ArealUK.Chunk6391
import ArealUK.Chunk6392
import ArealUK.Chunk6393
import ArealUK.Chunk6394
import ArealUK.Chunk6395
import ArealUK.Chunk6396
import ArealUK.Chunk6397
import ArealUK.Chunk6398
import ArealUK.Chunk6399
import Areal.UCert.LeavesKGen

/-! Group 63 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_63 : leavesOK ctxLitU 329525000000 3 ((leaves.drop 12600).take 200) 334525000000 3 = true := by
  have s99 := ArealUCore.ArealUK.chunk_6399
  have s98 : leavesOK ctxLitU 334425000000 3 ((leaves.drop 12796).take 4) 334525000000 3 = true :=
    take_step (n := 2) (t := 4) (b := 12798) rfl rfl ArealUCore.ArealUK.chunk_6398 s99
  have s97 : leavesOK ctxLitU 334375000000 3 ((leaves.drop 12794).take 6) 334525000000 3 = true :=
    take_step (n := 2) (t := 6) (b := 12796) rfl rfl ArealUCore.ArealUK.chunk_6397 s98
  have s96 : leavesOK ctxLitU 334325000000 3 ((leaves.drop 12792).take 8) 334525000000 3 = true :=
    take_step (n := 2) (t := 8) (b := 12794) rfl rfl ArealUCore.ArealUK.chunk_6396 s97
  have s95 : leavesOK ctxLitU 334275000000 3 ((leaves.drop 12790).take 10) 334525000000 3 = true :=
    take_step (n := 2) (t := 10) (b := 12792) rfl rfl ArealUCore.ArealUK.chunk_6395 s96
  have s94 : leavesOK ctxLitU 334225000000 3 ((leaves.drop 12788).take 12) 334525000000 3 = true :=
    take_step (n := 2) (t := 12) (b := 12790) rfl rfl ArealUCore.ArealUK.chunk_6394 s95
  have s93 : leavesOK ctxLitU 334175000000 3 ((leaves.drop 12786).take 14) 334525000000 3 = true :=
    take_step (n := 2) (t := 14) (b := 12788) rfl rfl ArealUCore.ArealUK.chunk_6393 s94
  have s92 : leavesOK ctxLitU 334125000000 3 ((leaves.drop 12784).take 16) 334525000000 3 = true :=
    take_step (n := 2) (t := 16) (b := 12786) rfl rfl ArealUCore.ArealUK.chunk_6392 s93
  have s91 : leavesOK ctxLitU 334075000000 3 ((leaves.drop 12782).take 18) 334525000000 3 = true :=
    take_step (n := 2) (t := 18) (b := 12784) rfl rfl ArealUCore.ArealUK.chunk_6391 s92
  have s90 : leavesOK ctxLitU 334025000000 3 ((leaves.drop 12780).take 20) 334525000000 3 = true :=
    take_step (n := 2) (t := 20) (b := 12782) rfl rfl ArealUCore.ArealUK.chunk_6390 s91
  have s89 : leavesOK ctxLitU 333975000000 3 ((leaves.drop 12778).take 22) 334525000000 3 = true :=
    take_step (n := 2) (t := 22) (b := 12780) rfl rfl ArealUCore.ArealUK.chunk_6389 s90
  have s88 : leavesOK ctxLitU 333925000000 3 ((leaves.drop 12776).take 24) 334525000000 3 = true :=
    take_step (n := 2) (t := 24) (b := 12778) rfl rfl ArealUCore.ArealUK.chunk_6388 s89
  have s87 : leavesOK ctxLitU 333875000000 3 ((leaves.drop 12774).take 26) 334525000000 3 = true :=
    take_step (n := 2) (t := 26) (b := 12776) rfl rfl ArealUCore.ArealUK.chunk_6387 s88
  have s86 : leavesOK ctxLitU 333825000000 3 ((leaves.drop 12772).take 28) 334525000000 3 = true :=
    take_step (n := 2) (t := 28) (b := 12774) rfl rfl ArealUCore.ArealUK.chunk_6386 s87
  have s85 : leavesOK ctxLitU 333775000000 3 ((leaves.drop 12770).take 30) 334525000000 3 = true :=
    take_step (n := 2) (t := 30) (b := 12772) rfl rfl ArealUCore.ArealUK.chunk_6385 s86
  have s84 : leavesOK ctxLitU 333725000000 3 ((leaves.drop 12768).take 32) 334525000000 3 = true :=
    take_step (n := 2) (t := 32) (b := 12770) rfl rfl ArealUCore.ArealUK.chunk_6384 s85
  have s83 : leavesOK ctxLitU 333675000000 3 ((leaves.drop 12766).take 34) 334525000000 3 = true :=
    take_step (n := 2) (t := 34) (b := 12768) rfl rfl ArealUCore.ArealUK.chunk_6383 s84
  have s82 : leavesOK ctxLitU 333625000000 3 ((leaves.drop 12764).take 36) 334525000000 3 = true :=
    take_step (n := 2) (t := 36) (b := 12766) rfl rfl ArealUCore.ArealUK.chunk_6382 s83
  have s81 : leavesOK ctxLitU 333575000000 3 ((leaves.drop 12762).take 38) 334525000000 3 = true :=
    take_step (n := 2) (t := 38) (b := 12764) rfl rfl ArealUCore.ArealUK.chunk_6381 s82
  have s80 : leavesOK ctxLitU 333525000000 3 ((leaves.drop 12760).take 40) 334525000000 3 = true :=
    take_step (n := 2) (t := 40) (b := 12762) rfl rfl ArealUCore.ArealUK.chunk_6380 s81
  have s79 : leavesOK ctxLitU 333475000000 3 ((leaves.drop 12758).take 42) 334525000000 3 = true :=
    take_step (n := 2) (t := 42) (b := 12760) rfl rfl ArealUCore.ArealUK.chunk_6379 s80
  have s78 : leavesOK ctxLitU 333425000000 3 ((leaves.drop 12756).take 44) 334525000000 3 = true :=
    take_step (n := 2) (t := 44) (b := 12758) rfl rfl ArealUCore.ArealUK.chunk_6378 s79
  have s77 : leavesOK ctxLitU 333375000000 3 ((leaves.drop 12754).take 46) 334525000000 3 = true :=
    take_step (n := 2) (t := 46) (b := 12756) rfl rfl ArealUCore.ArealUK.chunk_6377 s78
  have s76 : leavesOK ctxLitU 333325000000 3 ((leaves.drop 12752).take 48) 334525000000 3 = true :=
    take_step (n := 2) (t := 48) (b := 12754) rfl rfl ArealUCore.ArealUK.chunk_6376 s77
  have s75 : leavesOK ctxLitU 333275000000 3 ((leaves.drop 12750).take 50) 334525000000 3 = true :=
    take_step (n := 2) (t := 50) (b := 12752) rfl rfl ArealUCore.ArealUK.chunk_6375 s76
  have s74 : leavesOK ctxLitU 333225000000 3 ((leaves.drop 12748).take 52) 334525000000 3 = true :=
    take_step (n := 2) (t := 52) (b := 12750) rfl rfl ArealUCore.ArealUK.chunk_6374 s75
  have s73 : leavesOK ctxLitU 333175000000 3 ((leaves.drop 12746).take 54) 334525000000 3 = true :=
    take_step (n := 2) (t := 54) (b := 12748) rfl rfl ArealUCore.ArealUK.chunk_6373 s74
  have s72 : leavesOK ctxLitU 333125000000 3 ((leaves.drop 12744).take 56) 334525000000 3 = true :=
    take_step (n := 2) (t := 56) (b := 12746) rfl rfl ArealUCore.ArealUK.chunk_6372 s73
  have s71 : leavesOK ctxLitU 333075000000 3 ((leaves.drop 12742).take 58) 334525000000 3 = true :=
    take_step (n := 2) (t := 58) (b := 12744) rfl rfl ArealUCore.ArealUK.chunk_6371 s72
  have s70 : leavesOK ctxLitU 333025000000 3 ((leaves.drop 12740).take 60) 334525000000 3 = true :=
    take_step (n := 2) (t := 60) (b := 12742) rfl rfl ArealUCore.ArealUK.chunk_6370 s71
  have s69 : leavesOK ctxLitU 332975000000 3 ((leaves.drop 12738).take 62) 334525000000 3 = true :=
    take_step (n := 2) (t := 62) (b := 12740) rfl rfl ArealUCore.ArealUK.chunk_6369 s70
  have s68 : leavesOK ctxLitU 332925000000 3 ((leaves.drop 12736).take 64) 334525000000 3 = true :=
    take_step (n := 2) (t := 64) (b := 12738) rfl rfl ArealUCore.ArealUK.chunk_6368 s69
  have s67 : leavesOK ctxLitU 332875000000 3 ((leaves.drop 12734).take 66) 334525000000 3 = true :=
    take_step (n := 2) (t := 66) (b := 12736) rfl rfl ArealUCore.ArealUK.chunk_6367 s68
  have s66 : leavesOK ctxLitU 332825000000 3 ((leaves.drop 12732).take 68) 334525000000 3 = true :=
    take_step (n := 2) (t := 68) (b := 12734) rfl rfl ArealUCore.ArealUK.chunk_6366 s67
  have s65 : leavesOK ctxLitU 332775000000 3 ((leaves.drop 12730).take 70) 334525000000 3 = true :=
    take_step (n := 2) (t := 70) (b := 12732) rfl rfl ArealUCore.ArealUK.chunk_6365 s66
  have s64 : leavesOK ctxLitU 332725000000 3 ((leaves.drop 12728).take 72) 334525000000 3 = true :=
    take_step (n := 2) (t := 72) (b := 12730) rfl rfl ArealUCore.ArealUK.chunk_6364 s65
  have s63 : leavesOK ctxLitU 332675000000 3 ((leaves.drop 12726).take 74) 334525000000 3 = true :=
    take_step (n := 2) (t := 74) (b := 12728) rfl rfl ArealUCore.ArealUK.chunk_6363 s64
  have s62 : leavesOK ctxLitU 332625000000 3 ((leaves.drop 12724).take 76) 334525000000 3 = true :=
    take_step (n := 2) (t := 76) (b := 12726) rfl rfl ArealUCore.ArealUK.chunk_6362 s63
  have s61 : leavesOK ctxLitU 332575000000 3 ((leaves.drop 12722).take 78) 334525000000 3 = true :=
    take_step (n := 2) (t := 78) (b := 12724) rfl rfl ArealUCore.ArealUK.chunk_6361 s62
  have s60 : leavesOK ctxLitU 332525000000 3 ((leaves.drop 12720).take 80) 334525000000 3 = true :=
    take_step (n := 2) (t := 80) (b := 12722) rfl rfl ArealUCore.ArealUK.chunk_6360 s61
  have s59 : leavesOK ctxLitU 332475000000 3 ((leaves.drop 12718).take 82) 334525000000 3 = true :=
    take_step (n := 2) (t := 82) (b := 12720) rfl rfl ArealUCore.ArealUK.chunk_6359 s60
  have s58 : leavesOK ctxLitU 332425000000 3 ((leaves.drop 12716).take 84) 334525000000 3 = true :=
    take_step (n := 2) (t := 84) (b := 12718) rfl rfl ArealUCore.ArealUK.chunk_6358 s59
  have s57 : leavesOK ctxLitU 332375000000 3 ((leaves.drop 12714).take 86) 334525000000 3 = true :=
    take_step (n := 2) (t := 86) (b := 12716) rfl rfl ArealUCore.ArealUK.chunk_6357 s58
  have s56 : leavesOK ctxLitU 332325000000 3 ((leaves.drop 12712).take 88) 334525000000 3 = true :=
    take_step (n := 2) (t := 88) (b := 12714) rfl rfl ArealUCore.ArealUK.chunk_6356 s57
  have s55 : leavesOK ctxLitU 332275000000 3 ((leaves.drop 12710).take 90) 334525000000 3 = true :=
    take_step (n := 2) (t := 90) (b := 12712) rfl rfl ArealUCore.ArealUK.chunk_6355 s56
  have s54 : leavesOK ctxLitU 332225000000 3 ((leaves.drop 12708).take 92) 334525000000 3 = true :=
    take_step (n := 2) (t := 92) (b := 12710) rfl rfl ArealUCore.ArealUK.chunk_6354 s55
  have s53 : leavesOK ctxLitU 332175000000 3 ((leaves.drop 12706).take 94) 334525000000 3 = true :=
    take_step (n := 2) (t := 94) (b := 12708) rfl rfl ArealUCore.ArealUK.chunk_6353 s54
  have s52 : leavesOK ctxLitU 332125000000 3 ((leaves.drop 12704).take 96) 334525000000 3 = true :=
    take_step (n := 2) (t := 96) (b := 12706) rfl rfl ArealUCore.ArealUK.chunk_6352 s53
  have s51 : leavesOK ctxLitU 332075000000 3 ((leaves.drop 12702).take 98) 334525000000 3 = true :=
    take_step (n := 2) (t := 98) (b := 12704) rfl rfl ArealUCore.ArealUK.chunk_6351 s52
  have s50 : leavesOK ctxLitU 332025000000 3 ((leaves.drop 12700).take 100) 334525000000 3 = true :=
    take_step (n := 2) (t := 100) (b := 12702) rfl rfl ArealUCore.ArealUK.chunk_6350 s51
  have s49 : leavesOK ctxLitU 331975000000 3 ((leaves.drop 12698).take 102) 334525000000 3 = true :=
    take_step (n := 2) (t := 102) (b := 12700) rfl rfl ArealUCore.ArealUK.chunk_6349 s50
  have s48 : leavesOK ctxLitU 331925000000 3 ((leaves.drop 12696).take 104) 334525000000 3 = true :=
    take_step (n := 2) (t := 104) (b := 12698) rfl rfl ArealUCore.ArealUK.chunk_6348 s49
  have s47 : leavesOK ctxLitU 331875000000 3 ((leaves.drop 12694).take 106) 334525000000 3 = true :=
    take_step (n := 2) (t := 106) (b := 12696) rfl rfl ArealUCore.ArealUK.chunk_6347 s48
  have s46 : leavesOK ctxLitU 331825000000 3 ((leaves.drop 12692).take 108) 334525000000 3 = true :=
    take_step (n := 2) (t := 108) (b := 12694) rfl rfl ArealUCore.ArealUK.chunk_6346 s47
  have s45 : leavesOK ctxLitU 331775000000 3 ((leaves.drop 12690).take 110) 334525000000 3 = true :=
    take_step (n := 2) (t := 110) (b := 12692) rfl rfl ArealUCore.ArealUK.chunk_6345 s46
  have s44 : leavesOK ctxLitU 331725000000 3 ((leaves.drop 12688).take 112) 334525000000 3 = true :=
    take_step (n := 2) (t := 112) (b := 12690) rfl rfl ArealUCore.ArealUK.chunk_6344 s45
  have s43 : leavesOK ctxLitU 331675000000 3 ((leaves.drop 12686).take 114) 334525000000 3 = true :=
    take_step (n := 2) (t := 114) (b := 12688) rfl rfl ArealUCore.ArealUK.chunk_6343 s44
  have s42 : leavesOK ctxLitU 331625000000 3 ((leaves.drop 12684).take 116) 334525000000 3 = true :=
    take_step (n := 2) (t := 116) (b := 12686) rfl rfl ArealUCore.ArealUK.chunk_6342 s43
  have s41 : leavesOK ctxLitU 331575000000 3 ((leaves.drop 12682).take 118) 334525000000 3 = true :=
    take_step (n := 2) (t := 118) (b := 12684) rfl rfl ArealUCore.ArealUK.chunk_6341 s42
  have s40 : leavesOK ctxLitU 331525000000 3 ((leaves.drop 12680).take 120) 334525000000 3 = true :=
    take_step (n := 2) (t := 120) (b := 12682) rfl rfl ArealUCore.ArealUK.chunk_6340 s41
  have s39 : leavesOK ctxLitU 331475000000 3 ((leaves.drop 12678).take 122) 334525000000 3 = true :=
    take_step (n := 2) (t := 122) (b := 12680) rfl rfl ArealUCore.ArealUK.chunk_6339 s40
  have s38 : leavesOK ctxLitU 331425000000 3 ((leaves.drop 12676).take 124) 334525000000 3 = true :=
    take_step (n := 2) (t := 124) (b := 12678) rfl rfl ArealUCore.ArealUK.chunk_6338 s39
  have s37 : leavesOK ctxLitU 331375000000 3 ((leaves.drop 12674).take 126) 334525000000 3 = true :=
    take_step (n := 2) (t := 126) (b := 12676) rfl rfl ArealUCore.ArealUK.chunk_6337 s38
  have s36 : leavesOK ctxLitU 331325000000 3 ((leaves.drop 12672).take 128) 334525000000 3 = true :=
    take_step (n := 2) (t := 128) (b := 12674) rfl rfl ArealUCore.ArealUK.chunk_6336 s37
  have s35 : leavesOK ctxLitU 331275000000 3 ((leaves.drop 12670).take 130) 334525000000 3 = true :=
    take_step (n := 2) (t := 130) (b := 12672) rfl rfl ArealUCore.ArealUK.chunk_6335 s36
  have s34 : leavesOK ctxLitU 331225000000 3 ((leaves.drop 12668).take 132) 334525000000 3 = true :=
    take_step (n := 2) (t := 132) (b := 12670) rfl rfl ArealUCore.ArealUK.chunk_6334 s35
  have s33 : leavesOK ctxLitU 331175000000 3 ((leaves.drop 12666).take 134) 334525000000 3 = true :=
    take_step (n := 2) (t := 134) (b := 12668) rfl rfl ArealUCore.ArealUK.chunk_6333 s34
  have s32 : leavesOK ctxLitU 331125000000 3 ((leaves.drop 12664).take 136) 334525000000 3 = true :=
    take_step (n := 2) (t := 136) (b := 12666) rfl rfl ArealUCore.ArealUK.chunk_6332 s33
  have s31 : leavesOK ctxLitU 331075000000 3 ((leaves.drop 12662).take 138) 334525000000 3 = true :=
    take_step (n := 2) (t := 138) (b := 12664) rfl rfl ArealUCore.ArealUK.chunk_6331 s32
  have s30 : leavesOK ctxLitU 331025000000 3 ((leaves.drop 12660).take 140) 334525000000 3 = true :=
    take_step (n := 2) (t := 140) (b := 12662) rfl rfl ArealUCore.ArealUK.chunk_6330 s31
  have s29 : leavesOK ctxLitU 330975000000 3 ((leaves.drop 12658).take 142) 334525000000 3 = true :=
    take_step (n := 2) (t := 142) (b := 12660) rfl rfl ArealUCore.ArealUK.chunk_6329 s30
  have s28 : leavesOK ctxLitU 330925000000 3 ((leaves.drop 12656).take 144) 334525000000 3 = true :=
    take_step (n := 2) (t := 144) (b := 12658) rfl rfl ArealUCore.ArealUK.chunk_6328 s29
  have s27 : leavesOK ctxLitU 330875000000 3 ((leaves.drop 12654).take 146) 334525000000 3 = true :=
    take_step (n := 2) (t := 146) (b := 12656) rfl rfl ArealUCore.ArealUK.chunk_6327 s28
  have s26 : leavesOK ctxLitU 330825000000 3 ((leaves.drop 12652).take 148) 334525000000 3 = true :=
    take_step (n := 2) (t := 148) (b := 12654) rfl rfl ArealUCore.ArealUK.chunk_6326 s27
  have s25 : leavesOK ctxLitU 330775000000 3 ((leaves.drop 12650).take 150) 334525000000 3 = true :=
    take_step (n := 2) (t := 150) (b := 12652) rfl rfl ArealUCore.ArealUK.chunk_6325 s26
  have s24 : leavesOK ctxLitU 330725000000 3 ((leaves.drop 12648).take 152) 334525000000 3 = true :=
    take_step (n := 2) (t := 152) (b := 12650) rfl rfl ArealUCore.ArealUK.chunk_6324 s25
  have s23 : leavesOK ctxLitU 330675000000 3 ((leaves.drop 12646).take 154) 334525000000 3 = true :=
    take_step (n := 2) (t := 154) (b := 12648) rfl rfl ArealUCore.ArealUK.chunk_6323 s24
  have s22 : leavesOK ctxLitU 330625000000 3 ((leaves.drop 12644).take 156) 334525000000 3 = true :=
    take_step (n := 2) (t := 156) (b := 12646) rfl rfl ArealUCore.ArealUK.chunk_6322 s23
  have s21 : leavesOK ctxLitU 330575000000 3 ((leaves.drop 12642).take 158) 334525000000 3 = true :=
    take_step (n := 2) (t := 158) (b := 12644) rfl rfl ArealUCore.ArealUK.chunk_6321 s22
  have s20 : leavesOK ctxLitU 330525000000 3 ((leaves.drop 12640).take 160) 334525000000 3 = true :=
    take_step (n := 2) (t := 160) (b := 12642) rfl rfl ArealUCore.ArealUK.chunk_6320 s21
  have s19 : leavesOK ctxLitU 330475000000 3 ((leaves.drop 12638).take 162) 334525000000 3 = true :=
    take_step (n := 2) (t := 162) (b := 12640) rfl rfl ArealUCore.ArealUK.chunk_6319 s20
  have s18 : leavesOK ctxLitU 330425000000 3 ((leaves.drop 12636).take 164) 334525000000 3 = true :=
    take_step (n := 2) (t := 164) (b := 12638) rfl rfl ArealUCore.ArealUK.chunk_6318 s19
  have s17 : leavesOK ctxLitU 330375000000 3 ((leaves.drop 12634).take 166) 334525000000 3 = true :=
    take_step (n := 2) (t := 166) (b := 12636) rfl rfl ArealUCore.ArealUK.chunk_6317 s18
  have s16 : leavesOK ctxLitU 330325000000 3 ((leaves.drop 12632).take 168) 334525000000 3 = true :=
    take_step (n := 2) (t := 168) (b := 12634) rfl rfl ArealUCore.ArealUK.chunk_6316 s17
  have s15 : leavesOK ctxLitU 330275000000 3 ((leaves.drop 12630).take 170) 334525000000 3 = true :=
    take_step (n := 2) (t := 170) (b := 12632) rfl rfl ArealUCore.ArealUK.chunk_6315 s16
  have s14 : leavesOK ctxLitU 330225000000 3 ((leaves.drop 12628).take 172) 334525000000 3 = true :=
    take_step (n := 2) (t := 172) (b := 12630) rfl rfl ArealUCore.ArealUK.chunk_6314 s15
  have s13 : leavesOK ctxLitU 330175000000 3 ((leaves.drop 12626).take 174) 334525000000 3 = true :=
    take_step (n := 2) (t := 174) (b := 12628) rfl rfl ArealUCore.ArealUK.chunk_6313 s14
  have s12 : leavesOK ctxLitU 330125000000 3 ((leaves.drop 12624).take 176) 334525000000 3 = true :=
    take_step (n := 2) (t := 176) (b := 12626) rfl rfl ArealUCore.ArealUK.chunk_6312 s13
  have s11 : leavesOK ctxLitU 330075000000 3 ((leaves.drop 12622).take 178) 334525000000 3 = true :=
    take_step (n := 2) (t := 178) (b := 12624) rfl rfl ArealUCore.ArealUK.chunk_6311 s12
  have s10 : leavesOK ctxLitU 330025000000 3 ((leaves.drop 12620).take 180) 334525000000 3 = true :=
    take_step (n := 2) (t := 180) (b := 12622) rfl rfl ArealUCore.ArealUK.chunk_6310 s11
  have s9 : leavesOK ctxLitU 329975000000 3 ((leaves.drop 12618).take 182) 334525000000 3 = true :=
    take_step (n := 2) (t := 182) (b := 12620) rfl rfl ArealUCore.ArealUK.chunk_6309 s10
  have s8 : leavesOK ctxLitU 329925000000 3 ((leaves.drop 12616).take 184) 334525000000 3 = true :=
    take_step (n := 2) (t := 184) (b := 12618) rfl rfl ArealUCore.ArealUK.chunk_6308 s9
  have s7 : leavesOK ctxLitU 329875000000 3 ((leaves.drop 12614).take 186) 334525000000 3 = true :=
    take_step (n := 2) (t := 186) (b := 12616) rfl rfl ArealUCore.ArealUK.chunk_6307 s8
  have s6 : leavesOK ctxLitU 329825000000 3 ((leaves.drop 12612).take 188) 334525000000 3 = true :=
    take_step (n := 2) (t := 188) (b := 12614) rfl rfl ArealUCore.ArealUK.chunk_6306 s7
  have s5 : leavesOK ctxLitU 329775000000 3 ((leaves.drop 12610).take 190) 334525000000 3 = true :=
    take_step (n := 2) (t := 190) (b := 12612) rfl rfl ArealUCore.ArealUK.chunk_6305 s6
  have s4 : leavesOK ctxLitU 329725000000 3 ((leaves.drop 12608).take 192) 334525000000 3 = true :=
    take_step (n := 2) (t := 192) (b := 12610) rfl rfl ArealUCore.ArealUK.chunk_6304 s5
  have s3 : leavesOK ctxLitU 329675000000 3 ((leaves.drop 12606).take 194) 334525000000 3 = true :=
    take_step (n := 2) (t := 194) (b := 12608) rfl rfl ArealUCore.ArealUK.chunk_6303 s4
  have s2 : leavesOK ctxLitU 329625000000 3 ((leaves.drop 12604).take 196) 334525000000 3 = true :=
    take_step (n := 2) (t := 196) (b := 12606) rfl rfl ArealUCore.ArealUK.chunk_6302 s3
  have s1 : leavesOK ctxLitU 329575000000 3 ((leaves.drop 12602).take 198) 334525000000 3 = true :=
    take_step (n := 2) (t := 198) (b := 12604) rfl rfl ArealUCore.ArealUK.chunk_6301 s2
  have s0 : leavesOK ctxLitU 329525000000 3 ((leaves.drop 12600).take 200) 334525000000 3 = true :=
    take_step (n := 2) (t := 200) (b := 12602) rfl rfl ArealUCore.ArealUK.chunk_6300 s1
  exact s0

end Areal.UCert

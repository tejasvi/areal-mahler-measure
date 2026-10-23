import ArealUK.Chunk16300
import ArealUK.Chunk16301
import ArealUK.Chunk16302
import ArealUK.Chunk16303
import ArealUK.Chunk16304
import ArealUK.Chunk16305
import ArealUK.Chunk16306
import ArealUK.Chunk16307
import ArealUK.Chunk16308
import ArealUK.Chunk16309
import ArealUK.Chunk16310
import ArealUK.Chunk16311
import ArealUK.Chunk16312
import ArealUK.Chunk16313
import ArealUK.Chunk16314
import ArealUK.Chunk16315
import ArealUK.Chunk16316
import ArealUK.Chunk16317
import ArealUK.Chunk16318
import ArealUK.Chunk16319
import ArealUK.Chunk16320
import ArealUK.Chunk16321
import ArealUK.Chunk16322
import ArealUK.Chunk16323
import ArealUK.Chunk16324
import ArealUK.Chunk16325
import ArealUK.Chunk16326
import ArealUK.Chunk16327
import ArealUK.Chunk16328
import ArealUK.Chunk16329
import ArealUK.Chunk16330
import ArealUK.Chunk16331
import ArealUK.Chunk16332
import ArealUK.Chunk16333
import ArealUK.Chunk16334
import ArealUK.Chunk16335
import ArealUK.Chunk16336
import ArealUK.Chunk16337
import ArealUK.Chunk16338
import ArealUK.Chunk16339
import ArealUK.Chunk16340
import ArealUK.Chunk16341
import ArealUK.Chunk16342
import ArealUK.Chunk16343
import ArealUK.Chunk16344
import ArealUK.Chunk16345
import ArealUK.Chunk16346
import ArealUK.Chunk16347
import ArealUK.Chunk16348
import ArealUK.Chunk16349
import ArealUK.Chunk16350
import ArealUK.Chunk16351
import ArealUK.Chunk16352
import ArealUK.Chunk16353
import ArealUK.Chunk16354
import ArealUK.Chunk16355
import ArealUK.Chunk16356
import ArealUK.Chunk16357
import ArealUK.Chunk16358
import ArealUK.Chunk16359
import ArealUK.Chunk16360
import ArealUK.Chunk16361
import ArealUK.Chunk16362
import ArealUK.Chunk16363
import ArealUK.Chunk16364
import ArealUK.Chunk16365
import ArealUK.Chunk16366
import ArealUK.Chunk16367
import ArealUK.Chunk16368
import ArealUK.Chunk16369
import ArealUK.Chunk16370
import ArealUK.Chunk16371
import ArealUK.Chunk16372
import ArealUK.Chunk16373
import ArealUK.Chunk16374
import ArealUK.Chunk16375
import ArealUK.Chunk16376
import ArealUK.Chunk16377
import ArealUK.Chunk16378
import ArealUK.Chunk16379
import ArealUK.Chunk16380
import ArealUK.Chunk16381
import ArealUK.Chunk16382
import ArealUK.Chunk16383
import ArealUK.Chunk16384
import ArealUK.Chunk16385
import ArealUK.Chunk16386
import ArealUK.Chunk16387
import ArealUK.Chunk16388
import ArealUK.Chunk16389
import ArealUK.Chunk16390
import ArealUK.Chunk16391
import ArealUK.Chunk16392
import ArealUK.Chunk16393
import ArealUK.Chunk16394
import ArealUK.Chunk16395
import ArealUK.Chunk16396
import ArealUK.Chunk16397
import ArealUK.Chunk16398
import ArealUK.Chunk16399
import Areal.UCert.LeavesKGen

/-! Group 163 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_163 : leavesOK ctxLitU 178300000000 0 ((leaves.drop 32600).take 200) 183300000000 0 = true := by
  have s99 := ArealUCore.ArealUK.chunk_16399
  have s98 : leavesOK ctxLitU 183200000000 0 ((leaves.drop 32796).take 4) 183300000000 0 = true :=
    take_step (n := 2) (t := 4) (b := 32798) rfl rfl ArealUCore.ArealUK.chunk_16398 s99
  have s97 : leavesOK ctxLitU 183150000000 0 ((leaves.drop 32794).take 6) 183300000000 0 = true :=
    take_step (n := 2) (t := 6) (b := 32796) rfl rfl ArealUCore.ArealUK.chunk_16397 s98
  have s96 : leavesOK ctxLitU 183100000000 0 ((leaves.drop 32792).take 8) 183300000000 0 = true :=
    take_step (n := 2) (t := 8) (b := 32794) rfl rfl ArealUCore.ArealUK.chunk_16396 s97
  have s95 : leavesOK ctxLitU 183050000000 0 ((leaves.drop 32790).take 10) 183300000000 0 = true :=
    take_step (n := 2) (t := 10) (b := 32792) rfl rfl ArealUCore.ArealUK.chunk_16395 s96
  have s94 : leavesOK ctxLitU 183000000000 0 ((leaves.drop 32788).take 12) 183300000000 0 = true :=
    take_step (n := 2) (t := 12) (b := 32790) rfl rfl ArealUCore.ArealUK.chunk_16394 s95
  have s93 : leavesOK ctxLitU 182950000000 0 ((leaves.drop 32786).take 14) 183300000000 0 = true :=
    take_step (n := 2) (t := 14) (b := 32788) rfl rfl ArealUCore.ArealUK.chunk_16393 s94
  have s92 : leavesOK ctxLitU 182900000000 0 ((leaves.drop 32784).take 16) 183300000000 0 = true :=
    take_step (n := 2) (t := 16) (b := 32786) rfl rfl ArealUCore.ArealUK.chunk_16392 s93
  have s91 : leavesOK ctxLitU 182850000000 0 ((leaves.drop 32782).take 18) 183300000000 0 = true :=
    take_step (n := 2) (t := 18) (b := 32784) rfl rfl ArealUCore.ArealUK.chunk_16391 s92
  have s90 : leavesOK ctxLitU 182800000000 0 ((leaves.drop 32780).take 20) 183300000000 0 = true :=
    take_step (n := 2) (t := 20) (b := 32782) rfl rfl ArealUCore.ArealUK.chunk_16390 s91
  have s89 : leavesOK ctxLitU 182750000000 0 ((leaves.drop 32778).take 22) 183300000000 0 = true :=
    take_step (n := 2) (t := 22) (b := 32780) rfl rfl ArealUCore.ArealUK.chunk_16389 s90
  have s88 : leavesOK ctxLitU 182700000000 0 ((leaves.drop 32776).take 24) 183300000000 0 = true :=
    take_step (n := 2) (t := 24) (b := 32778) rfl rfl ArealUCore.ArealUK.chunk_16388 s89
  have s87 : leavesOK ctxLitU 182650000000 0 ((leaves.drop 32774).take 26) 183300000000 0 = true :=
    take_step (n := 2) (t := 26) (b := 32776) rfl rfl ArealUCore.ArealUK.chunk_16387 s88
  have s86 : leavesOK ctxLitU 182600000000 0 ((leaves.drop 32772).take 28) 183300000000 0 = true :=
    take_step (n := 2) (t := 28) (b := 32774) rfl rfl ArealUCore.ArealUK.chunk_16386 s87
  have s85 : leavesOK ctxLitU 182550000000 0 ((leaves.drop 32770).take 30) 183300000000 0 = true :=
    take_step (n := 2) (t := 30) (b := 32772) rfl rfl ArealUCore.ArealUK.chunk_16385 s86
  have s84 : leavesOK ctxLitU 182500000000 0 ((leaves.drop 32768).take 32) 183300000000 0 = true :=
    take_step (n := 2) (t := 32) (b := 32770) rfl rfl ArealUCore.ArealUK.chunk_16384 s85
  have s83 : leavesOK ctxLitU 182450000000 0 ((leaves.drop 32766).take 34) 183300000000 0 = true :=
    take_step (n := 2) (t := 34) (b := 32768) rfl rfl ArealUCore.ArealUK.chunk_16383 s84
  have s82 : leavesOK ctxLitU 182400000000 0 ((leaves.drop 32764).take 36) 183300000000 0 = true :=
    take_step (n := 2) (t := 36) (b := 32766) rfl rfl ArealUCore.ArealUK.chunk_16382 s83
  have s81 : leavesOK ctxLitU 182350000000 0 ((leaves.drop 32762).take 38) 183300000000 0 = true :=
    take_step (n := 2) (t := 38) (b := 32764) rfl rfl ArealUCore.ArealUK.chunk_16381 s82
  have s80 : leavesOK ctxLitU 182300000000 0 ((leaves.drop 32760).take 40) 183300000000 0 = true :=
    take_step (n := 2) (t := 40) (b := 32762) rfl rfl ArealUCore.ArealUK.chunk_16380 s81
  have s79 : leavesOK ctxLitU 182250000000 0 ((leaves.drop 32758).take 42) 183300000000 0 = true :=
    take_step (n := 2) (t := 42) (b := 32760) rfl rfl ArealUCore.ArealUK.chunk_16379 s80
  have s78 : leavesOK ctxLitU 182200000000 0 ((leaves.drop 32756).take 44) 183300000000 0 = true :=
    take_step (n := 2) (t := 44) (b := 32758) rfl rfl ArealUCore.ArealUK.chunk_16378 s79
  have s77 : leavesOK ctxLitU 182150000000 0 ((leaves.drop 32754).take 46) 183300000000 0 = true :=
    take_step (n := 2) (t := 46) (b := 32756) rfl rfl ArealUCore.ArealUK.chunk_16377 s78
  have s76 : leavesOK ctxLitU 182100000000 0 ((leaves.drop 32752).take 48) 183300000000 0 = true :=
    take_step (n := 2) (t := 48) (b := 32754) rfl rfl ArealUCore.ArealUK.chunk_16376 s77
  have s75 : leavesOK ctxLitU 182050000000 0 ((leaves.drop 32750).take 50) 183300000000 0 = true :=
    take_step (n := 2) (t := 50) (b := 32752) rfl rfl ArealUCore.ArealUK.chunk_16375 s76
  have s74 : leavesOK ctxLitU 182000000000 0 ((leaves.drop 32748).take 52) 183300000000 0 = true :=
    take_step (n := 2) (t := 52) (b := 32750) rfl rfl ArealUCore.ArealUK.chunk_16374 s75
  have s73 : leavesOK ctxLitU 181950000000 0 ((leaves.drop 32746).take 54) 183300000000 0 = true :=
    take_step (n := 2) (t := 54) (b := 32748) rfl rfl ArealUCore.ArealUK.chunk_16373 s74
  have s72 : leavesOK ctxLitU 181900000000 0 ((leaves.drop 32744).take 56) 183300000000 0 = true :=
    take_step (n := 2) (t := 56) (b := 32746) rfl rfl ArealUCore.ArealUK.chunk_16372 s73
  have s71 : leavesOK ctxLitU 181850000000 0 ((leaves.drop 32742).take 58) 183300000000 0 = true :=
    take_step (n := 2) (t := 58) (b := 32744) rfl rfl ArealUCore.ArealUK.chunk_16371 s72
  have s70 : leavesOK ctxLitU 181800000000 0 ((leaves.drop 32740).take 60) 183300000000 0 = true :=
    take_step (n := 2) (t := 60) (b := 32742) rfl rfl ArealUCore.ArealUK.chunk_16370 s71
  have s69 : leavesOK ctxLitU 181750000000 0 ((leaves.drop 32738).take 62) 183300000000 0 = true :=
    take_step (n := 2) (t := 62) (b := 32740) rfl rfl ArealUCore.ArealUK.chunk_16369 s70
  have s68 : leavesOK ctxLitU 181700000000 0 ((leaves.drop 32736).take 64) 183300000000 0 = true :=
    take_step (n := 2) (t := 64) (b := 32738) rfl rfl ArealUCore.ArealUK.chunk_16368 s69
  have s67 : leavesOK ctxLitU 181650000000 0 ((leaves.drop 32734).take 66) 183300000000 0 = true :=
    take_step (n := 2) (t := 66) (b := 32736) rfl rfl ArealUCore.ArealUK.chunk_16367 s68
  have s66 : leavesOK ctxLitU 181600000000 0 ((leaves.drop 32732).take 68) 183300000000 0 = true :=
    take_step (n := 2) (t := 68) (b := 32734) rfl rfl ArealUCore.ArealUK.chunk_16366 s67
  have s65 : leavesOK ctxLitU 181550000000 0 ((leaves.drop 32730).take 70) 183300000000 0 = true :=
    take_step (n := 2) (t := 70) (b := 32732) rfl rfl ArealUCore.ArealUK.chunk_16365 s66
  have s64 : leavesOK ctxLitU 181500000000 0 ((leaves.drop 32728).take 72) 183300000000 0 = true :=
    take_step (n := 2) (t := 72) (b := 32730) rfl rfl ArealUCore.ArealUK.chunk_16364 s65
  have s63 : leavesOK ctxLitU 181450000000 0 ((leaves.drop 32726).take 74) 183300000000 0 = true :=
    take_step (n := 2) (t := 74) (b := 32728) rfl rfl ArealUCore.ArealUK.chunk_16363 s64
  have s62 : leavesOK ctxLitU 181400000000 0 ((leaves.drop 32724).take 76) 183300000000 0 = true :=
    take_step (n := 2) (t := 76) (b := 32726) rfl rfl ArealUCore.ArealUK.chunk_16362 s63
  have s61 : leavesOK ctxLitU 181350000000 0 ((leaves.drop 32722).take 78) 183300000000 0 = true :=
    take_step (n := 2) (t := 78) (b := 32724) rfl rfl ArealUCore.ArealUK.chunk_16361 s62
  have s60 : leavesOK ctxLitU 181300000000 0 ((leaves.drop 32720).take 80) 183300000000 0 = true :=
    take_step (n := 2) (t := 80) (b := 32722) rfl rfl ArealUCore.ArealUK.chunk_16360 s61
  have s59 : leavesOK ctxLitU 181250000000 0 ((leaves.drop 32718).take 82) 183300000000 0 = true :=
    take_step (n := 2) (t := 82) (b := 32720) rfl rfl ArealUCore.ArealUK.chunk_16359 s60
  have s58 : leavesOK ctxLitU 181200000000 0 ((leaves.drop 32716).take 84) 183300000000 0 = true :=
    take_step (n := 2) (t := 84) (b := 32718) rfl rfl ArealUCore.ArealUK.chunk_16358 s59
  have s57 : leavesOK ctxLitU 181150000000 0 ((leaves.drop 32714).take 86) 183300000000 0 = true :=
    take_step (n := 2) (t := 86) (b := 32716) rfl rfl ArealUCore.ArealUK.chunk_16357 s58
  have s56 : leavesOK ctxLitU 181100000000 0 ((leaves.drop 32712).take 88) 183300000000 0 = true :=
    take_step (n := 2) (t := 88) (b := 32714) rfl rfl ArealUCore.ArealUK.chunk_16356 s57
  have s55 : leavesOK ctxLitU 181050000000 0 ((leaves.drop 32710).take 90) 183300000000 0 = true :=
    take_step (n := 2) (t := 90) (b := 32712) rfl rfl ArealUCore.ArealUK.chunk_16355 s56
  have s54 : leavesOK ctxLitU 181000000000 0 ((leaves.drop 32708).take 92) 183300000000 0 = true :=
    take_step (n := 2) (t := 92) (b := 32710) rfl rfl ArealUCore.ArealUK.chunk_16354 s55
  have s53 : leavesOK ctxLitU 180950000000 0 ((leaves.drop 32706).take 94) 183300000000 0 = true :=
    take_step (n := 2) (t := 94) (b := 32708) rfl rfl ArealUCore.ArealUK.chunk_16353 s54
  have s52 : leavesOK ctxLitU 180900000000 0 ((leaves.drop 32704).take 96) 183300000000 0 = true :=
    take_step (n := 2) (t := 96) (b := 32706) rfl rfl ArealUCore.ArealUK.chunk_16352 s53
  have s51 : leavesOK ctxLitU 180850000000 0 ((leaves.drop 32702).take 98) 183300000000 0 = true :=
    take_step (n := 2) (t := 98) (b := 32704) rfl rfl ArealUCore.ArealUK.chunk_16351 s52
  have s50 : leavesOK ctxLitU 180800000000 0 ((leaves.drop 32700).take 100) 183300000000 0 = true :=
    take_step (n := 2) (t := 100) (b := 32702) rfl rfl ArealUCore.ArealUK.chunk_16350 s51
  have s49 : leavesOK ctxLitU 180750000000 0 ((leaves.drop 32698).take 102) 183300000000 0 = true :=
    take_step (n := 2) (t := 102) (b := 32700) rfl rfl ArealUCore.ArealUK.chunk_16349 s50
  have s48 : leavesOK ctxLitU 180700000000 0 ((leaves.drop 32696).take 104) 183300000000 0 = true :=
    take_step (n := 2) (t := 104) (b := 32698) rfl rfl ArealUCore.ArealUK.chunk_16348 s49
  have s47 : leavesOK ctxLitU 180650000000 0 ((leaves.drop 32694).take 106) 183300000000 0 = true :=
    take_step (n := 2) (t := 106) (b := 32696) rfl rfl ArealUCore.ArealUK.chunk_16347 s48
  have s46 : leavesOK ctxLitU 180600000000 0 ((leaves.drop 32692).take 108) 183300000000 0 = true :=
    take_step (n := 2) (t := 108) (b := 32694) rfl rfl ArealUCore.ArealUK.chunk_16346 s47
  have s45 : leavesOK ctxLitU 180550000000 0 ((leaves.drop 32690).take 110) 183300000000 0 = true :=
    take_step (n := 2) (t := 110) (b := 32692) rfl rfl ArealUCore.ArealUK.chunk_16345 s46
  have s44 : leavesOK ctxLitU 180500000000 0 ((leaves.drop 32688).take 112) 183300000000 0 = true :=
    take_step (n := 2) (t := 112) (b := 32690) rfl rfl ArealUCore.ArealUK.chunk_16344 s45
  have s43 : leavesOK ctxLitU 180450000000 0 ((leaves.drop 32686).take 114) 183300000000 0 = true :=
    take_step (n := 2) (t := 114) (b := 32688) rfl rfl ArealUCore.ArealUK.chunk_16343 s44
  have s42 : leavesOK ctxLitU 180400000000 0 ((leaves.drop 32684).take 116) 183300000000 0 = true :=
    take_step (n := 2) (t := 116) (b := 32686) rfl rfl ArealUCore.ArealUK.chunk_16342 s43
  have s41 : leavesOK ctxLitU 180350000000 0 ((leaves.drop 32682).take 118) 183300000000 0 = true :=
    take_step (n := 2) (t := 118) (b := 32684) rfl rfl ArealUCore.ArealUK.chunk_16341 s42
  have s40 : leavesOK ctxLitU 180300000000 0 ((leaves.drop 32680).take 120) 183300000000 0 = true :=
    take_step (n := 2) (t := 120) (b := 32682) rfl rfl ArealUCore.ArealUK.chunk_16340 s41
  have s39 : leavesOK ctxLitU 180250000000 0 ((leaves.drop 32678).take 122) 183300000000 0 = true :=
    take_step (n := 2) (t := 122) (b := 32680) rfl rfl ArealUCore.ArealUK.chunk_16339 s40
  have s38 : leavesOK ctxLitU 180200000000 0 ((leaves.drop 32676).take 124) 183300000000 0 = true :=
    take_step (n := 2) (t := 124) (b := 32678) rfl rfl ArealUCore.ArealUK.chunk_16338 s39
  have s37 : leavesOK ctxLitU 180150000000 0 ((leaves.drop 32674).take 126) 183300000000 0 = true :=
    take_step (n := 2) (t := 126) (b := 32676) rfl rfl ArealUCore.ArealUK.chunk_16337 s38
  have s36 : leavesOK ctxLitU 180100000000 0 ((leaves.drop 32672).take 128) 183300000000 0 = true :=
    take_step (n := 2) (t := 128) (b := 32674) rfl rfl ArealUCore.ArealUK.chunk_16336 s37
  have s35 : leavesOK ctxLitU 180050000000 0 ((leaves.drop 32670).take 130) 183300000000 0 = true :=
    take_step (n := 2) (t := 130) (b := 32672) rfl rfl ArealUCore.ArealUK.chunk_16335 s36
  have s34 : leavesOK ctxLitU 180000000000 0 ((leaves.drop 32668).take 132) 183300000000 0 = true :=
    take_step (n := 2) (t := 132) (b := 32670) rfl rfl ArealUCore.ArealUK.chunk_16334 s35
  have s33 : leavesOK ctxLitU 179950000000 0 ((leaves.drop 32666).take 134) 183300000000 0 = true :=
    take_step (n := 2) (t := 134) (b := 32668) rfl rfl ArealUCore.ArealUK.chunk_16333 s34
  have s32 : leavesOK ctxLitU 179900000000 0 ((leaves.drop 32664).take 136) 183300000000 0 = true :=
    take_step (n := 2) (t := 136) (b := 32666) rfl rfl ArealUCore.ArealUK.chunk_16332 s33
  have s31 : leavesOK ctxLitU 179850000000 0 ((leaves.drop 32662).take 138) 183300000000 0 = true :=
    take_step (n := 2) (t := 138) (b := 32664) rfl rfl ArealUCore.ArealUK.chunk_16331 s32
  have s30 : leavesOK ctxLitU 179800000000 0 ((leaves.drop 32660).take 140) 183300000000 0 = true :=
    take_step (n := 2) (t := 140) (b := 32662) rfl rfl ArealUCore.ArealUK.chunk_16330 s31
  have s29 : leavesOK ctxLitU 179750000000 0 ((leaves.drop 32658).take 142) 183300000000 0 = true :=
    take_step (n := 2) (t := 142) (b := 32660) rfl rfl ArealUCore.ArealUK.chunk_16329 s30
  have s28 : leavesOK ctxLitU 179700000000 0 ((leaves.drop 32656).take 144) 183300000000 0 = true :=
    take_step (n := 2) (t := 144) (b := 32658) rfl rfl ArealUCore.ArealUK.chunk_16328 s29
  have s27 : leavesOK ctxLitU 179650000000 0 ((leaves.drop 32654).take 146) 183300000000 0 = true :=
    take_step (n := 2) (t := 146) (b := 32656) rfl rfl ArealUCore.ArealUK.chunk_16327 s28
  have s26 : leavesOK ctxLitU 179600000000 0 ((leaves.drop 32652).take 148) 183300000000 0 = true :=
    take_step (n := 2) (t := 148) (b := 32654) rfl rfl ArealUCore.ArealUK.chunk_16326 s27
  have s25 : leavesOK ctxLitU 179550000000 0 ((leaves.drop 32650).take 150) 183300000000 0 = true :=
    take_step (n := 2) (t := 150) (b := 32652) rfl rfl ArealUCore.ArealUK.chunk_16325 s26
  have s24 : leavesOK ctxLitU 179500000000 0 ((leaves.drop 32648).take 152) 183300000000 0 = true :=
    take_step (n := 2) (t := 152) (b := 32650) rfl rfl ArealUCore.ArealUK.chunk_16324 s25
  have s23 : leavesOK ctxLitU 179450000000 0 ((leaves.drop 32646).take 154) 183300000000 0 = true :=
    take_step (n := 2) (t := 154) (b := 32648) rfl rfl ArealUCore.ArealUK.chunk_16323 s24
  have s22 : leavesOK ctxLitU 179400000000 0 ((leaves.drop 32644).take 156) 183300000000 0 = true :=
    take_step (n := 2) (t := 156) (b := 32646) rfl rfl ArealUCore.ArealUK.chunk_16322 s23
  have s21 : leavesOK ctxLitU 179350000000 0 ((leaves.drop 32642).take 158) 183300000000 0 = true :=
    take_step (n := 2) (t := 158) (b := 32644) rfl rfl ArealUCore.ArealUK.chunk_16321 s22
  have s20 : leavesOK ctxLitU 179300000000 0 ((leaves.drop 32640).take 160) 183300000000 0 = true :=
    take_step (n := 2) (t := 160) (b := 32642) rfl rfl ArealUCore.ArealUK.chunk_16320 s21
  have s19 : leavesOK ctxLitU 179250000000 0 ((leaves.drop 32638).take 162) 183300000000 0 = true :=
    take_step (n := 2) (t := 162) (b := 32640) rfl rfl ArealUCore.ArealUK.chunk_16319 s20
  have s18 : leavesOK ctxLitU 179200000000 0 ((leaves.drop 32636).take 164) 183300000000 0 = true :=
    take_step (n := 2) (t := 164) (b := 32638) rfl rfl ArealUCore.ArealUK.chunk_16318 s19
  have s17 : leavesOK ctxLitU 179150000000 0 ((leaves.drop 32634).take 166) 183300000000 0 = true :=
    take_step (n := 2) (t := 166) (b := 32636) rfl rfl ArealUCore.ArealUK.chunk_16317 s18
  have s16 : leavesOK ctxLitU 179100000000 0 ((leaves.drop 32632).take 168) 183300000000 0 = true :=
    take_step (n := 2) (t := 168) (b := 32634) rfl rfl ArealUCore.ArealUK.chunk_16316 s17
  have s15 : leavesOK ctxLitU 179050000000 0 ((leaves.drop 32630).take 170) 183300000000 0 = true :=
    take_step (n := 2) (t := 170) (b := 32632) rfl rfl ArealUCore.ArealUK.chunk_16315 s16
  have s14 : leavesOK ctxLitU 179000000000 0 ((leaves.drop 32628).take 172) 183300000000 0 = true :=
    take_step (n := 2) (t := 172) (b := 32630) rfl rfl ArealUCore.ArealUK.chunk_16314 s15
  have s13 : leavesOK ctxLitU 178950000000 0 ((leaves.drop 32626).take 174) 183300000000 0 = true :=
    take_step (n := 2) (t := 174) (b := 32628) rfl rfl ArealUCore.ArealUK.chunk_16313 s14
  have s12 : leavesOK ctxLitU 178900000000 0 ((leaves.drop 32624).take 176) 183300000000 0 = true :=
    take_step (n := 2) (t := 176) (b := 32626) rfl rfl ArealUCore.ArealUK.chunk_16312 s13
  have s11 : leavesOK ctxLitU 178850000000 0 ((leaves.drop 32622).take 178) 183300000000 0 = true :=
    take_step (n := 2) (t := 178) (b := 32624) rfl rfl ArealUCore.ArealUK.chunk_16311 s12
  have s10 : leavesOK ctxLitU 178800000000 0 ((leaves.drop 32620).take 180) 183300000000 0 = true :=
    take_step (n := 2) (t := 180) (b := 32622) rfl rfl ArealUCore.ArealUK.chunk_16310 s11
  have s9 : leavesOK ctxLitU 178750000000 0 ((leaves.drop 32618).take 182) 183300000000 0 = true :=
    take_step (n := 2) (t := 182) (b := 32620) rfl rfl ArealUCore.ArealUK.chunk_16309 s10
  have s8 : leavesOK ctxLitU 178700000000 0 ((leaves.drop 32616).take 184) 183300000000 0 = true :=
    take_step (n := 2) (t := 184) (b := 32618) rfl rfl ArealUCore.ArealUK.chunk_16308 s9
  have s7 : leavesOK ctxLitU 178650000000 0 ((leaves.drop 32614).take 186) 183300000000 0 = true :=
    take_step (n := 2) (t := 186) (b := 32616) rfl rfl ArealUCore.ArealUK.chunk_16307 s8
  have s6 : leavesOK ctxLitU 178600000000 0 ((leaves.drop 32612).take 188) 183300000000 0 = true :=
    take_step (n := 2) (t := 188) (b := 32614) rfl rfl ArealUCore.ArealUK.chunk_16306 s7
  have s5 : leavesOK ctxLitU 178550000000 0 ((leaves.drop 32610).take 190) 183300000000 0 = true :=
    take_step (n := 2) (t := 190) (b := 32612) rfl rfl ArealUCore.ArealUK.chunk_16305 s6
  have s4 : leavesOK ctxLitU 178500000000 0 ((leaves.drop 32608).take 192) 183300000000 0 = true :=
    take_step (n := 2) (t := 192) (b := 32610) rfl rfl ArealUCore.ArealUK.chunk_16304 s5
  have s3 : leavesOK ctxLitU 178450000000 0 ((leaves.drop 32606).take 194) 183300000000 0 = true :=
    take_step (n := 2) (t := 194) (b := 32608) rfl rfl ArealUCore.ArealUK.chunk_16303 s4
  have s2 : leavesOK ctxLitU 178400000000 0 ((leaves.drop 32604).take 196) 183300000000 0 = true :=
    take_step (n := 2) (t := 196) (b := 32606) rfl rfl ArealUCore.ArealUK.chunk_16302 s3
  have s1 : leavesOK ctxLitU 178350000000 0 ((leaves.drop 32602).take 198) 183300000000 0 = true :=
    take_step (n := 2) (t := 198) (b := 32604) rfl rfl ArealUCore.ArealUK.chunk_16301 s2
  have s0 : leavesOK ctxLitU 178300000000 0 ((leaves.drop 32600).take 200) 183300000000 0 = true :=
    take_step (n := 2) (t := 200) (b := 32602) rfl rfl ArealUCore.ArealUK.chunk_16300 s1
  exact s0

end Areal.UCert

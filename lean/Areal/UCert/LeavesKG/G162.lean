import ArealUK.Chunk16200
import ArealUK.Chunk16201
import ArealUK.Chunk16202
import ArealUK.Chunk16203
import ArealUK.Chunk16204
import ArealUK.Chunk16205
import ArealUK.Chunk16206
import ArealUK.Chunk16207
import ArealUK.Chunk16208
import ArealUK.Chunk16209
import ArealUK.Chunk16210
import ArealUK.Chunk16211
import ArealUK.Chunk16212
import ArealUK.Chunk16213
import ArealUK.Chunk16214
import ArealUK.Chunk16215
import ArealUK.Chunk16216
import ArealUK.Chunk16217
import ArealUK.Chunk16218
import ArealUK.Chunk16219
import ArealUK.Chunk16220
import ArealUK.Chunk16221
import ArealUK.Chunk16222
import ArealUK.Chunk16223
import ArealUK.Chunk16224
import ArealUK.Chunk16225
import ArealUK.Chunk16226
import ArealUK.Chunk16227
import ArealUK.Chunk16228
import ArealUK.Chunk16229
import ArealUK.Chunk16230
import ArealUK.Chunk16231
import ArealUK.Chunk16232
import ArealUK.Chunk16233
import ArealUK.Chunk16234
import ArealUK.Chunk16235
import ArealUK.Chunk16236
import ArealUK.Chunk16237
import ArealUK.Chunk16238
import ArealUK.Chunk16239
import ArealUK.Chunk16240
import ArealUK.Chunk16241
import ArealUK.Chunk16242
import ArealUK.Chunk16243
import ArealUK.Chunk16244
import ArealUK.Chunk16245
import ArealUK.Chunk16246
import ArealUK.Chunk16247
import ArealUK.Chunk16248
import ArealUK.Chunk16249
import ArealUK.Chunk16250
import ArealUK.Chunk16251
import ArealUK.Chunk16252
import ArealUK.Chunk16253
import ArealUK.Chunk16254
import ArealUK.Chunk16255
import ArealUK.Chunk16256
import ArealUK.Chunk16257
import ArealUK.Chunk16258
import ArealUK.Chunk16259
import ArealUK.Chunk16260
import ArealUK.Chunk16261
import ArealUK.Chunk16262
import ArealUK.Chunk16263
import ArealUK.Chunk16264
import ArealUK.Chunk16265
import ArealUK.Chunk16266
import ArealUK.Chunk16267
import ArealUK.Chunk16268
import ArealUK.Chunk16269
import ArealUK.Chunk16270
import ArealUK.Chunk16271
import ArealUK.Chunk16272
import ArealUK.Chunk16273
import ArealUK.Chunk16274
import ArealUK.Chunk16275
import ArealUK.Chunk16276
import ArealUK.Chunk16277
import ArealUK.Chunk16278
import ArealUK.Chunk16279
import ArealUK.Chunk16280
import ArealUK.Chunk16281
import ArealUK.Chunk16282
import ArealUK.Chunk16283
import ArealUK.Chunk16284
import ArealUK.Chunk16285
import ArealUK.Chunk16286
import ArealUK.Chunk16287
import ArealUK.Chunk16288
import ArealUK.Chunk16289
import ArealUK.Chunk16290
import ArealUK.Chunk16291
import ArealUK.Chunk16292
import ArealUK.Chunk16293
import ArealUK.Chunk16294
import ArealUK.Chunk16295
import ArealUK.Chunk16296
import ArealUK.Chunk16297
import ArealUK.Chunk16298
import ArealUK.Chunk16299
import Areal.UCert.LeavesKGen

/-! Group 162 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_162 : leavesOK ctxLitU 173993750000 0 ((leaves.drop 32400).take 200) 178300000000 0 = true := by
  have s99 := ArealUCore.ArealUK.chunk_16299
  have s98 : leavesOK ctxLitU 178200000000 0 ((leaves.drop 32596).take 4) 178300000000 0 = true :=
    take_step (n := 2) (t := 4) (b := 32598) rfl rfl ArealUCore.ArealUK.chunk_16298 s99
  have s97 : leavesOK ctxLitU 178150000000 0 ((leaves.drop 32594).take 6) 178300000000 0 = true :=
    take_step (n := 2) (t := 6) (b := 32596) rfl rfl ArealUCore.ArealUK.chunk_16297 s98
  have s96 : leavesOK ctxLitU 178100000000 0 ((leaves.drop 32592).take 8) 178300000000 0 = true :=
    take_step (n := 2) (t := 8) (b := 32594) rfl rfl ArealUCore.ArealUK.chunk_16296 s97
  have s95 : leavesOK ctxLitU 178050000000 0 ((leaves.drop 32590).take 10) 178300000000 0 = true :=
    take_step (n := 2) (t := 10) (b := 32592) rfl rfl ArealUCore.ArealUK.chunk_16295 s96
  have s94 : leavesOK ctxLitU 178000000000 0 ((leaves.drop 32588).take 12) 178300000000 0 = true :=
    take_step (n := 2) (t := 12) (b := 32590) rfl rfl ArealUCore.ArealUK.chunk_16294 s95
  have s93 : leavesOK ctxLitU 177950000000 0 ((leaves.drop 32586).take 14) 178300000000 0 = true :=
    take_step (n := 2) (t := 14) (b := 32588) rfl rfl ArealUCore.ArealUK.chunk_16293 s94
  have s92 : leavesOK ctxLitU 177900000000 0 ((leaves.drop 32584).take 16) 178300000000 0 = true :=
    take_step (n := 2) (t := 16) (b := 32586) rfl rfl ArealUCore.ArealUK.chunk_16292 s93
  have s91 : leavesOK ctxLitU 177850000000 0 ((leaves.drop 32582).take 18) 178300000000 0 = true :=
    take_step (n := 2) (t := 18) (b := 32584) rfl rfl ArealUCore.ArealUK.chunk_16291 s92
  have s90 : leavesOK ctxLitU 177800000000 0 ((leaves.drop 32580).take 20) 178300000000 0 = true :=
    take_step (n := 2) (t := 20) (b := 32582) rfl rfl ArealUCore.ArealUK.chunk_16290 s91
  have s89 : leavesOK ctxLitU 177750000000 0 ((leaves.drop 32578).take 22) 178300000000 0 = true :=
    take_step (n := 2) (t := 22) (b := 32580) rfl rfl ArealUCore.ArealUK.chunk_16289 s90
  have s88 : leavesOK ctxLitU 177700000000 0 ((leaves.drop 32576).take 24) 178300000000 0 = true :=
    take_step (n := 2) (t := 24) (b := 32578) rfl rfl ArealUCore.ArealUK.chunk_16288 s89
  have s87 : leavesOK ctxLitU 177650000000 0 ((leaves.drop 32574).take 26) 178300000000 0 = true :=
    take_step (n := 2) (t := 26) (b := 32576) rfl rfl ArealUCore.ArealUK.chunk_16287 s88
  have s86 : leavesOK ctxLitU 177600000000 0 ((leaves.drop 32572).take 28) 178300000000 0 = true :=
    take_step (n := 2) (t := 28) (b := 32574) rfl rfl ArealUCore.ArealUK.chunk_16286 s87
  have s85 : leavesOK ctxLitU 177550000000 0 ((leaves.drop 32570).take 30) 178300000000 0 = true :=
    take_step (n := 2) (t := 30) (b := 32572) rfl rfl ArealUCore.ArealUK.chunk_16285 s86
  have s84 : leavesOK ctxLitU 177500000000 0 ((leaves.drop 32568).take 32) 178300000000 0 = true :=
    take_step (n := 2) (t := 32) (b := 32570) rfl rfl ArealUCore.ArealUK.chunk_16284 s85
  have s83 : leavesOK ctxLitU 177450000000 0 ((leaves.drop 32566).take 34) 178300000000 0 = true :=
    take_step (n := 2) (t := 34) (b := 32568) rfl rfl ArealUCore.ArealUK.chunk_16283 s84
  have s82 : leavesOK ctxLitU 177400000000 0 ((leaves.drop 32564).take 36) 178300000000 0 = true :=
    take_step (n := 2) (t := 36) (b := 32566) rfl rfl ArealUCore.ArealUK.chunk_16282 s83
  have s81 : leavesOK ctxLitU 177350000000 0 ((leaves.drop 32562).take 38) 178300000000 0 = true :=
    take_step (n := 2) (t := 38) (b := 32564) rfl rfl ArealUCore.ArealUK.chunk_16281 s82
  have s80 : leavesOK ctxLitU 177300000000 0 ((leaves.drop 32560).take 40) 178300000000 0 = true :=
    take_step (n := 2) (t := 40) (b := 32562) rfl rfl ArealUCore.ArealUK.chunk_16280 s81
  have s79 : leavesOK ctxLitU 177250000000 0 ((leaves.drop 32558).take 42) 178300000000 0 = true :=
    take_step (n := 2) (t := 42) (b := 32560) rfl rfl ArealUCore.ArealUK.chunk_16279 s80
  have s78 : leavesOK ctxLitU 177200000000 0 ((leaves.drop 32556).take 44) 178300000000 0 = true :=
    take_step (n := 2) (t := 44) (b := 32558) rfl rfl ArealUCore.ArealUK.chunk_16278 s79
  have s77 : leavesOK ctxLitU 177150000000 0 ((leaves.drop 32554).take 46) 178300000000 0 = true :=
    take_step (n := 2) (t := 46) (b := 32556) rfl rfl ArealUCore.ArealUK.chunk_16277 s78
  have s76 : leavesOK ctxLitU 177100000000 0 ((leaves.drop 32552).take 48) 178300000000 0 = true :=
    take_step (n := 2) (t := 48) (b := 32554) rfl rfl ArealUCore.ArealUK.chunk_16276 s77
  have s75 : leavesOK ctxLitU 177050000000 0 ((leaves.drop 32550).take 50) 178300000000 0 = true :=
    take_step (n := 2) (t := 50) (b := 32552) rfl rfl ArealUCore.ArealUK.chunk_16275 s76
  have s74 : leavesOK ctxLitU 177000000000 0 ((leaves.drop 32548).take 52) 178300000000 0 = true :=
    take_step (n := 2) (t := 52) (b := 32550) rfl rfl ArealUCore.ArealUK.chunk_16274 s75
  have s73 : leavesOK ctxLitU 176950000000 0 ((leaves.drop 32546).take 54) 178300000000 0 = true :=
    take_step (n := 2) (t := 54) (b := 32548) rfl rfl ArealUCore.ArealUK.chunk_16273 s74
  have s72 : leavesOK ctxLitU 176900000000 0 ((leaves.drop 32544).take 56) 178300000000 0 = true :=
    take_step (n := 2) (t := 56) (b := 32546) rfl rfl ArealUCore.ArealUK.chunk_16272 s73
  have s71 : leavesOK ctxLitU 176850000000 0 ((leaves.drop 32542).take 58) 178300000000 0 = true :=
    take_step (n := 2) (t := 58) (b := 32544) rfl rfl ArealUCore.ArealUK.chunk_16271 s72
  have s70 : leavesOK ctxLitU 176800000000 0 ((leaves.drop 32540).take 60) 178300000000 0 = true :=
    take_step (n := 2) (t := 60) (b := 32542) rfl rfl ArealUCore.ArealUK.chunk_16270 s71
  have s69 : leavesOK ctxLitU 176750000000 0 ((leaves.drop 32538).take 62) 178300000000 0 = true :=
    take_step (n := 2) (t := 62) (b := 32540) rfl rfl ArealUCore.ArealUK.chunk_16269 s70
  have s68 : leavesOK ctxLitU 176700000000 0 ((leaves.drop 32536).take 64) 178300000000 0 = true :=
    take_step (n := 2) (t := 64) (b := 32538) rfl rfl ArealUCore.ArealUK.chunk_16268 s69
  have s67 : leavesOK ctxLitU 176650000000 0 ((leaves.drop 32534).take 66) 178300000000 0 = true :=
    take_step (n := 2) (t := 66) (b := 32536) rfl rfl ArealUCore.ArealUK.chunk_16267 s68
  have s66 : leavesOK ctxLitU 176600000000 0 ((leaves.drop 32532).take 68) 178300000000 0 = true :=
    take_step (n := 2) (t := 68) (b := 32534) rfl rfl ArealUCore.ArealUK.chunk_16266 s67
  have s65 : leavesOK ctxLitU 176550000000 0 ((leaves.drop 32530).take 70) 178300000000 0 = true :=
    take_step (n := 2) (t := 70) (b := 32532) rfl rfl ArealUCore.ArealUK.chunk_16265 s66
  have s64 : leavesOK ctxLitU 176500000000 0 ((leaves.drop 32528).take 72) 178300000000 0 = true :=
    take_step (n := 2) (t := 72) (b := 32530) rfl rfl ArealUCore.ArealUK.chunk_16264 s65
  have s63 : leavesOK ctxLitU 176450000000 0 ((leaves.drop 32526).take 74) 178300000000 0 = true :=
    take_step (n := 2) (t := 74) (b := 32528) rfl rfl ArealUCore.ArealUK.chunk_16263 s64
  have s62 : leavesOK ctxLitU 176400000000 0 ((leaves.drop 32524).take 76) 178300000000 0 = true :=
    take_step (n := 2) (t := 76) (b := 32526) rfl rfl ArealUCore.ArealUK.chunk_16262 s63
  have s61 : leavesOK ctxLitU 176350000000 0 ((leaves.drop 32522).take 78) 178300000000 0 = true :=
    take_step (n := 2) (t := 78) (b := 32524) rfl rfl ArealUCore.ArealUK.chunk_16261 s62
  have s60 : leavesOK ctxLitU 176300000000 0 ((leaves.drop 32520).take 80) 178300000000 0 = true :=
    take_step (n := 2) (t := 80) (b := 32522) rfl rfl ArealUCore.ArealUK.chunk_16260 s61
  have s59 : leavesOK ctxLitU 176250000000 0 ((leaves.drop 32518).take 82) 178300000000 0 = true :=
    take_step (n := 2) (t := 82) (b := 32520) rfl rfl ArealUCore.ArealUK.chunk_16259 s60
  have s58 : leavesOK ctxLitU 176200000000 0 ((leaves.drop 32516).take 84) 178300000000 0 = true :=
    take_step (n := 2) (t := 84) (b := 32518) rfl rfl ArealUCore.ArealUK.chunk_16258 s59
  have s57 : leavesOK ctxLitU 176150000000 0 ((leaves.drop 32514).take 86) 178300000000 0 = true :=
    take_step (n := 2) (t := 86) (b := 32516) rfl rfl ArealUCore.ArealUK.chunk_16257 s58
  have s56 : leavesOK ctxLitU 176100000000 0 ((leaves.drop 32512).take 88) 178300000000 0 = true :=
    take_step (n := 2) (t := 88) (b := 32514) rfl rfl ArealUCore.ArealUK.chunk_16256 s57
  have s55 : leavesOK ctxLitU 176050000000 0 ((leaves.drop 32510).take 90) 178300000000 0 = true :=
    take_step (n := 2) (t := 90) (b := 32512) rfl rfl ArealUCore.ArealUK.chunk_16255 s56
  have s54 : leavesOK ctxLitU 176000000000 0 ((leaves.drop 32508).take 92) 178300000000 0 = true :=
    take_step (n := 2) (t := 92) (b := 32510) rfl rfl ArealUCore.ArealUK.chunk_16254 s55
  have s53 : leavesOK ctxLitU 175950000000 0 ((leaves.drop 32506).take 94) 178300000000 0 = true :=
    take_step (n := 2) (t := 94) (b := 32508) rfl rfl ArealUCore.ArealUK.chunk_16253 s54
  have s52 : leavesOK ctxLitU 175900000000 0 ((leaves.drop 32504).take 96) 178300000000 0 = true :=
    take_step (n := 2) (t := 96) (b := 32506) rfl rfl ArealUCore.ArealUK.chunk_16252 s53
  have s51 : leavesOK ctxLitU 175850000000 0 ((leaves.drop 32502).take 98) 178300000000 0 = true :=
    take_step (n := 2) (t := 98) (b := 32504) rfl rfl ArealUCore.ArealUK.chunk_16251 s52
  have s50 : leavesOK ctxLitU 175800000000 0 ((leaves.drop 32500).take 100) 178300000000 0 = true :=
    take_step (n := 2) (t := 100) (b := 32502) rfl rfl ArealUCore.ArealUK.chunk_16250 s51
  have s49 : leavesOK ctxLitU 175750000000 0 ((leaves.drop 32498).take 102) 178300000000 0 = true :=
    take_step (n := 2) (t := 102) (b := 32500) rfl rfl ArealUCore.ArealUK.chunk_16249 s50
  have s48 : leavesOK ctxLitU 175700000000 0 ((leaves.drop 32496).take 104) 178300000000 0 = true :=
    take_step (n := 2) (t := 104) (b := 32498) rfl rfl ArealUCore.ArealUK.chunk_16248 s49
  have s47 : leavesOK ctxLitU 175650000000 0 ((leaves.drop 32494).take 106) 178300000000 0 = true :=
    take_step (n := 2) (t := 106) (b := 32496) rfl rfl ArealUCore.ArealUK.chunk_16247 s48
  have s46 : leavesOK ctxLitU 175600000000 0 ((leaves.drop 32492).take 108) 178300000000 0 = true :=
    take_step (n := 2) (t := 108) (b := 32494) rfl rfl ArealUCore.ArealUK.chunk_16246 s47
  have s45 : leavesOK ctxLitU 175550000000 0 ((leaves.drop 32490).take 110) 178300000000 0 = true :=
    take_step (n := 2) (t := 110) (b := 32492) rfl rfl ArealUCore.ArealUK.chunk_16245 s46
  have s44 : leavesOK ctxLitU 175500000000 0 ((leaves.drop 32488).take 112) 178300000000 0 = true :=
    take_step (n := 2) (t := 112) (b := 32490) rfl rfl ArealUCore.ArealUK.chunk_16244 s45
  have s43 : leavesOK ctxLitU 175450000000 0 ((leaves.drop 32486).take 114) 178300000000 0 = true :=
    take_step (n := 2) (t := 114) (b := 32488) rfl rfl ArealUCore.ArealUK.chunk_16243 s44
  have s42 : leavesOK ctxLitU 175400000000 0 ((leaves.drop 32484).take 116) 178300000000 0 = true :=
    take_step (n := 2) (t := 116) (b := 32486) rfl rfl ArealUCore.ArealUK.chunk_16242 s43
  have s41 : leavesOK ctxLitU 175350000000 0 ((leaves.drop 32482).take 118) 178300000000 0 = true :=
    take_step (n := 2) (t := 118) (b := 32484) rfl rfl ArealUCore.ArealUK.chunk_16241 s42
  have s40 : leavesOK ctxLitU 175300000000 0 ((leaves.drop 32480).take 120) 178300000000 0 = true :=
    take_step (n := 2) (t := 120) (b := 32482) rfl rfl ArealUCore.ArealUK.chunk_16240 s41
  have s39 : leavesOK ctxLitU 175250000000 0 ((leaves.drop 32478).take 122) 178300000000 0 = true :=
    take_step (n := 2) (t := 122) (b := 32480) rfl rfl ArealUCore.ArealUK.chunk_16239 s40
  have s38 : leavesOK ctxLitU 175200000000 0 ((leaves.drop 32476).take 124) 178300000000 0 = true :=
    take_step (n := 2) (t := 124) (b := 32478) rfl rfl ArealUCore.ArealUK.chunk_16238 s39
  have s37 : leavesOK ctxLitU 175150000000 0 ((leaves.drop 32474).take 126) 178300000000 0 = true :=
    take_step (n := 2) (t := 126) (b := 32476) rfl rfl ArealUCore.ArealUK.chunk_16237 s38
  have s36 : leavesOK ctxLitU 175100000000 0 ((leaves.drop 32472).take 128) 178300000000 0 = true :=
    take_step (n := 2) (t := 128) (b := 32474) rfl rfl ArealUCore.ArealUK.chunk_16236 s37
  have s35 : leavesOK ctxLitU 175050000000 0 ((leaves.drop 32470).take 130) 178300000000 0 = true :=
    take_step (n := 2) (t := 130) (b := 32472) rfl rfl ArealUCore.ArealUK.chunk_16235 s36
  have s34 : leavesOK ctxLitU 175000000000 0 ((leaves.drop 32468).take 132) 178300000000 0 = true :=
    take_step (n := 2) (t := 132) (b := 32470) rfl rfl ArealUCore.ArealUK.chunk_16234 s35
  have s33 : leavesOK ctxLitU 174950000000 0 ((leaves.drop 32466).take 134) 178300000000 0 = true :=
    take_step (n := 2) (t := 134) (b := 32468) rfl rfl ArealUCore.ArealUK.chunk_16233 s34
  have s32 : leavesOK ctxLitU 174900000000 0 ((leaves.drop 32464).take 136) 178300000000 0 = true :=
    take_step (n := 2) (t := 136) (b := 32466) rfl rfl ArealUCore.ArealUK.chunk_16232 s33
  have s31 : leavesOK ctxLitU 174850000000 0 ((leaves.drop 32462).take 138) 178300000000 0 = true :=
    take_step (n := 2) (t := 138) (b := 32464) rfl rfl ArealUCore.ArealUK.chunk_16231 s32
  have s30 : leavesOK ctxLitU 174800000000 0 ((leaves.drop 32460).take 140) 178300000000 0 = true :=
    take_step (n := 2) (t := 140) (b := 32462) rfl rfl ArealUCore.ArealUK.chunk_16230 s31
  have s29 : leavesOK ctxLitU 174750000000 0 ((leaves.drop 32458).take 142) 178300000000 0 = true :=
    take_step (n := 2) (t := 142) (b := 32460) rfl rfl ArealUCore.ArealUK.chunk_16229 s30
  have s28 : leavesOK ctxLitU 349425000000 1 ((leaves.drop 32456).take 144) 178300000000 0 = true :=
    take_step (n := 2) (t := 144) (b := 32458) rfl rfl ArealUCore.ArealUK.chunk_16228 s29
  have s27 : leavesOK ctxLitU 698775000000 2 ((leaves.drop 32454).take 146) 178300000000 0 = true :=
    take_step (n := 2) (t := 146) (b := 32456) rfl rfl ArealUCore.ArealUK.chunk_16227 s28
  have s26 : leavesOK ctxLitU 349350000000 1 ((leaves.drop 32452).take 148) 178300000000 0 = true :=
    take_step (n := 2) (t := 148) (b := 32454) rfl rfl ArealUCore.ArealUK.chunk_16226 s27
  have s25 : leavesOK ctxLitU 174625000000 0 ((leaves.drop 32450).take 150) 178300000000 0 = true :=
    take_step (n := 2) (t := 150) (b := 32452) rfl rfl ArealUCore.ArealUK.chunk_16225 s26
  have s24 : leavesOK ctxLitU 174575000000 0 ((leaves.drop 32448).take 152) 178300000000 0 = true :=
    take_step (n := 2) (t := 152) (b := 32450) rfl rfl ArealUCore.ArealUK.chunk_16224 s25
  have s23 : leavesOK ctxLitU 174525000000 0 ((leaves.drop 32446).take 154) 178300000000 0 = true :=
    take_step (n := 2) (t := 154) (b := 32448) rfl rfl ArealUCore.ArealUK.chunk_16223 s24
  have s22 : leavesOK ctxLitU 349000000000 1 ((leaves.drop 32444).take 156) 178300000000 0 = true :=
    take_step (n := 2) (t := 156) (b := 32446) rfl rfl ArealUCore.ArealUK.chunk_16222 s23
  have s21 : leavesOK ctxLitU 174450000000 0 ((leaves.drop 32442).take 158) 178300000000 0 = true :=
    take_step (n := 2) (t := 158) (b := 32444) rfl rfl ArealUCore.ArealUK.chunk_16221 s22
  have s20 : leavesOK ctxLitU 174400000000 0 ((leaves.drop 32440).take 160) 178300000000 0 = true :=
    take_step (n := 2) (t := 160) (b := 32442) rfl rfl ArealUCore.ArealUK.chunk_16220 s21
  have s19 : leavesOK ctxLitU 697525000000 2 ((leaves.drop 32438).take 162) 178300000000 0 = true :=
    take_step (n := 2) (t := 162) (b := 32440) rfl rfl ArealUCore.ArealUK.chunk_16219 s20
  have s18 : leavesOK ctxLitU 1395000000000 3 ((leaves.drop 32436).take 164) 178300000000 0 = true :=
    take_step (n := 2) (t := 164) (b := 32438) rfl rfl ArealUCore.ArealUK.chunk_16218 s19
  have s17 : leavesOK ctxLitU 2789950000000 4 ((leaves.drop 32434).take 166) 178300000000 0 = true :=
    take_step (n := 2) (t := 166) (b := 32436) rfl rfl ArealUCore.ArealUK.chunk_16217 s18
  have s16 : leavesOK ctxLitU 697450000000 2 ((leaves.drop 32432).take 168) 178300000000 0 = true :=
    take_step (n := 2) (t := 168) (b := 32434) rfl rfl ArealUCore.ArealUK.chunk_16216 s17
  have s15 : leavesOK ctxLitU 348675000000 1 ((leaves.drop 32430).take 170) 178300000000 0 = true :=
    take_step (n := 2) (t := 170) (b := 32432) rfl rfl ArealUCore.ArealUK.chunk_16215 s16
  have s14 : leavesOK ctxLitU 348625000000 1 ((leaves.drop 32428).take 172) 178300000000 0 = true :=
    take_step (n := 2) (t := 172) (b := 32430) rfl rfl ArealUCore.ArealUK.chunk_16214 s15
  have s13 : leavesOK ctxLitU 697200000000 2 ((leaves.drop 32426).take 174) 178300000000 0 = true :=
    take_step (n := 2) (t := 174) (b := 32428) rfl rfl ArealUCore.ArealUK.chunk_16213 s14
  have s12 : leavesOK ctxLitU 697150000000 2 ((leaves.drop 32424).take 176) 178300000000 0 = true :=
    take_step (n := 2) (t := 176) (b := 32426) rfl rfl ArealUCore.ArealUK.chunk_16212 s13
  have s11 : leavesOK ctxLitU 174250000000 0 ((leaves.drop 32422).take 178) 178300000000 0 = true :=
    take_step (n := 2) (t := 178) (b := 32424) rfl rfl ArealUCore.ArealUK.chunk_16211 s12
  have s10 : leavesOK ctxLitU 174200000000 0 ((leaves.drop 32420).take 180) 178300000000 0 = true :=
    take_step (n := 2) (t := 180) (b := 32422) rfl rfl ArealUCore.ArealUK.chunk_16210 s11
  have s9 : leavesOK ctxLitU 348350000000 1 ((leaves.drop 32418).take 182) 178300000000 0 = true :=
    take_step (n := 2) (t := 182) (b := 32420) rfl rfl ArealUCore.ArealUK.chunk_16209 s10
  have s8 : leavesOK ctxLitU 348300000000 1 ((leaves.drop 32416).take 184) 178300000000 0 = true :=
    take_step (n := 2) (t := 184) (b := 32418) rfl rfl ArealUCore.ArealUK.chunk_16208 s9
  have s7 : leavesOK ctxLitU 348250000000 1 ((leaves.drop 32414).take 186) 178300000000 0 = true :=
    take_step (n := 2) (t := 186) (b := 32416) rfl rfl ArealUCore.ArealUK.chunk_16207 s8
  have s6 : leavesOK ctxLitU 348200000000 1 ((leaves.drop 32412).take 188) 178300000000 0 = true :=
    take_step (n := 2) (t := 188) (b := 32414) rfl rfl ArealUCore.ArealUK.chunk_16206 s7
  have s5 : leavesOK ctxLitU 174062500000 0 ((leaves.drop 32410).take 190) 178300000000 0 = true :=
    take_step (n := 2) (t := 190) (b := 32412) rfl rfl ArealUCore.ArealUK.chunk_16205 s6
  have s4 : leavesOK ctxLitU 174043750000 0 ((leaves.drop 32408).take 192) 178300000000 0 = true :=
    take_step (n := 2) (t := 192) (b := 32410) rfl rfl ArealUCore.ArealUK.chunk_16204 s5
  have s3 : leavesOK ctxLitU 174031250000 0 ((leaves.drop 32406).take 194) 178300000000 0 = true :=
    take_step (n := 2) (t := 194) (b := 32408) rfl rfl ArealUCore.ArealUK.chunk_16203 s4
  have s2 : leavesOK ctxLitU 174018750000 0 ((leaves.drop 32404).take 196) 178300000000 0 = true :=
    take_step (n := 2) (t := 196) (b := 32406) rfl rfl ArealUCore.ArealUK.chunk_16202 s3
  have s1 : leavesOK ctxLitU 174006250000 0 ((leaves.drop 32402).take 198) 178300000000 0 = true :=
    take_step (n := 2) (t := 198) (b := 32404) rfl rfl ArealUCore.ArealUK.chunk_16201 s2
  have s0 : leavesOK ctxLitU 173993750000 0 ((leaves.drop 32400).take 200) 178300000000 0 = true :=
    take_step (n := 2) (t := 200) (b := 32402) rfl rfl ArealUCore.ArealUK.chunk_16200 s1
  exact s0

end Areal.UCert

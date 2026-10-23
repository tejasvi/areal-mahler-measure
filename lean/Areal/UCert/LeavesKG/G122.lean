import ArealUK.Chunk12200
import ArealUK.Chunk12201
import ArealUK.Chunk12202
import ArealUK.Chunk12203
import ArealUK.Chunk12204
import ArealUK.Chunk12205
import ArealUK.Chunk12206
import ArealUK.Chunk12207
import ArealUK.Chunk12208
import ArealUK.Chunk12209
import ArealUK.Chunk12210
import ArealUK.Chunk12211
import ArealUK.Chunk12212
import ArealUK.Chunk12213
import ArealUK.Chunk12214
import ArealUK.Chunk12215
import ArealUK.Chunk12216
import ArealUK.Chunk12217
import ArealUK.Chunk12218
import ArealUK.Chunk12219
import ArealUK.Chunk12220
import ArealUK.Chunk12221
import ArealUK.Chunk12222
import ArealUK.Chunk12223
import ArealUK.Chunk12224
import ArealUK.Chunk12225
import ArealUK.Chunk12226
import ArealUK.Chunk12227
import ArealUK.Chunk12228
import ArealUK.Chunk12229
import ArealUK.Chunk12230
import ArealUK.Chunk12231
import ArealUK.Chunk12232
import ArealUK.Chunk12233
import ArealUK.Chunk12234
import ArealUK.Chunk12235
import ArealUK.Chunk12236
import ArealUK.Chunk12237
import ArealUK.Chunk12238
import ArealUK.Chunk12239
import ArealUK.Chunk12240
import ArealUK.Chunk12241
import ArealUK.Chunk12242
import ArealUK.Chunk12243
import ArealUK.Chunk12244
import ArealUK.Chunk12245
import ArealUK.Chunk12246
import ArealUK.Chunk12247
import ArealUK.Chunk12248
import ArealUK.Chunk12249
import ArealUK.Chunk12250
import ArealUK.Chunk12251
import ArealUK.Chunk12252
import ArealUK.Chunk12253
import ArealUK.Chunk12254
import ArealUK.Chunk12255
import ArealUK.Chunk12256
import ArealUK.Chunk12257
import ArealUK.Chunk12258
import ArealUK.Chunk12259
import ArealUK.Chunk12260
import ArealUK.Chunk12261
import ArealUK.Chunk12262
import ArealUK.Chunk12263
import ArealUK.Chunk12264
import ArealUK.Chunk12265
import ArealUK.Chunk12266
import ArealUK.Chunk12267
import ArealUK.Chunk12268
import ArealUK.Chunk12269
import ArealUK.Chunk12270
import ArealUK.Chunk12271
import ArealUK.Chunk12272
import ArealUK.Chunk12273
import ArealUK.Chunk12274
import ArealUK.Chunk12275
import ArealUK.Chunk12276
import ArealUK.Chunk12277
import ArealUK.Chunk12278
import ArealUK.Chunk12279
import ArealUK.Chunk12280
import ArealUK.Chunk12281
import ArealUK.Chunk12282
import ArealUK.Chunk12283
import ArealUK.Chunk12284
import ArealUK.Chunk12285
import ArealUK.Chunk12286
import ArealUK.Chunk12287
import ArealUK.Chunk12288
import ArealUK.Chunk12289
import ArealUK.Chunk12290
import ArealUK.Chunk12291
import ArealUK.Chunk12292
import ArealUK.Chunk12293
import ArealUK.Chunk12294
import ArealUK.Chunk12295
import ArealUK.Chunk12296
import ArealUK.Chunk12297
import ArealUK.Chunk12298
import ArealUK.Chunk12299
import Areal.UCert.LeavesKGen

/-! Group 122 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_122 : leavesOK ctxLitU 487775000000 2 ((leaves.drop 24400).take 200) 492775000000 2 = true := by
  have s99 := ArealUCore.ArealUK.chunk_12299
  have s98 : leavesOK ctxLitU 492675000000 2 ((leaves.drop 24596).take 4) 492775000000 2 = true :=
    take_step (n := 2) (t := 4) (b := 24598) rfl rfl ArealUCore.ArealUK.chunk_12298 s99
  have s97 : leavesOK ctxLitU 492625000000 2 ((leaves.drop 24594).take 6) 492775000000 2 = true :=
    take_step (n := 2) (t := 6) (b := 24596) rfl rfl ArealUCore.ArealUK.chunk_12297 s98
  have s96 : leavesOK ctxLitU 492575000000 2 ((leaves.drop 24592).take 8) 492775000000 2 = true :=
    take_step (n := 2) (t := 8) (b := 24594) rfl rfl ArealUCore.ArealUK.chunk_12296 s97
  have s95 : leavesOK ctxLitU 492525000000 2 ((leaves.drop 24590).take 10) 492775000000 2 = true :=
    take_step (n := 2) (t := 10) (b := 24592) rfl rfl ArealUCore.ArealUK.chunk_12295 s96
  have s94 : leavesOK ctxLitU 492475000000 2 ((leaves.drop 24588).take 12) 492775000000 2 = true :=
    take_step (n := 2) (t := 12) (b := 24590) rfl rfl ArealUCore.ArealUK.chunk_12294 s95
  have s93 : leavesOK ctxLitU 492425000000 2 ((leaves.drop 24586).take 14) 492775000000 2 = true :=
    take_step (n := 2) (t := 14) (b := 24588) rfl rfl ArealUCore.ArealUK.chunk_12293 s94
  have s92 : leavesOK ctxLitU 492375000000 2 ((leaves.drop 24584).take 16) 492775000000 2 = true :=
    take_step (n := 2) (t := 16) (b := 24586) rfl rfl ArealUCore.ArealUK.chunk_12292 s93
  have s91 : leavesOK ctxLitU 492325000000 2 ((leaves.drop 24582).take 18) 492775000000 2 = true :=
    take_step (n := 2) (t := 18) (b := 24584) rfl rfl ArealUCore.ArealUK.chunk_12291 s92
  have s90 : leavesOK ctxLitU 492275000000 2 ((leaves.drop 24580).take 20) 492775000000 2 = true :=
    take_step (n := 2) (t := 20) (b := 24582) rfl rfl ArealUCore.ArealUK.chunk_12290 s91
  have s89 : leavesOK ctxLitU 492225000000 2 ((leaves.drop 24578).take 22) 492775000000 2 = true :=
    take_step (n := 2) (t := 22) (b := 24580) rfl rfl ArealUCore.ArealUK.chunk_12289 s90
  have s88 : leavesOK ctxLitU 492175000000 2 ((leaves.drop 24576).take 24) 492775000000 2 = true :=
    take_step (n := 2) (t := 24) (b := 24578) rfl rfl ArealUCore.ArealUK.chunk_12288 s89
  have s87 : leavesOK ctxLitU 492125000000 2 ((leaves.drop 24574).take 26) 492775000000 2 = true :=
    take_step (n := 2) (t := 26) (b := 24576) rfl rfl ArealUCore.ArealUK.chunk_12287 s88
  have s86 : leavesOK ctxLitU 492075000000 2 ((leaves.drop 24572).take 28) 492775000000 2 = true :=
    take_step (n := 2) (t := 28) (b := 24574) rfl rfl ArealUCore.ArealUK.chunk_12286 s87
  have s85 : leavesOK ctxLitU 492025000000 2 ((leaves.drop 24570).take 30) 492775000000 2 = true :=
    take_step (n := 2) (t := 30) (b := 24572) rfl rfl ArealUCore.ArealUK.chunk_12285 s86
  have s84 : leavesOK ctxLitU 491975000000 2 ((leaves.drop 24568).take 32) 492775000000 2 = true :=
    take_step (n := 2) (t := 32) (b := 24570) rfl rfl ArealUCore.ArealUK.chunk_12284 s85
  have s83 : leavesOK ctxLitU 491925000000 2 ((leaves.drop 24566).take 34) 492775000000 2 = true :=
    take_step (n := 2) (t := 34) (b := 24568) rfl rfl ArealUCore.ArealUK.chunk_12283 s84
  have s82 : leavesOK ctxLitU 491875000000 2 ((leaves.drop 24564).take 36) 492775000000 2 = true :=
    take_step (n := 2) (t := 36) (b := 24566) rfl rfl ArealUCore.ArealUK.chunk_12282 s83
  have s81 : leavesOK ctxLitU 491825000000 2 ((leaves.drop 24562).take 38) 492775000000 2 = true :=
    take_step (n := 2) (t := 38) (b := 24564) rfl rfl ArealUCore.ArealUK.chunk_12281 s82
  have s80 : leavesOK ctxLitU 491775000000 2 ((leaves.drop 24560).take 40) 492775000000 2 = true :=
    take_step (n := 2) (t := 40) (b := 24562) rfl rfl ArealUCore.ArealUK.chunk_12280 s81
  have s79 : leavesOK ctxLitU 491725000000 2 ((leaves.drop 24558).take 42) 492775000000 2 = true :=
    take_step (n := 2) (t := 42) (b := 24560) rfl rfl ArealUCore.ArealUK.chunk_12279 s80
  have s78 : leavesOK ctxLitU 491675000000 2 ((leaves.drop 24556).take 44) 492775000000 2 = true :=
    take_step (n := 2) (t := 44) (b := 24558) rfl rfl ArealUCore.ArealUK.chunk_12278 s79
  have s77 : leavesOK ctxLitU 491625000000 2 ((leaves.drop 24554).take 46) 492775000000 2 = true :=
    take_step (n := 2) (t := 46) (b := 24556) rfl rfl ArealUCore.ArealUK.chunk_12277 s78
  have s76 : leavesOK ctxLitU 491575000000 2 ((leaves.drop 24552).take 48) 492775000000 2 = true :=
    take_step (n := 2) (t := 48) (b := 24554) rfl rfl ArealUCore.ArealUK.chunk_12276 s77
  have s75 : leavesOK ctxLitU 491525000000 2 ((leaves.drop 24550).take 50) 492775000000 2 = true :=
    take_step (n := 2) (t := 50) (b := 24552) rfl rfl ArealUCore.ArealUK.chunk_12275 s76
  have s74 : leavesOK ctxLitU 491475000000 2 ((leaves.drop 24548).take 52) 492775000000 2 = true :=
    take_step (n := 2) (t := 52) (b := 24550) rfl rfl ArealUCore.ArealUK.chunk_12274 s75
  have s73 : leavesOK ctxLitU 491425000000 2 ((leaves.drop 24546).take 54) 492775000000 2 = true :=
    take_step (n := 2) (t := 54) (b := 24548) rfl rfl ArealUCore.ArealUK.chunk_12273 s74
  have s72 : leavesOK ctxLitU 491375000000 2 ((leaves.drop 24544).take 56) 492775000000 2 = true :=
    take_step (n := 2) (t := 56) (b := 24546) rfl rfl ArealUCore.ArealUK.chunk_12272 s73
  have s71 : leavesOK ctxLitU 491325000000 2 ((leaves.drop 24542).take 58) 492775000000 2 = true :=
    take_step (n := 2) (t := 58) (b := 24544) rfl rfl ArealUCore.ArealUK.chunk_12271 s72
  have s70 : leavesOK ctxLitU 491275000000 2 ((leaves.drop 24540).take 60) 492775000000 2 = true :=
    take_step (n := 2) (t := 60) (b := 24542) rfl rfl ArealUCore.ArealUK.chunk_12270 s71
  have s69 : leavesOK ctxLitU 491225000000 2 ((leaves.drop 24538).take 62) 492775000000 2 = true :=
    take_step (n := 2) (t := 62) (b := 24540) rfl rfl ArealUCore.ArealUK.chunk_12269 s70
  have s68 : leavesOK ctxLitU 491175000000 2 ((leaves.drop 24536).take 64) 492775000000 2 = true :=
    take_step (n := 2) (t := 64) (b := 24538) rfl rfl ArealUCore.ArealUK.chunk_12268 s69
  have s67 : leavesOK ctxLitU 491125000000 2 ((leaves.drop 24534).take 66) 492775000000 2 = true :=
    take_step (n := 2) (t := 66) (b := 24536) rfl rfl ArealUCore.ArealUK.chunk_12267 s68
  have s66 : leavesOK ctxLitU 491075000000 2 ((leaves.drop 24532).take 68) 492775000000 2 = true :=
    take_step (n := 2) (t := 68) (b := 24534) rfl rfl ArealUCore.ArealUK.chunk_12266 s67
  have s65 : leavesOK ctxLitU 491025000000 2 ((leaves.drop 24530).take 70) 492775000000 2 = true :=
    take_step (n := 2) (t := 70) (b := 24532) rfl rfl ArealUCore.ArealUK.chunk_12265 s66
  have s64 : leavesOK ctxLitU 490975000000 2 ((leaves.drop 24528).take 72) 492775000000 2 = true :=
    take_step (n := 2) (t := 72) (b := 24530) rfl rfl ArealUCore.ArealUK.chunk_12264 s65
  have s63 : leavesOK ctxLitU 490925000000 2 ((leaves.drop 24526).take 74) 492775000000 2 = true :=
    take_step (n := 2) (t := 74) (b := 24528) rfl rfl ArealUCore.ArealUK.chunk_12263 s64
  have s62 : leavesOK ctxLitU 490875000000 2 ((leaves.drop 24524).take 76) 492775000000 2 = true :=
    take_step (n := 2) (t := 76) (b := 24526) rfl rfl ArealUCore.ArealUK.chunk_12262 s63
  have s61 : leavesOK ctxLitU 490825000000 2 ((leaves.drop 24522).take 78) 492775000000 2 = true :=
    take_step (n := 2) (t := 78) (b := 24524) rfl rfl ArealUCore.ArealUK.chunk_12261 s62
  have s60 : leavesOK ctxLitU 490775000000 2 ((leaves.drop 24520).take 80) 492775000000 2 = true :=
    take_step (n := 2) (t := 80) (b := 24522) rfl rfl ArealUCore.ArealUK.chunk_12260 s61
  have s59 : leavesOK ctxLitU 490725000000 2 ((leaves.drop 24518).take 82) 492775000000 2 = true :=
    take_step (n := 2) (t := 82) (b := 24520) rfl rfl ArealUCore.ArealUK.chunk_12259 s60
  have s58 : leavesOK ctxLitU 490675000000 2 ((leaves.drop 24516).take 84) 492775000000 2 = true :=
    take_step (n := 2) (t := 84) (b := 24518) rfl rfl ArealUCore.ArealUK.chunk_12258 s59
  have s57 : leavesOK ctxLitU 490625000000 2 ((leaves.drop 24514).take 86) 492775000000 2 = true :=
    take_step (n := 2) (t := 86) (b := 24516) rfl rfl ArealUCore.ArealUK.chunk_12257 s58
  have s56 : leavesOK ctxLitU 490575000000 2 ((leaves.drop 24512).take 88) 492775000000 2 = true :=
    take_step (n := 2) (t := 88) (b := 24514) rfl rfl ArealUCore.ArealUK.chunk_12256 s57
  have s55 : leavesOK ctxLitU 490525000000 2 ((leaves.drop 24510).take 90) 492775000000 2 = true :=
    take_step (n := 2) (t := 90) (b := 24512) rfl rfl ArealUCore.ArealUK.chunk_12255 s56
  have s54 : leavesOK ctxLitU 490475000000 2 ((leaves.drop 24508).take 92) 492775000000 2 = true :=
    take_step (n := 2) (t := 92) (b := 24510) rfl rfl ArealUCore.ArealUK.chunk_12254 s55
  have s53 : leavesOK ctxLitU 490425000000 2 ((leaves.drop 24506).take 94) 492775000000 2 = true :=
    take_step (n := 2) (t := 94) (b := 24508) rfl rfl ArealUCore.ArealUK.chunk_12253 s54
  have s52 : leavesOK ctxLitU 490375000000 2 ((leaves.drop 24504).take 96) 492775000000 2 = true :=
    take_step (n := 2) (t := 96) (b := 24506) rfl rfl ArealUCore.ArealUK.chunk_12252 s53
  have s51 : leavesOK ctxLitU 490325000000 2 ((leaves.drop 24502).take 98) 492775000000 2 = true :=
    take_step (n := 2) (t := 98) (b := 24504) rfl rfl ArealUCore.ArealUK.chunk_12251 s52
  have s50 : leavesOK ctxLitU 490275000000 2 ((leaves.drop 24500).take 100) 492775000000 2 = true :=
    take_step (n := 2) (t := 100) (b := 24502) rfl rfl ArealUCore.ArealUK.chunk_12250 s51
  have s49 : leavesOK ctxLitU 490225000000 2 ((leaves.drop 24498).take 102) 492775000000 2 = true :=
    take_step (n := 2) (t := 102) (b := 24500) rfl rfl ArealUCore.ArealUK.chunk_12249 s50
  have s48 : leavesOK ctxLitU 490175000000 2 ((leaves.drop 24496).take 104) 492775000000 2 = true :=
    take_step (n := 2) (t := 104) (b := 24498) rfl rfl ArealUCore.ArealUK.chunk_12248 s49
  have s47 : leavesOK ctxLitU 490125000000 2 ((leaves.drop 24494).take 106) 492775000000 2 = true :=
    take_step (n := 2) (t := 106) (b := 24496) rfl rfl ArealUCore.ArealUK.chunk_12247 s48
  have s46 : leavesOK ctxLitU 490075000000 2 ((leaves.drop 24492).take 108) 492775000000 2 = true :=
    take_step (n := 2) (t := 108) (b := 24494) rfl rfl ArealUCore.ArealUK.chunk_12246 s47
  have s45 : leavesOK ctxLitU 490025000000 2 ((leaves.drop 24490).take 110) 492775000000 2 = true :=
    take_step (n := 2) (t := 110) (b := 24492) rfl rfl ArealUCore.ArealUK.chunk_12245 s46
  have s44 : leavesOK ctxLitU 489975000000 2 ((leaves.drop 24488).take 112) 492775000000 2 = true :=
    take_step (n := 2) (t := 112) (b := 24490) rfl rfl ArealUCore.ArealUK.chunk_12244 s45
  have s43 : leavesOK ctxLitU 489925000000 2 ((leaves.drop 24486).take 114) 492775000000 2 = true :=
    take_step (n := 2) (t := 114) (b := 24488) rfl rfl ArealUCore.ArealUK.chunk_12243 s44
  have s42 : leavesOK ctxLitU 489875000000 2 ((leaves.drop 24484).take 116) 492775000000 2 = true :=
    take_step (n := 2) (t := 116) (b := 24486) rfl rfl ArealUCore.ArealUK.chunk_12242 s43
  have s41 : leavesOK ctxLitU 489825000000 2 ((leaves.drop 24482).take 118) 492775000000 2 = true :=
    take_step (n := 2) (t := 118) (b := 24484) rfl rfl ArealUCore.ArealUK.chunk_12241 s42
  have s40 : leavesOK ctxLitU 489775000000 2 ((leaves.drop 24480).take 120) 492775000000 2 = true :=
    take_step (n := 2) (t := 120) (b := 24482) rfl rfl ArealUCore.ArealUK.chunk_12240 s41
  have s39 : leavesOK ctxLitU 489725000000 2 ((leaves.drop 24478).take 122) 492775000000 2 = true :=
    take_step (n := 2) (t := 122) (b := 24480) rfl rfl ArealUCore.ArealUK.chunk_12239 s40
  have s38 : leavesOK ctxLitU 489675000000 2 ((leaves.drop 24476).take 124) 492775000000 2 = true :=
    take_step (n := 2) (t := 124) (b := 24478) rfl rfl ArealUCore.ArealUK.chunk_12238 s39
  have s37 : leavesOK ctxLitU 489625000000 2 ((leaves.drop 24474).take 126) 492775000000 2 = true :=
    take_step (n := 2) (t := 126) (b := 24476) rfl rfl ArealUCore.ArealUK.chunk_12237 s38
  have s36 : leavesOK ctxLitU 489575000000 2 ((leaves.drop 24472).take 128) 492775000000 2 = true :=
    take_step (n := 2) (t := 128) (b := 24474) rfl rfl ArealUCore.ArealUK.chunk_12236 s37
  have s35 : leavesOK ctxLitU 489525000000 2 ((leaves.drop 24470).take 130) 492775000000 2 = true :=
    take_step (n := 2) (t := 130) (b := 24472) rfl rfl ArealUCore.ArealUK.chunk_12235 s36
  have s34 : leavesOK ctxLitU 489475000000 2 ((leaves.drop 24468).take 132) 492775000000 2 = true :=
    take_step (n := 2) (t := 132) (b := 24470) rfl rfl ArealUCore.ArealUK.chunk_12234 s35
  have s33 : leavesOK ctxLitU 489425000000 2 ((leaves.drop 24466).take 134) 492775000000 2 = true :=
    take_step (n := 2) (t := 134) (b := 24468) rfl rfl ArealUCore.ArealUK.chunk_12233 s34
  have s32 : leavesOK ctxLitU 489375000000 2 ((leaves.drop 24464).take 136) 492775000000 2 = true :=
    take_step (n := 2) (t := 136) (b := 24466) rfl rfl ArealUCore.ArealUK.chunk_12232 s33
  have s31 : leavesOK ctxLitU 489325000000 2 ((leaves.drop 24462).take 138) 492775000000 2 = true :=
    take_step (n := 2) (t := 138) (b := 24464) rfl rfl ArealUCore.ArealUK.chunk_12231 s32
  have s30 : leavesOK ctxLitU 489275000000 2 ((leaves.drop 24460).take 140) 492775000000 2 = true :=
    take_step (n := 2) (t := 140) (b := 24462) rfl rfl ArealUCore.ArealUK.chunk_12230 s31
  have s29 : leavesOK ctxLitU 489225000000 2 ((leaves.drop 24458).take 142) 492775000000 2 = true :=
    take_step (n := 2) (t := 142) (b := 24460) rfl rfl ArealUCore.ArealUK.chunk_12229 s30
  have s28 : leavesOK ctxLitU 489175000000 2 ((leaves.drop 24456).take 144) 492775000000 2 = true :=
    take_step (n := 2) (t := 144) (b := 24458) rfl rfl ArealUCore.ArealUK.chunk_12228 s29
  have s27 : leavesOK ctxLitU 489125000000 2 ((leaves.drop 24454).take 146) 492775000000 2 = true :=
    take_step (n := 2) (t := 146) (b := 24456) rfl rfl ArealUCore.ArealUK.chunk_12227 s28
  have s26 : leavesOK ctxLitU 489075000000 2 ((leaves.drop 24452).take 148) 492775000000 2 = true :=
    take_step (n := 2) (t := 148) (b := 24454) rfl rfl ArealUCore.ArealUK.chunk_12226 s27
  have s25 : leavesOK ctxLitU 489025000000 2 ((leaves.drop 24450).take 150) 492775000000 2 = true :=
    take_step (n := 2) (t := 150) (b := 24452) rfl rfl ArealUCore.ArealUK.chunk_12225 s26
  have s24 : leavesOK ctxLitU 488975000000 2 ((leaves.drop 24448).take 152) 492775000000 2 = true :=
    take_step (n := 2) (t := 152) (b := 24450) rfl rfl ArealUCore.ArealUK.chunk_12224 s25
  have s23 : leavesOK ctxLitU 488925000000 2 ((leaves.drop 24446).take 154) 492775000000 2 = true :=
    take_step (n := 2) (t := 154) (b := 24448) rfl rfl ArealUCore.ArealUK.chunk_12223 s24
  have s22 : leavesOK ctxLitU 488875000000 2 ((leaves.drop 24444).take 156) 492775000000 2 = true :=
    take_step (n := 2) (t := 156) (b := 24446) rfl rfl ArealUCore.ArealUK.chunk_12222 s23
  have s21 : leavesOK ctxLitU 488825000000 2 ((leaves.drop 24442).take 158) 492775000000 2 = true :=
    take_step (n := 2) (t := 158) (b := 24444) rfl rfl ArealUCore.ArealUK.chunk_12221 s22
  have s20 : leavesOK ctxLitU 488775000000 2 ((leaves.drop 24440).take 160) 492775000000 2 = true :=
    take_step (n := 2) (t := 160) (b := 24442) rfl rfl ArealUCore.ArealUK.chunk_12220 s21
  have s19 : leavesOK ctxLitU 488725000000 2 ((leaves.drop 24438).take 162) 492775000000 2 = true :=
    take_step (n := 2) (t := 162) (b := 24440) rfl rfl ArealUCore.ArealUK.chunk_12219 s20
  have s18 : leavesOK ctxLitU 488675000000 2 ((leaves.drop 24436).take 164) 492775000000 2 = true :=
    take_step (n := 2) (t := 164) (b := 24438) rfl rfl ArealUCore.ArealUK.chunk_12218 s19
  have s17 : leavesOK ctxLitU 488625000000 2 ((leaves.drop 24434).take 166) 492775000000 2 = true :=
    take_step (n := 2) (t := 166) (b := 24436) rfl rfl ArealUCore.ArealUK.chunk_12217 s18
  have s16 : leavesOK ctxLitU 488575000000 2 ((leaves.drop 24432).take 168) 492775000000 2 = true :=
    take_step (n := 2) (t := 168) (b := 24434) rfl rfl ArealUCore.ArealUK.chunk_12216 s17
  have s15 : leavesOK ctxLitU 488525000000 2 ((leaves.drop 24430).take 170) 492775000000 2 = true :=
    take_step (n := 2) (t := 170) (b := 24432) rfl rfl ArealUCore.ArealUK.chunk_12215 s16
  have s14 : leavesOK ctxLitU 488475000000 2 ((leaves.drop 24428).take 172) 492775000000 2 = true :=
    take_step (n := 2) (t := 172) (b := 24430) rfl rfl ArealUCore.ArealUK.chunk_12214 s15
  have s13 : leavesOK ctxLitU 488425000000 2 ((leaves.drop 24426).take 174) 492775000000 2 = true :=
    take_step (n := 2) (t := 174) (b := 24428) rfl rfl ArealUCore.ArealUK.chunk_12213 s14
  have s12 : leavesOK ctxLitU 488375000000 2 ((leaves.drop 24424).take 176) 492775000000 2 = true :=
    take_step (n := 2) (t := 176) (b := 24426) rfl rfl ArealUCore.ArealUK.chunk_12212 s13
  have s11 : leavesOK ctxLitU 488325000000 2 ((leaves.drop 24422).take 178) 492775000000 2 = true :=
    take_step (n := 2) (t := 178) (b := 24424) rfl rfl ArealUCore.ArealUK.chunk_12211 s12
  have s10 : leavesOK ctxLitU 488275000000 2 ((leaves.drop 24420).take 180) 492775000000 2 = true :=
    take_step (n := 2) (t := 180) (b := 24422) rfl rfl ArealUCore.ArealUK.chunk_12210 s11
  have s9 : leavesOK ctxLitU 488225000000 2 ((leaves.drop 24418).take 182) 492775000000 2 = true :=
    take_step (n := 2) (t := 182) (b := 24420) rfl rfl ArealUCore.ArealUK.chunk_12209 s10
  have s8 : leavesOK ctxLitU 488175000000 2 ((leaves.drop 24416).take 184) 492775000000 2 = true :=
    take_step (n := 2) (t := 184) (b := 24418) rfl rfl ArealUCore.ArealUK.chunk_12208 s9
  have s7 : leavesOK ctxLitU 488125000000 2 ((leaves.drop 24414).take 186) 492775000000 2 = true :=
    take_step (n := 2) (t := 186) (b := 24416) rfl rfl ArealUCore.ArealUK.chunk_12207 s8
  have s6 : leavesOK ctxLitU 488075000000 2 ((leaves.drop 24412).take 188) 492775000000 2 = true :=
    take_step (n := 2) (t := 188) (b := 24414) rfl rfl ArealUCore.ArealUK.chunk_12206 s7
  have s5 : leavesOK ctxLitU 488025000000 2 ((leaves.drop 24410).take 190) 492775000000 2 = true :=
    take_step (n := 2) (t := 190) (b := 24412) rfl rfl ArealUCore.ArealUK.chunk_12205 s6
  have s4 : leavesOK ctxLitU 487975000000 2 ((leaves.drop 24408).take 192) 492775000000 2 = true :=
    take_step (n := 2) (t := 192) (b := 24410) rfl rfl ArealUCore.ArealUK.chunk_12204 s5
  have s3 : leavesOK ctxLitU 487925000000 2 ((leaves.drop 24406).take 194) 492775000000 2 = true :=
    take_step (n := 2) (t := 194) (b := 24408) rfl rfl ArealUCore.ArealUK.chunk_12203 s4
  have s2 : leavesOK ctxLitU 487875000000 2 ((leaves.drop 24404).take 196) 492775000000 2 = true :=
    take_step (n := 2) (t := 196) (b := 24406) rfl rfl ArealUCore.ArealUK.chunk_12202 s3
  have s1 : leavesOK ctxLitU 487825000000 2 ((leaves.drop 24402).take 198) 492775000000 2 = true :=
    take_step (n := 2) (t := 198) (b := 24404) rfl rfl ArealUCore.ArealUK.chunk_12201 s2
  have s0 : leavesOK ctxLitU 487775000000 2 ((leaves.drop 24400).take 200) 492775000000 2 = true :=
    take_step (n := 2) (t := 200) (b := 24402) rfl rfl ArealUCore.ArealUK.chunk_12200 s1
  exact s0

end Areal.UCert

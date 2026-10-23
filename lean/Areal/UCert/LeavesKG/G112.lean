import ArealUK.Chunk11200
import ArealUK.Chunk11201
import ArealUK.Chunk11202
import ArealUK.Chunk11203
import ArealUK.Chunk11204
import ArealUK.Chunk11205
import ArealUK.Chunk11206
import ArealUK.Chunk11207
import ArealUK.Chunk11208
import ArealUK.Chunk11209
import ArealUK.Chunk11210
import ArealUK.Chunk11211
import ArealUK.Chunk11212
import ArealUK.Chunk11213
import ArealUK.Chunk11214
import ArealUK.Chunk11215
import ArealUK.Chunk11216
import ArealUK.Chunk11217
import ArealUK.Chunk11218
import ArealUK.Chunk11219
import ArealUK.Chunk11220
import ArealUK.Chunk11221
import ArealUK.Chunk11222
import ArealUK.Chunk11223
import ArealUK.Chunk11224
import ArealUK.Chunk11225
import ArealUK.Chunk11226
import ArealUK.Chunk11227
import ArealUK.Chunk11228
import ArealUK.Chunk11229
import ArealUK.Chunk11230
import ArealUK.Chunk11231
import ArealUK.Chunk11232
import ArealUK.Chunk11233
import ArealUK.Chunk11234
import ArealUK.Chunk11235
import ArealUK.Chunk11236
import ArealUK.Chunk11237
import ArealUK.Chunk11238
import ArealUK.Chunk11239
import ArealUK.Chunk11240
import ArealUK.Chunk11241
import ArealUK.Chunk11242
import ArealUK.Chunk11243
import ArealUK.Chunk11244
import ArealUK.Chunk11245
import ArealUK.Chunk11246
import ArealUK.Chunk11247
import ArealUK.Chunk11248
import ArealUK.Chunk11249
import ArealUK.Chunk11250
import ArealUK.Chunk11251
import ArealUK.Chunk11252
import ArealUK.Chunk11253
import ArealUK.Chunk11254
import ArealUK.Chunk11255
import ArealUK.Chunk11256
import ArealUK.Chunk11257
import ArealUK.Chunk11258
import ArealUK.Chunk11259
import ArealUK.Chunk11260
import ArealUK.Chunk11261
import ArealUK.Chunk11262
import ArealUK.Chunk11263
import ArealUK.Chunk11264
import ArealUK.Chunk11265
import ArealUK.Chunk11266
import ArealUK.Chunk11267
import ArealUK.Chunk11268
import ArealUK.Chunk11269
import ArealUK.Chunk11270
import ArealUK.Chunk11271
import ArealUK.Chunk11272
import ArealUK.Chunk11273
import ArealUK.Chunk11274
import ArealUK.Chunk11275
import ArealUK.Chunk11276
import ArealUK.Chunk11277
import ArealUK.Chunk11278
import ArealUK.Chunk11279
import ArealUK.Chunk11280
import ArealUK.Chunk11281
import ArealUK.Chunk11282
import ArealUK.Chunk11283
import ArealUK.Chunk11284
import ArealUK.Chunk11285
import ArealUK.Chunk11286
import ArealUK.Chunk11287
import ArealUK.Chunk11288
import ArealUK.Chunk11289
import ArealUK.Chunk11290
import ArealUK.Chunk11291
import ArealUK.Chunk11292
import ArealUK.Chunk11293
import ArealUK.Chunk11294
import ArealUK.Chunk11295
import ArealUK.Chunk11296
import ArealUK.Chunk11297
import ArealUK.Chunk11298
import ArealUK.Chunk11299
import Areal.UCert.LeavesKGen

/-! Group 112 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_112 : leavesOK ctxLitU 417900000000 2 ((leaves.drop 22400).take 200) 422900000000 2 = true := by
  have s99 := ArealUCore.ArealUK.chunk_11299
  have s98 : leavesOK ctxLitU 422800000000 2 ((leaves.drop 22596).take 4) 422900000000 2 = true :=
    take_step (n := 2) (t := 4) (b := 22598) rfl rfl ArealUCore.ArealUK.chunk_11298 s99
  have s97 : leavesOK ctxLitU 422750000000 2 ((leaves.drop 22594).take 6) 422900000000 2 = true :=
    take_step (n := 2) (t := 6) (b := 22596) rfl rfl ArealUCore.ArealUK.chunk_11297 s98
  have s96 : leavesOK ctxLitU 422700000000 2 ((leaves.drop 22592).take 8) 422900000000 2 = true :=
    take_step (n := 2) (t := 8) (b := 22594) rfl rfl ArealUCore.ArealUK.chunk_11296 s97
  have s95 : leavesOK ctxLitU 422650000000 2 ((leaves.drop 22590).take 10) 422900000000 2 = true :=
    take_step (n := 2) (t := 10) (b := 22592) rfl rfl ArealUCore.ArealUK.chunk_11295 s96
  have s94 : leavesOK ctxLitU 422600000000 2 ((leaves.drop 22588).take 12) 422900000000 2 = true :=
    take_step (n := 2) (t := 12) (b := 22590) rfl rfl ArealUCore.ArealUK.chunk_11294 s95
  have s93 : leavesOK ctxLitU 422550000000 2 ((leaves.drop 22586).take 14) 422900000000 2 = true :=
    take_step (n := 2) (t := 14) (b := 22588) rfl rfl ArealUCore.ArealUK.chunk_11293 s94
  have s92 : leavesOK ctxLitU 422500000000 2 ((leaves.drop 22584).take 16) 422900000000 2 = true :=
    take_step (n := 2) (t := 16) (b := 22586) rfl rfl ArealUCore.ArealUK.chunk_11292 s93
  have s91 : leavesOK ctxLitU 422450000000 2 ((leaves.drop 22582).take 18) 422900000000 2 = true :=
    take_step (n := 2) (t := 18) (b := 22584) rfl rfl ArealUCore.ArealUK.chunk_11291 s92
  have s90 : leavesOK ctxLitU 422400000000 2 ((leaves.drop 22580).take 20) 422900000000 2 = true :=
    take_step (n := 2) (t := 20) (b := 22582) rfl rfl ArealUCore.ArealUK.chunk_11290 s91
  have s89 : leavesOK ctxLitU 422350000000 2 ((leaves.drop 22578).take 22) 422900000000 2 = true :=
    take_step (n := 2) (t := 22) (b := 22580) rfl rfl ArealUCore.ArealUK.chunk_11289 s90
  have s88 : leavesOK ctxLitU 422300000000 2 ((leaves.drop 22576).take 24) 422900000000 2 = true :=
    take_step (n := 2) (t := 24) (b := 22578) rfl rfl ArealUCore.ArealUK.chunk_11288 s89
  have s87 : leavesOK ctxLitU 422250000000 2 ((leaves.drop 22574).take 26) 422900000000 2 = true :=
    take_step (n := 2) (t := 26) (b := 22576) rfl rfl ArealUCore.ArealUK.chunk_11287 s88
  have s86 : leavesOK ctxLitU 422200000000 2 ((leaves.drop 22572).take 28) 422900000000 2 = true :=
    take_step (n := 2) (t := 28) (b := 22574) rfl rfl ArealUCore.ArealUK.chunk_11286 s87
  have s85 : leavesOK ctxLitU 422150000000 2 ((leaves.drop 22570).take 30) 422900000000 2 = true :=
    take_step (n := 2) (t := 30) (b := 22572) rfl rfl ArealUCore.ArealUK.chunk_11285 s86
  have s84 : leavesOK ctxLitU 422100000000 2 ((leaves.drop 22568).take 32) 422900000000 2 = true :=
    take_step (n := 2) (t := 32) (b := 22570) rfl rfl ArealUCore.ArealUK.chunk_11284 s85
  have s83 : leavesOK ctxLitU 422050000000 2 ((leaves.drop 22566).take 34) 422900000000 2 = true :=
    take_step (n := 2) (t := 34) (b := 22568) rfl rfl ArealUCore.ArealUK.chunk_11283 s84
  have s82 : leavesOK ctxLitU 422000000000 2 ((leaves.drop 22564).take 36) 422900000000 2 = true :=
    take_step (n := 2) (t := 36) (b := 22566) rfl rfl ArealUCore.ArealUK.chunk_11282 s83
  have s81 : leavesOK ctxLitU 421950000000 2 ((leaves.drop 22562).take 38) 422900000000 2 = true :=
    take_step (n := 2) (t := 38) (b := 22564) rfl rfl ArealUCore.ArealUK.chunk_11281 s82
  have s80 : leavesOK ctxLitU 421900000000 2 ((leaves.drop 22560).take 40) 422900000000 2 = true :=
    take_step (n := 2) (t := 40) (b := 22562) rfl rfl ArealUCore.ArealUK.chunk_11280 s81
  have s79 : leavesOK ctxLitU 421850000000 2 ((leaves.drop 22558).take 42) 422900000000 2 = true :=
    take_step (n := 2) (t := 42) (b := 22560) rfl rfl ArealUCore.ArealUK.chunk_11279 s80
  have s78 : leavesOK ctxLitU 421800000000 2 ((leaves.drop 22556).take 44) 422900000000 2 = true :=
    take_step (n := 2) (t := 44) (b := 22558) rfl rfl ArealUCore.ArealUK.chunk_11278 s79
  have s77 : leavesOK ctxLitU 421750000000 2 ((leaves.drop 22554).take 46) 422900000000 2 = true :=
    take_step (n := 2) (t := 46) (b := 22556) rfl rfl ArealUCore.ArealUK.chunk_11277 s78
  have s76 : leavesOK ctxLitU 421700000000 2 ((leaves.drop 22552).take 48) 422900000000 2 = true :=
    take_step (n := 2) (t := 48) (b := 22554) rfl rfl ArealUCore.ArealUK.chunk_11276 s77
  have s75 : leavesOK ctxLitU 421650000000 2 ((leaves.drop 22550).take 50) 422900000000 2 = true :=
    take_step (n := 2) (t := 50) (b := 22552) rfl rfl ArealUCore.ArealUK.chunk_11275 s76
  have s74 : leavesOK ctxLitU 421600000000 2 ((leaves.drop 22548).take 52) 422900000000 2 = true :=
    take_step (n := 2) (t := 52) (b := 22550) rfl rfl ArealUCore.ArealUK.chunk_11274 s75
  have s73 : leavesOK ctxLitU 421550000000 2 ((leaves.drop 22546).take 54) 422900000000 2 = true :=
    take_step (n := 2) (t := 54) (b := 22548) rfl rfl ArealUCore.ArealUK.chunk_11273 s74
  have s72 : leavesOK ctxLitU 421500000000 2 ((leaves.drop 22544).take 56) 422900000000 2 = true :=
    take_step (n := 2) (t := 56) (b := 22546) rfl rfl ArealUCore.ArealUK.chunk_11272 s73
  have s71 : leavesOK ctxLitU 421450000000 2 ((leaves.drop 22542).take 58) 422900000000 2 = true :=
    take_step (n := 2) (t := 58) (b := 22544) rfl rfl ArealUCore.ArealUK.chunk_11271 s72
  have s70 : leavesOK ctxLitU 421400000000 2 ((leaves.drop 22540).take 60) 422900000000 2 = true :=
    take_step (n := 2) (t := 60) (b := 22542) rfl rfl ArealUCore.ArealUK.chunk_11270 s71
  have s69 : leavesOK ctxLitU 421350000000 2 ((leaves.drop 22538).take 62) 422900000000 2 = true :=
    take_step (n := 2) (t := 62) (b := 22540) rfl rfl ArealUCore.ArealUK.chunk_11269 s70
  have s68 : leavesOK ctxLitU 421300000000 2 ((leaves.drop 22536).take 64) 422900000000 2 = true :=
    take_step (n := 2) (t := 64) (b := 22538) rfl rfl ArealUCore.ArealUK.chunk_11268 s69
  have s67 : leavesOK ctxLitU 421250000000 2 ((leaves.drop 22534).take 66) 422900000000 2 = true :=
    take_step (n := 2) (t := 66) (b := 22536) rfl rfl ArealUCore.ArealUK.chunk_11267 s68
  have s66 : leavesOK ctxLitU 421200000000 2 ((leaves.drop 22532).take 68) 422900000000 2 = true :=
    take_step (n := 2) (t := 68) (b := 22534) rfl rfl ArealUCore.ArealUK.chunk_11266 s67
  have s65 : leavesOK ctxLitU 421150000000 2 ((leaves.drop 22530).take 70) 422900000000 2 = true :=
    take_step (n := 2) (t := 70) (b := 22532) rfl rfl ArealUCore.ArealUK.chunk_11265 s66
  have s64 : leavesOK ctxLitU 421100000000 2 ((leaves.drop 22528).take 72) 422900000000 2 = true :=
    take_step (n := 2) (t := 72) (b := 22530) rfl rfl ArealUCore.ArealUK.chunk_11264 s65
  have s63 : leavesOK ctxLitU 421050000000 2 ((leaves.drop 22526).take 74) 422900000000 2 = true :=
    take_step (n := 2) (t := 74) (b := 22528) rfl rfl ArealUCore.ArealUK.chunk_11263 s64
  have s62 : leavesOK ctxLitU 421000000000 2 ((leaves.drop 22524).take 76) 422900000000 2 = true :=
    take_step (n := 2) (t := 76) (b := 22526) rfl rfl ArealUCore.ArealUK.chunk_11262 s63
  have s61 : leavesOK ctxLitU 420950000000 2 ((leaves.drop 22522).take 78) 422900000000 2 = true :=
    take_step (n := 2) (t := 78) (b := 22524) rfl rfl ArealUCore.ArealUK.chunk_11261 s62
  have s60 : leavesOK ctxLitU 420900000000 2 ((leaves.drop 22520).take 80) 422900000000 2 = true :=
    take_step (n := 2) (t := 80) (b := 22522) rfl rfl ArealUCore.ArealUK.chunk_11260 s61
  have s59 : leavesOK ctxLitU 420850000000 2 ((leaves.drop 22518).take 82) 422900000000 2 = true :=
    take_step (n := 2) (t := 82) (b := 22520) rfl rfl ArealUCore.ArealUK.chunk_11259 s60
  have s58 : leavesOK ctxLitU 420800000000 2 ((leaves.drop 22516).take 84) 422900000000 2 = true :=
    take_step (n := 2) (t := 84) (b := 22518) rfl rfl ArealUCore.ArealUK.chunk_11258 s59
  have s57 : leavesOK ctxLitU 420750000000 2 ((leaves.drop 22514).take 86) 422900000000 2 = true :=
    take_step (n := 2) (t := 86) (b := 22516) rfl rfl ArealUCore.ArealUK.chunk_11257 s58
  have s56 : leavesOK ctxLitU 420700000000 2 ((leaves.drop 22512).take 88) 422900000000 2 = true :=
    take_step (n := 2) (t := 88) (b := 22514) rfl rfl ArealUCore.ArealUK.chunk_11256 s57
  have s55 : leavesOK ctxLitU 420650000000 2 ((leaves.drop 22510).take 90) 422900000000 2 = true :=
    take_step (n := 2) (t := 90) (b := 22512) rfl rfl ArealUCore.ArealUK.chunk_11255 s56
  have s54 : leavesOK ctxLitU 420600000000 2 ((leaves.drop 22508).take 92) 422900000000 2 = true :=
    take_step (n := 2) (t := 92) (b := 22510) rfl rfl ArealUCore.ArealUK.chunk_11254 s55
  have s53 : leavesOK ctxLitU 420550000000 2 ((leaves.drop 22506).take 94) 422900000000 2 = true :=
    take_step (n := 2) (t := 94) (b := 22508) rfl rfl ArealUCore.ArealUK.chunk_11253 s54
  have s52 : leavesOK ctxLitU 420500000000 2 ((leaves.drop 22504).take 96) 422900000000 2 = true :=
    take_step (n := 2) (t := 96) (b := 22506) rfl rfl ArealUCore.ArealUK.chunk_11252 s53
  have s51 : leavesOK ctxLitU 420450000000 2 ((leaves.drop 22502).take 98) 422900000000 2 = true :=
    take_step (n := 2) (t := 98) (b := 22504) rfl rfl ArealUCore.ArealUK.chunk_11251 s52
  have s50 : leavesOK ctxLitU 420400000000 2 ((leaves.drop 22500).take 100) 422900000000 2 = true :=
    take_step (n := 2) (t := 100) (b := 22502) rfl rfl ArealUCore.ArealUK.chunk_11250 s51
  have s49 : leavesOK ctxLitU 420350000000 2 ((leaves.drop 22498).take 102) 422900000000 2 = true :=
    take_step (n := 2) (t := 102) (b := 22500) rfl rfl ArealUCore.ArealUK.chunk_11249 s50
  have s48 : leavesOK ctxLitU 420300000000 2 ((leaves.drop 22496).take 104) 422900000000 2 = true :=
    take_step (n := 2) (t := 104) (b := 22498) rfl rfl ArealUCore.ArealUK.chunk_11248 s49
  have s47 : leavesOK ctxLitU 420250000000 2 ((leaves.drop 22494).take 106) 422900000000 2 = true :=
    take_step (n := 2) (t := 106) (b := 22496) rfl rfl ArealUCore.ArealUK.chunk_11247 s48
  have s46 : leavesOK ctxLitU 420200000000 2 ((leaves.drop 22492).take 108) 422900000000 2 = true :=
    take_step (n := 2) (t := 108) (b := 22494) rfl rfl ArealUCore.ArealUK.chunk_11246 s47
  have s45 : leavesOK ctxLitU 420150000000 2 ((leaves.drop 22490).take 110) 422900000000 2 = true :=
    take_step (n := 2) (t := 110) (b := 22492) rfl rfl ArealUCore.ArealUK.chunk_11245 s46
  have s44 : leavesOK ctxLitU 420100000000 2 ((leaves.drop 22488).take 112) 422900000000 2 = true :=
    take_step (n := 2) (t := 112) (b := 22490) rfl rfl ArealUCore.ArealUK.chunk_11244 s45
  have s43 : leavesOK ctxLitU 420050000000 2 ((leaves.drop 22486).take 114) 422900000000 2 = true :=
    take_step (n := 2) (t := 114) (b := 22488) rfl rfl ArealUCore.ArealUK.chunk_11243 s44
  have s42 : leavesOK ctxLitU 420000000000 2 ((leaves.drop 22484).take 116) 422900000000 2 = true :=
    take_step (n := 2) (t := 116) (b := 22486) rfl rfl ArealUCore.ArealUK.chunk_11242 s43
  have s41 : leavesOK ctxLitU 419950000000 2 ((leaves.drop 22482).take 118) 422900000000 2 = true :=
    take_step (n := 2) (t := 118) (b := 22484) rfl rfl ArealUCore.ArealUK.chunk_11241 s42
  have s40 : leavesOK ctxLitU 419900000000 2 ((leaves.drop 22480).take 120) 422900000000 2 = true :=
    take_step (n := 2) (t := 120) (b := 22482) rfl rfl ArealUCore.ArealUK.chunk_11240 s41
  have s39 : leavesOK ctxLitU 419850000000 2 ((leaves.drop 22478).take 122) 422900000000 2 = true :=
    take_step (n := 2) (t := 122) (b := 22480) rfl rfl ArealUCore.ArealUK.chunk_11239 s40
  have s38 : leavesOK ctxLitU 419800000000 2 ((leaves.drop 22476).take 124) 422900000000 2 = true :=
    take_step (n := 2) (t := 124) (b := 22478) rfl rfl ArealUCore.ArealUK.chunk_11238 s39
  have s37 : leavesOK ctxLitU 419750000000 2 ((leaves.drop 22474).take 126) 422900000000 2 = true :=
    take_step (n := 2) (t := 126) (b := 22476) rfl rfl ArealUCore.ArealUK.chunk_11237 s38
  have s36 : leavesOK ctxLitU 419700000000 2 ((leaves.drop 22472).take 128) 422900000000 2 = true :=
    take_step (n := 2) (t := 128) (b := 22474) rfl rfl ArealUCore.ArealUK.chunk_11236 s37
  have s35 : leavesOK ctxLitU 419650000000 2 ((leaves.drop 22470).take 130) 422900000000 2 = true :=
    take_step (n := 2) (t := 130) (b := 22472) rfl rfl ArealUCore.ArealUK.chunk_11235 s36
  have s34 : leavesOK ctxLitU 419600000000 2 ((leaves.drop 22468).take 132) 422900000000 2 = true :=
    take_step (n := 2) (t := 132) (b := 22470) rfl rfl ArealUCore.ArealUK.chunk_11234 s35
  have s33 : leavesOK ctxLitU 419550000000 2 ((leaves.drop 22466).take 134) 422900000000 2 = true :=
    take_step (n := 2) (t := 134) (b := 22468) rfl rfl ArealUCore.ArealUK.chunk_11233 s34
  have s32 : leavesOK ctxLitU 419500000000 2 ((leaves.drop 22464).take 136) 422900000000 2 = true :=
    take_step (n := 2) (t := 136) (b := 22466) rfl rfl ArealUCore.ArealUK.chunk_11232 s33
  have s31 : leavesOK ctxLitU 419450000000 2 ((leaves.drop 22462).take 138) 422900000000 2 = true :=
    take_step (n := 2) (t := 138) (b := 22464) rfl rfl ArealUCore.ArealUK.chunk_11231 s32
  have s30 : leavesOK ctxLitU 419400000000 2 ((leaves.drop 22460).take 140) 422900000000 2 = true :=
    take_step (n := 2) (t := 140) (b := 22462) rfl rfl ArealUCore.ArealUK.chunk_11230 s31
  have s29 : leavesOK ctxLitU 419350000000 2 ((leaves.drop 22458).take 142) 422900000000 2 = true :=
    take_step (n := 2) (t := 142) (b := 22460) rfl rfl ArealUCore.ArealUK.chunk_11229 s30
  have s28 : leavesOK ctxLitU 419300000000 2 ((leaves.drop 22456).take 144) 422900000000 2 = true :=
    take_step (n := 2) (t := 144) (b := 22458) rfl rfl ArealUCore.ArealUK.chunk_11228 s29
  have s27 : leavesOK ctxLitU 419250000000 2 ((leaves.drop 22454).take 146) 422900000000 2 = true :=
    take_step (n := 2) (t := 146) (b := 22456) rfl rfl ArealUCore.ArealUK.chunk_11227 s28
  have s26 : leavesOK ctxLitU 419200000000 2 ((leaves.drop 22452).take 148) 422900000000 2 = true :=
    take_step (n := 2) (t := 148) (b := 22454) rfl rfl ArealUCore.ArealUK.chunk_11226 s27
  have s25 : leavesOK ctxLitU 419150000000 2 ((leaves.drop 22450).take 150) 422900000000 2 = true :=
    take_step (n := 2) (t := 150) (b := 22452) rfl rfl ArealUCore.ArealUK.chunk_11225 s26
  have s24 : leavesOK ctxLitU 419100000000 2 ((leaves.drop 22448).take 152) 422900000000 2 = true :=
    take_step (n := 2) (t := 152) (b := 22450) rfl rfl ArealUCore.ArealUK.chunk_11224 s25
  have s23 : leavesOK ctxLitU 419050000000 2 ((leaves.drop 22446).take 154) 422900000000 2 = true :=
    take_step (n := 2) (t := 154) (b := 22448) rfl rfl ArealUCore.ArealUK.chunk_11223 s24
  have s22 : leavesOK ctxLitU 419000000000 2 ((leaves.drop 22444).take 156) 422900000000 2 = true :=
    take_step (n := 2) (t := 156) (b := 22446) rfl rfl ArealUCore.ArealUK.chunk_11222 s23
  have s21 : leavesOK ctxLitU 418950000000 2 ((leaves.drop 22442).take 158) 422900000000 2 = true :=
    take_step (n := 2) (t := 158) (b := 22444) rfl rfl ArealUCore.ArealUK.chunk_11221 s22
  have s20 : leavesOK ctxLitU 418900000000 2 ((leaves.drop 22440).take 160) 422900000000 2 = true :=
    take_step (n := 2) (t := 160) (b := 22442) rfl rfl ArealUCore.ArealUK.chunk_11220 s21
  have s19 : leavesOK ctxLitU 418850000000 2 ((leaves.drop 22438).take 162) 422900000000 2 = true :=
    take_step (n := 2) (t := 162) (b := 22440) rfl rfl ArealUCore.ArealUK.chunk_11219 s20
  have s18 : leavesOK ctxLitU 418800000000 2 ((leaves.drop 22436).take 164) 422900000000 2 = true :=
    take_step (n := 2) (t := 164) (b := 22438) rfl rfl ArealUCore.ArealUK.chunk_11218 s19
  have s17 : leavesOK ctxLitU 418750000000 2 ((leaves.drop 22434).take 166) 422900000000 2 = true :=
    take_step (n := 2) (t := 166) (b := 22436) rfl rfl ArealUCore.ArealUK.chunk_11217 s18
  have s16 : leavesOK ctxLitU 418700000000 2 ((leaves.drop 22432).take 168) 422900000000 2 = true :=
    take_step (n := 2) (t := 168) (b := 22434) rfl rfl ArealUCore.ArealUK.chunk_11216 s17
  have s15 : leavesOK ctxLitU 418650000000 2 ((leaves.drop 22430).take 170) 422900000000 2 = true :=
    take_step (n := 2) (t := 170) (b := 22432) rfl rfl ArealUCore.ArealUK.chunk_11215 s16
  have s14 : leavesOK ctxLitU 418600000000 2 ((leaves.drop 22428).take 172) 422900000000 2 = true :=
    take_step (n := 2) (t := 172) (b := 22430) rfl rfl ArealUCore.ArealUK.chunk_11214 s15
  have s13 : leavesOK ctxLitU 418550000000 2 ((leaves.drop 22426).take 174) 422900000000 2 = true :=
    take_step (n := 2) (t := 174) (b := 22428) rfl rfl ArealUCore.ArealUK.chunk_11213 s14
  have s12 : leavesOK ctxLitU 418500000000 2 ((leaves.drop 22424).take 176) 422900000000 2 = true :=
    take_step (n := 2) (t := 176) (b := 22426) rfl rfl ArealUCore.ArealUK.chunk_11212 s13
  have s11 : leavesOK ctxLitU 418450000000 2 ((leaves.drop 22422).take 178) 422900000000 2 = true :=
    take_step (n := 2) (t := 178) (b := 22424) rfl rfl ArealUCore.ArealUK.chunk_11211 s12
  have s10 : leavesOK ctxLitU 418400000000 2 ((leaves.drop 22420).take 180) 422900000000 2 = true :=
    take_step (n := 2) (t := 180) (b := 22422) rfl rfl ArealUCore.ArealUK.chunk_11210 s11
  have s9 : leavesOK ctxLitU 418350000000 2 ((leaves.drop 22418).take 182) 422900000000 2 = true :=
    take_step (n := 2) (t := 182) (b := 22420) rfl rfl ArealUCore.ArealUK.chunk_11209 s10
  have s8 : leavesOK ctxLitU 418300000000 2 ((leaves.drop 22416).take 184) 422900000000 2 = true :=
    take_step (n := 2) (t := 184) (b := 22418) rfl rfl ArealUCore.ArealUK.chunk_11208 s9
  have s7 : leavesOK ctxLitU 418250000000 2 ((leaves.drop 22414).take 186) 422900000000 2 = true :=
    take_step (n := 2) (t := 186) (b := 22416) rfl rfl ArealUCore.ArealUK.chunk_11207 s8
  have s6 : leavesOK ctxLitU 418200000000 2 ((leaves.drop 22412).take 188) 422900000000 2 = true :=
    take_step (n := 2) (t := 188) (b := 22414) rfl rfl ArealUCore.ArealUK.chunk_11206 s7
  have s5 : leavesOK ctxLitU 418150000000 2 ((leaves.drop 22410).take 190) 422900000000 2 = true :=
    take_step (n := 2) (t := 190) (b := 22412) rfl rfl ArealUCore.ArealUK.chunk_11205 s6
  have s4 : leavesOK ctxLitU 418100000000 2 ((leaves.drop 22408).take 192) 422900000000 2 = true :=
    take_step (n := 2) (t := 192) (b := 22410) rfl rfl ArealUCore.ArealUK.chunk_11204 s5
  have s3 : leavesOK ctxLitU 418050000000 2 ((leaves.drop 22406).take 194) 422900000000 2 = true :=
    take_step (n := 2) (t := 194) (b := 22408) rfl rfl ArealUCore.ArealUK.chunk_11203 s4
  have s2 : leavesOK ctxLitU 418000000000 2 ((leaves.drop 22404).take 196) 422900000000 2 = true :=
    take_step (n := 2) (t := 196) (b := 22406) rfl rfl ArealUCore.ArealUK.chunk_11202 s3
  have s1 : leavesOK ctxLitU 417950000000 2 ((leaves.drop 22402).take 198) 422900000000 2 = true :=
    take_step (n := 2) (t := 198) (b := 22404) rfl rfl ArealUCore.ArealUK.chunk_11201 s2
  have s0 : leavesOK ctxLitU 417900000000 2 ((leaves.drop 22400).take 200) 422900000000 2 = true :=
    take_step (n := 2) (t := 200) (b := 22402) rfl rfl ArealUCore.ArealUK.chunk_11200 s1
  exact s0

end Areal.UCert

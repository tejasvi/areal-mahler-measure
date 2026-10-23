import ArealUK.Chunk10200
import ArealUK.Chunk10201
import ArealUK.Chunk10202
import ArealUK.Chunk10203
import ArealUK.Chunk10204
import ArealUK.Chunk10205
import ArealUK.Chunk10206
import ArealUK.Chunk10207
import ArealUK.Chunk10208
import ArealUK.Chunk10209
import ArealUK.Chunk10210
import ArealUK.Chunk10211
import ArealUK.Chunk10212
import ArealUK.Chunk10213
import ArealUK.Chunk10214
import ArealUK.Chunk10215
import ArealUK.Chunk10216
import ArealUK.Chunk10217
import ArealUK.Chunk10218
import ArealUK.Chunk10219
import ArealUK.Chunk10220
import ArealUK.Chunk10221
import ArealUK.Chunk10222
import ArealUK.Chunk10223
import ArealUK.Chunk10224
import ArealUK.Chunk10225
import ArealUK.Chunk10226
import ArealUK.Chunk10227
import ArealUK.Chunk10228
import ArealUK.Chunk10229
import ArealUK.Chunk10230
import ArealUK.Chunk10231
import ArealUK.Chunk10232
import ArealUK.Chunk10233
import ArealUK.Chunk10234
import ArealUK.Chunk10235
import ArealUK.Chunk10236
import ArealUK.Chunk10237
import ArealUK.Chunk10238
import ArealUK.Chunk10239
import ArealUK.Chunk10240
import ArealUK.Chunk10241
import ArealUK.Chunk10242
import ArealUK.Chunk10243
import ArealUK.Chunk10244
import ArealUK.Chunk10245
import ArealUK.Chunk10246
import ArealUK.Chunk10247
import ArealUK.Chunk10248
import ArealUK.Chunk10249
import ArealUK.Chunk10250
import ArealUK.Chunk10251
import ArealUK.Chunk10252
import ArealUK.Chunk10253
import ArealUK.Chunk10254
import ArealUK.Chunk10255
import ArealUK.Chunk10256
import ArealUK.Chunk10257
import ArealUK.Chunk10258
import ArealUK.Chunk10259
import ArealUK.Chunk10260
import ArealUK.Chunk10261
import ArealUK.Chunk10262
import ArealUK.Chunk10263
import ArealUK.Chunk10264
import ArealUK.Chunk10265
import ArealUK.Chunk10266
import ArealUK.Chunk10267
import ArealUK.Chunk10268
import ArealUK.Chunk10269
import ArealUK.Chunk10270
import ArealUK.Chunk10271
import ArealUK.Chunk10272
import ArealUK.Chunk10273
import ArealUK.Chunk10274
import ArealUK.Chunk10275
import ArealUK.Chunk10276
import ArealUK.Chunk10277
import ArealUK.Chunk10278
import ArealUK.Chunk10279
import ArealUK.Chunk10280
import ArealUK.Chunk10281
import ArealUK.Chunk10282
import ArealUK.Chunk10283
import ArealUK.Chunk10284
import ArealUK.Chunk10285
import ArealUK.Chunk10286
import ArealUK.Chunk10287
import ArealUK.Chunk10288
import ArealUK.Chunk10289
import ArealUK.Chunk10290
import ArealUK.Chunk10291
import ArealUK.Chunk10292
import ArealUK.Chunk10293
import ArealUK.Chunk10294
import ArealUK.Chunk10295
import ArealUK.Chunk10296
import ArealUK.Chunk10297
import ArealUK.Chunk10298
import ArealUK.Chunk10299
import Areal.UCert.LeavesKGen

/-! Group 102 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_102 : leavesOK ctxLitU 367175000000 2 ((leaves.drop 20400).take 200) 372150000000 2 = true := by
  have s99 := ArealUCore.ArealUK.chunk_10299
  have s98 : leavesOK ctxLitU 372050000000 2 ((leaves.drop 20596).take 4) 372150000000 2 = true :=
    take_step (n := 2) (t := 4) (b := 20598) rfl rfl ArealUCore.ArealUK.chunk_10298 s99
  have s97 : leavesOK ctxLitU 372000000000 2 ((leaves.drop 20594).take 6) 372150000000 2 = true :=
    take_step (n := 2) (t := 6) (b := 20596) rfl rfl ArealUCore.ArealUK.chunk_10297 s98
  have s96 : leavesOK ctxLitU 371950000000 2 ((leaves.drop 20592).take 8) 372150000000 2 = true :=
    take_step (n := 2) (t := 8) (b := 20594) rfl rfl ArealUCore.ArealUK.chunk_10296 s97
  have s95 : leavesOK ctxLitU 371900000000 2 ((leaves.drop 20590).take 10) 372150000000 2 = true :=
    take_step (n := 2) (t := 10) (b := 20592) rfl rfl ArealUCore.ArealUK.chunk_10295 s96
  have s94 : leavesOK ctxLitU 371850000000 2 ((leaves.drop 20588).take 12) 372150000000 2 = true :=
    take_step (n := 2) (t := 12) (b := 20590) rfl rfl ArealUCore.ArealUK.chunk_10294 s95
  have s93 : leavesOK ctxLitU 371800000000 2 ((leaves.drop 20586).take 14) 372150000000 2 = true :=
    take_step (n := 2) (t := 14) (b := 20588) rfl rfl ArealUCore.ArealUK.chunk_10293 s94
  have s92 : leavesOK ctxLitU 371750000000 2 ((leaves.drop 20584).take 16) 372150000000 2 = true :=
    take_step (n := 2) (t := 16) (b := 20586) rfl rfl ArealUCore.ArealUK.chunk_10292 s93
  have s91 : leavesOK ctxLitU 371700000000 2 ((leaves.drop 20582).take 18) 372150000000 2 = true :=
    take_step (n := 2) (t := 18) (b := 20584) rfl rfl ArealUCore.ArealUK.chunk_10291 s92
  have s90 : leavesOK ctxLitU 371650000000 2 ((leaves.drop 20580).take 20) 372150000000 2 = true :=
    take_step (n := 2) (t := 20) (b := 20582) rfl rfl ArealUCore.ArealUK.chunk_10290 s91
  have s89 : leavesOK ctxLitU 371600000000 2 ((leaves.drop 20578).take 22) 372150000000 2 = true :=
    take_step (n := 2) (t := 22) (b := 20580) rfl rfl ArealUCore.ArealUK.chunk_10289 s90
  have s88 : leavesOK ctxLitU 371550000000 2 ((leaves.drop 20576).take 24) 372150000000 2 = true :=
    take_step (n := 2) (t := 24) (b := 20578) rfl rfl ArealUCore.ArealUK.chunk_10288 s89
  have s87 : leavesOK ctxLitU 371500000000 2 ((leaves.drop 20574).take 26) 372150000000 2 = true :=
    take_step (n := 2) (t := 26) (b := 20576) rfl rfl ArealUCore.ArealUK.chunk_10287 s88
  have s86 : leavesOK ctxLitU 371450000000 2 ((leaves.drop 20572).take 28) 372150000000 2 = true :=
    take_step (n := 2) (t := 28) (b := 20574) rfl rfl ArealUCore.ArealUK.chunk_10286 s87
  have s85 : leavesOK ctxLitU 371400000000 2 ((leaves.drop 20570).take 30) 372150000000 2 = true :=
    take_step (n := 2) (t := 30) (b := 20572) rfl rfl ArealUCore.ArealUK.chunk_10285 s86
  have s84 : leavesOK ctxLitU 371350000000 2 ((leaves.drop 20568).take 32) 372150000000 2 = true :=
    take_step (n := 2) (t := 32) (b := 20570) rfl rfl ArealUCore.ArealUK.chunk_10284 s85
  have s83 : leavesOK ctxLitU 371300000000 2 ((leaves.drop 20566).take 34) 372150000000 2 = true :=
    take_step (n := 2) (t := 34) (b := 20568) rfl rfl ArealUCore.ArealUK.chunk_10283 s84
  have s82 : leavesOK ctxLitU 371250000000 2 ((leaves.drop 20564).take 36) 372150000000 2 = true :=
    take_step (n := 2) (t := 36) (b := 20566) rfl rfl ArealUCore.ArealUK.chunk_10282 s83
  have s81 : leavesOK ctxLitU 371200000000 2 ((leaves.drop 20562).take 38) 372150000000 2 = true :=
    take_step (n := 2) (t := 38) (b := 20564) rfl rfl ArealUCore.ArealUK.chunk_10281 s82
  have s80 : leavesOK ctxLitU 371150000000 2 ((leaves.drop 20560).take 40) 372150000000 2 = true :=
    take_step (n := 2) (t := 40) (b := 20562) rfl rfl ArealUCore.ArealUK.chunk_10280 s81
  have s79 : leavesOK ctxLitU 371100000000 2 ((leaves.drop 20558).take 42) 372150000000 2 = true :=
    take_step (n := 2) (t := 42) (b := 20560) rfl rfl ArealUCore.ArealUK.chunk_10279 s80
  have s78 : leavesOK ctxLitU 371050000000 2 ((leaves.drop 20556).take 44) 372150000000 2 = true :=
    take_step (n := 2) (t := 44) (b := 20558) rfl rfl ArealUCore.ArealUK.chunk_10278 s79
  have s77 : leavesOK ctxLitU 371000000000 2 ((leaves.drop 20554).take 46) 372150000000 2 = true :=
    take_step (n := 2) (t := 46) (b := 20556) rfl rfl ArealUCore.ArealUK.chunk_10277 s78
  have s76 : leavesOK ctxLitU 370950000000 2 ((leaves.drop 20552).take 48) 372150000000 2 = true :=
    take_step (n := 2) (t := 48) (b := 20554) rfl rfl ArealUCore.ArealUK.chunk_10276 s77
  have s75 : leavesOK ctxLitU 370900000000 2 ((leaves.drop 20550).take 50) 372150000000 2 = true :=
    take_step (n := 2) (t := 50) (b := 20552) rfl rfl ArealUCore.ArealUK.chunk_10275 s76
  have s74 : leavesOK ctxLitU 370850000000 2 ((leaves.drop 20548).take 52) 372150000000 2 = true :=
    take_step (n := 2) (t := 52) (b := 20550) rfl rfl ArealUCore.ArealUK.chunk_10274 s75
  have s73 : leavesOK ctxLitU 370800000000 2 ((leaves.drop 20546).take 54) 372150000000 2 = true :=
    take_step (n := 2) (t := 54) (b := 20548) rfl rfl ArealUCore.ArealUK.chunk_10273 s74
  have s72 : leavesOK ctxLitU 370750000000 2 ((leaves.drop 20544).take 56) 372150000000 2 = true :=
    take_step (n := 2) (t := 56) (b := 20546) rfl rfl ArealUCore.ArealUK.chunk_10272 s73
  have s71 : leavesOK ctxLitU 370700000000 2 ((leaves.drop 20542).take 58) 372150000000 2 = true :=
    take_step (n := 2) (t := 58) (b := 20544) rfl rfl ArealUCore.ArealUK.chunk_10271 s72
  have s70 : leavesOK ctxLitU 370650000000 2 ((leaves.drop 20540).take 60) 372150000000 2 = true :=
    take_step (n := 2) (t := 60) (b := 20542) rfl rfl ArealUCore.ArealUK.chunk_10270 s71
  have s69 : leavesOK ctxLitU 370600000000 2 ((leaves.drop 20538).take 62) 372150000000 2 = true :=
    take_step (n := 2) (t := 62) (b := 20540) rfl rfl ArealUCore.ArealUK.chunk_10269 s70
  have s68 : leavesOK ctxLitU 370550000000 2 ((leaves.drop 20536).take 64) 372150000000 2 = true :=
    take_step (n := 2) (t := 64) (b := 20538) rfl rfl ArealUCore.ArealUK.chunk_10268 s69
  have s67 : leavesOK ctxLitU 370500000000 2 ((leaves.drop 20534).take 66) 372150000000 2 = true :=
    take_step (n := 2) (t := 66) (b := 20536) rfl rfl ArealUCore.ArealUK.chunk_10267 s68
  have s66 : leavesOK ctxLitU 370450000000 2 ((leaves.drop 20532).take 68) 372150000000 2 = true :=
    take_step (n := 2) (t := 68) (b := 20534) rfl rfl ArealUCore.ArealUK.chunk_10266 s67
  have s65 : leavesOK ctxLitU 370400000000 2 ((leaves.drop 20530).take 70) 372150000000 2 = true :=
    take_step (n := 2) (t := 70) (b := 20532) rfl rfl ArealUCore.ArealUK.chunk_10265 s66
  have s64 : leavesOK ctxLitU 370350000000 2 ((leaves.drop 20528).take 72) 372150000000 2 = true :=
    take_step (n := 2) (t := 72) (b := 20530) rfl rfl ArealUCore.ArealUK.chunk_10264 s65
  have s63 : leavesOK ctxLitU 370300000000 2 ((leaves.drop 20526).take 74) 372150000000 2 = true :=
    take_step (n := 2) (t := 74) (b := 20528) rfl rfl ArealUCore.ArealUK.chunk_10263 s64
  have s62 : leavesOK ctxLitU 370250000000 2 ((leaves.drop 20524).take 76) 372150000000 2 = true :=
    take_step (n := 2) (t := 76) (b := 20526) rfl rfl ArealUCore.ArealUK.chunk_10262 s63
  have s61 : leavesOK ctxLitU 370200000000 2 ((leaves.drop 20522).take 78) 372150000000 2 = true :=
    take_step (n := 2) (t := 78) (b := 20524) rfl rfl ArealUCore.ArealUK.chunk_10261 s62
  have s60 : leavesOK ctxLitU 370150000000 2 ((leaves.drop 20520).take 80) 372150000000 2 = true :=
    take_step (n := 2) (t := 80) (b := 20522) rfl rfl ArealUCore.ArealUK.chunk_10260 s61
  have s59 : leavesOK ctxLitU 370100000000 2 ((leaves.drop 20518).take 82) 372150000000 2 = true :=
    take_step (n := 2) (t := 82) (b := 20520) rfl rfl ArealUCore.ArealUK.chunk_10259 s60
  have s58 : leavesOK ctxLitU 370050000000 2 ((leaves.drop 20516).take 84) 372150000000 2 = true :=
    take_step (n := 2) (t := 84) (b := 20518) rfl rfl ArealUCore.ArealUK.chunk_10258 s59
  have s57 : leavesOK ctxLitU 370000000000 2 ((leaves.drop 20514).take 86) 372150000000 2 = true :=
    take_step (n := 2) (t := 86) (b := 20516) rfl rfl ArealUCore.ArealUK.chunk_10257 s58
  have s56 : leavesOK ctxLitU 369950000000 2 ((leaves.drop 20512).take 88) 372150000000 2 = true :=
    take_step (n := 2) (t := 88) (b := 20514) rfl rfl ArealUCore.ArealUK.chunk_10256 s57
  have s55 : leavesOK ctxLitU 369900000000 2 ((leaves.drop 20510).take 90) 372150000000 2 = true :=
    take_step (n := 2) (t := 90) (b := 20512) rfl rfl ArealUCore.ArealUK.chunk_10255 s56
  have s54 : leavesOK ctxLitU 369850000000 2 ((leaves.drop 20508).take 92) 372150000000 2 = true :=
    take_step (n := 2) (t := 92) (b := 20510) rfl rfl ArealUCore.ArealUK.chunk_10254 s55
  have s53 : leavesOK ctxLitU 369800000000 2 ((leaves.drop 20506).take 94) 372150000000 2 = true :=
    take_step (n := 2) (t := 94) (b := 20508) rfl rfl ArealUCore.ArealUK.chunk_10253 s54
  have s52 : leavesOK ctxLitU 369750000000 2 ((leaves.drop 20504).take 96) 372150000000 2 = true :=
    take_step (n := 2) (t := 96) (b := 20506) rfl rfl ArealUCore.ArealUK.chunk_10252 s53
  have s51 : leavesOK ctxLitU 369700000000 2 ((leaves.drop 20502).take 98) 372150000000 2 = true :=
    take_step (n := 2) (t := 98) (b := 20504) rfl rfl ArealUCore.ArealUK.chunk_10251 s52
  have s50 : leavesOK ctxLitU 369650000000 2 ((leaves.drop 20500).take 100) 372150000000 2 = true :=
    take_step (n := 2) (t := 100) (b := 20502) rfl rfl ArealUCore.ArealUK.chunk_10250 s51
  have s49 : leavesOK ctxLitU 369600000000 2 ((leaves.drop 20498).take 102) 372150000000 2 = true :=
    take_step (n := 2) (t := 102) (b := 20500) rfl rfl ArealUCore.ArealUK.chunk_10249 s50
  have s48 : leavesOK ctxLitU 369550000000 2 ((leaves.drop 20496).take 104) 372150000000 2 = true :=
    take_step (n := 2) (t := 104) (b := 20498) rfl rfl ArealUCore.ArealUK.chunk_10248 s49
  have s47 : leavesOK ctxLitU 369500000000 2 ((leaves.drop 20494).take 106) 372150000000 2 = true :=
    take_step (n := 2) (t := 106) (b := 20496) rfl rfl ArealUCore.ArealUK.chunk_10247 s48
  have s46 : leavesOK ctxLitU 369450000000 2 ((leaves.drop 20492).take 108) 372150000000 2 = true :=
    take_step (n := 2) (t := 108) (b := 20494) rfl rfl ArealUCore.ArealUK.chunk_10246 s47
  have s45 : leavesOK ctxLitU 369400000000 2 ((leaves.drop 20490).take 110) 372150000000 2 = true :=
    take_step (n := 2) (t := 110) (b := 20492) rfl rfl ArealUCore.ArealUK.chunk_10245 s46
  have s44 : leavesOK ctxLitU 369350000000 2 ((leaves.drop 20488).take 112) 372150000000 2 = true :=
    take_step (n := 2) (t := 112) (b := 20490) rfl rfl ArealUCore.ArealUK.chunk_10244 s45
  have s43 : leavesOK ctxLitU 369300000000 2 ((leaves.drop 20486).take 114) 372150000000 2 = true :=
    take_step (n := 2) (t := 114) (b := 20488) rfl rfl ArealUCore.ArealUK.chunk_10243 s44
  have s42 : leavesOK ctxLitU 369250000000 2 ((leaves.drop 20484).take 116) 372150000000 2 = true :=
    take_step (n := 2) (t := 116) (b := 20486) rfl rfl ArealUCore.ArealUK.chunk_10242 s43
  have s41 : leavesOK ctxLitU 369200000000 2 ((leaves.drop 20482).take 118) 372150000000 2 = true :=
    take_step (n := 2) (t := 118) (b := 20484) rfl rfl ArealUCore.ArealUK.chunk_10241 s42
  have s40 : leavesOK ctxLitU 369150000000 2 ((leaves.drop 20480).take 120) 372150000000 2 = true :=
    take_step (n := 2) (t := 120) (b := 20482) rfl rfl ArealUCore.ArealUK.chunk_10240 s41
  have s39 : leavesOK ctxLitU 369100000000 2 ((leaves.drop 20478).take 122) 372150000000 2 = true :=
    take_step (n := 2) (t := 122) (b := 20480) rfl rfl ArealUCore.ArealUK.chunk_10239 s40
  have s38 : leavesOK ctxLitU 369050000000 2 ((leaves.drop 20476).take 124) 372150000000 2 = true :=
    take_step (n := 2) (t := 124) (b := 20478) rfl rfl ArealUCore.ArealUK.chunk_10238 s39
  have s37 : leavesOK ctxLitU 369000000000 2 ((leaves.drop 20474).take 126) 372150000000 2 = true :=
    take_step (n := 2) (t := 126) (b := 20476) rfl rfl ArealUCore.ArealUK.chunk_10237 s38
  have s36 : leavesOK ctxLitU 368950000000 2 ((leaves.drop 20472).take 128) 372150000000 2 = true :=
    take_step (n := 2) (t := 128) (b := 20474) rfl rfl ArealUCore.ArealUK.chunk_10236 s37
  have s35 : leavesOK ctxLitU 368900000000 2 ((leaves.drop 20470).take 130) 372150000000 2 = true :=
    take_step (n := 2) (t := 130) (b := 20472) rfl rfl ArealUCore.ArealUK.chunk_10235 s36
  have s34 : leavesOK ctxLitU 368850000000 2 ((leaves.drop 20468).take 132) 372150000000 2 = true :=
    take_step (n := 2) (t := 132) (b := 20470) rfl rfl ArealUCore.ArealUK.chunk_10234 s35
  have s33 : leavesOK ctxLitU 368800000000 2 ((leaves.drop 20466).take 134) 372150000000 2 = true :=
    take_step (n := 2) (t := 134) (b := 20468) rfl rfl ArealUCore.ArealUK.chunk_10233 s34
  have s32 : leavesOK ctxLitU 368750000000 2 ((leaves.drop 20464).take 136) 372150000000 2 = true :=
    take_step (n := 2) (t := 136) (b := 20466) rfl rfl ArealUCore.ArealUK.chunk_10232 s33
  have s31 : leavesOK ctxLitU 368700000000 2 ((leaves.drop 20462).take 138) 372150000000 2 = true :=
    take_step (n := 2) (t := 138) (b := 20464) rfl rfl ArealUCore.ArealUK.chunk_10231 s32
  have s30 : leavesOK ctxLitU 368650000000 2 ((leaves.drop 20460).take 140) 372150000000 2 = true :=
    take_step (n := 2) (t := 140) (b := 20462) rfl rfl ArealUCore.ArealUK.chunk_10230 s31
  have s29 : leavesOK ctxLitU 368600000000 2 ((leaves.drop 20458).take 142) 372150000000 2 = true :=
    take_step (n := 2) (t := 142) (b := 20460) rfl rfl ArealUCore.ArealUK.chunk_10229 s30
  have s28 : leavesOK ctxLitU 368550000000 2 ((leaves.drop 20456).take 144) 372150000000 2 = true :=
    take_step (n := 2) (t := 144) (b := 20458) rfl rfl ArealUCore.ArealUK.chunk_10228 s29
  have s27 : leavesOK ctxLitU 368500000000 2 ((leaves.drop 20454).take 146) 372150000000 2 = true :=
    take_step (n := 2) (t := 146) (b := 20456) rfl rfl ArealUCore.ArealUK.chunk_10227 s28
  have s26 : leavesOK ctxLitU 368450000000 2 ((leaves.drop 20452).take 148) 372150000000 2 = true :=
    take_step (n := 2) (t := 148) (b := 20454) rfl rfl ArealUCore.ArealUK.chunk_10226 s27
  have s25 : leavesOK ctxLitU 368400000000 2 ((leaves.drop 20450).take 150) 372150000000 2 = true :=
    take_step (n := 2) (t := 150) (b := 20452) rfl rfl ArealUCore.ArealUK.chunk_10225 s26
  have s24 : leavesOK ctxLitU 368350000000 2 ((leaves.drop 20448).take 152) 372150000000 2 = true :=
    take_step (n := 2) (t := 152) (b := 20450) rfl rfl ArealUCore.ArealUK.chunk_10224 s25
  have s23 : leavesOK ctxLitU 368300000000 2 ((leaves.drop 20446).take 154) 372150000000 2 = true :=
    take_step (n := 2) (t := 154) (b := 20448) rfl rfl ArealUCore.ArealUK.chunk_10223 s24
  have s22 : leavesOK ctxLitU 368250000000 2 ((leaves.drop 20444).take 156) 372150000000 2 = true :=
    take_step (n := 2) (t := 156) (b := 20446) rfl rfl ArealUCore.ArealUK.chunk_10222 s23
  have s21 : leavesOK ctxLitU 368200000000 2 ((leaves.drop 20442).take 158) 372150000000 2 = true :=
    take_step (n := 2) (t := 158) (b := 20444) rfl rfl ArealUCore.ArealUK.chunk_10221 s22
  have s20 : leavesOK ctxLitU 753973877606012 13 ((leaves.drop 20440).take 160) 372150000000 2 = true :=
    take_step (n := 2) (t := 160) (b := 20442) rfl rfl ArealUCore.ArealUK.chunk_10220 s21
  have s19 : leavesOK ctxLitU 753921338803003 13 ((leaves.drop 20438).take 162) 372150000000 2 = true :=
    take_step (n := 2) (t := 162) (b := 20440) rfl rfl ArealUCore.ArealUK.chunk_10219 s20
  have s18 : leavesOK ctxLitU 368075000000 2 ((leaves.drop 20436).take 164) 372150000000 2 = true :=
    take_step (n := 2) (t := 164) (b := 20438) rfl rfl ArealUCore.ArealUK.chunk_10218 s19
  have s17 : leavesOK ctxLitU 368025000000 2 ((leaves.drop 20434).take 166) 372150000000 2 = true :=
    take_step (n := 2) (t := 166) (b := 20436) rfl rfl ArealUCore.ArealUK.chunk_10217 s18
  have s16 : leavesOK ctxLitU 367975000000 2 ((leaves.drop 20432).take 168) 372150000000 2 = true :=
    take_step (n := 2) (t := 168) (b := 20434) rfl rfl ArealUCore.ArealUK.chunk_10216 s17
  have s15 : leavesOK ctxLitU 367925000000 2 ((leaves.drop 20430).take 170) 372150000000 2 = true :=
    take_step (n := 2) (t := 170) (b := 20432) rfl rfl ArealUCore.ArealUK.chunk_10215 s16
  have s14 : leavesOK ctxLitU 367875000000 2 ((leaves.drop 20428).take 172) 372150000000 2 = true :=
    take_step (n := 2) (t := 172) (b := 20430) rfl rfl ArealUCore.ArealUK.chunk_10214 s15
  have s13 : leavesOK ctxLitU 367825000000 2 ((leaves.drop 20426).take 174) 372150000000 2 = true :=
    take_step (n := 2) (t := 174) (b := 20428) rfl rfl ArealUCore.ArealUK.chunk_10213 s14
  have s12 : leavesOK ctxLitU 367775000000 2 ((leaves.drop 20424).take 176) 372150000000 2 = true :=
    take_step (n := 2) (t := 176) (b := 20426) rfl rfl ArealUCore.ArealUK.chunk_10212 s13
  have s11 : leavesOK ctxLitU 367725000000 2 ((leaves.drop 20422).take 178) 372150000000 2 = true :=
    take_step (n := 2) (t := 178) (b := 20424) rfl rfl ArealUCore.ArealUK.chunk_10211 s12
  have s10 : leavesOK ctxLitU 367675000000 2 ((leaves.drop 20420).take 180) 372150000000 2 = true :=
    take_step (n := 2) (t := 180) (b := 20422) rfl rfl ArealUCore.ArealUK.chunk_10210 s11
  have s9 : leavesOK ctxLitU 367625000000 2 ((leaves.drop 20418).take 182) 372150000000 2 = true :=
    take_step (n := 2) (t := 182) (b := 20420) rfl rfl ArealUCore.ArealUK.chunk_10209 s10
  have s8 : leavesOK ctxLitU 367575000000 2 ((leaves.drop 20416).take 184) 372150000000 2 = true :=
    take_step (n := 2) (t := 184) (b := 20418) rfl rfl ArealUCore.ArealUK.chunk_10208 s9
  have s7 : leavesOK ctxLitU 367525000000 2 ((leaves.drop 20414).take 186) 372150000000 2 = true :=
    take_step (n := 2) (t := 186) (b := 20416) rfl rfl ArealUCore.ArealUK.chunk_10207 s8
  have s6 : leavesOK ctxLitU 367475000000 2 ((leaves.drop 20412).take 188) 372150000000 2 = true :=
    take_step (n := 2) (t := 188) (b := 20414) rfl rfl ArealUCore.ArealUK.chunk_10206 s7
  have s5 : leavesOK ctxLitU 367425000000 2 ((leaves.drop 20410).take 190) 372150000000 2 = true :=
    take_step (n := 2) (t := 190) (b := 20412) rfl rfl ArealUCore.ArealUK.chunk_10205 s6
  have s4 : leavesOK ctxLitU 367375000000 2 ((leaves.drop 20408).take 192) 372150000000 2 = true :=
    take_step (n := 2) (t := 192) (b := 20410) rfl rfl ArealUCore.ArealUK.chunk_10204 s5
  have s3 : leavesOK ctxLitU 367325000000 2 ((leaves.drop 20406).take 194) 372150000000 2 = true :=
    take_step (n := 2) (t := 194) (b := 20408) rfl rfl ArealUCore.ArealUK.chunk_10203 s4
  have s2 : leavesOK ctxLitU 367275000000 2 ((leaves.drop 20404).take 196) 372150000000 2 = true :=
    take_step (n := 2) (t := 196) (b := 20406) rfl rfl ArealUCore.ArealUK.chunk_10202 s3
  have s1 : leavesOK ctxLitU 367225000000 2 ((leaves.drop 20402).take 198) 372150000000 2 = true :=
    take_step (n := 2) (t := 198) (b := 20404) rfl rfl ArealUCore.ArealUK.chunk_10201 s2
  have s0 : leavesOK ctxLitU 367175000000 2 ((leaves.drop 20400).take 200) 372150000000 2 = true :=
    take_step (n := 2) (t := 200) (b := 20402) rfl rfl ArealUCore.ArealUK.chunk_10200 s1
  exact s0

end Areal.UCert

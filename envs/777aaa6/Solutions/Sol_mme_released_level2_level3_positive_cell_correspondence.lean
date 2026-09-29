-- Prove2me | solution 1 for mme_released_level2_level3_positive_cell_correspondence
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T20:38:23.211594+00:00
-- url     : https://prove2.me/submissions/8de7d3e0-9968-49b9-88f7-1ec078c1b700

import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_released_joint_interior_profiles
import Definitions.Def_mme_recursive_region_parent_profiles
open BigOperators MME MME.RecursiveYZ MME.RegionRealization
set_option autoImplicit false
set_option maxRecDepth 100000

namespace C9Corr

def phiTab : List (List ℕ) :=
  [[6, 2207, 4406, 6607, 8811, 11011, 31, 32, 4431, 4436, 6632, 6636, 56, 57, 4456, 4461, 6657, 6661, 2232, 2231, 8836, 8831, 11036, 11032, 81, 82, 2257, 2256, 4481, 4486, 8861, 8856],
   [11061, 11057, 107, 2281, 4511, 6686, 8881, 11082, 131, 136, 2307, 2311, 4531, 4532, 156, 157, 161, 2332, 2331, 2336, 4556, 4561, 4557, 6707, 6711, 6706, 4581, 4586, 4582, 6732, 6736, 6731],
   [8911, 8906, 8907, 11111, 11107, 11106, 181, 182, 186, 2357, 2356, 2361, 4606, 4611, 4607, 6757, 6761, 6756, 8936, 8931, 8932, 11136, 11132, 11131, 207, 211, 2381, 2386, 6786, 6781, 8956, 8957],
   [11157, 11156, 231, 236, 2407, 2411, 4631, 4632, 256, 257, 261, 2432, 2431, 2436, 8986, 8981, 8982, 11186, 11182, 11181, 281, 282, 286, 2457, 2456, 2461, 4656, 4661, 4657, 6807, 6811, 6806],
   [307, 311, 2481, 2486, 9006, 9007, 6832, 6831, 9036, 9032, 11211, 11206, 331, 332, 336, 2507, 2506, 2511, 4681, 4686, 4682, 9061, 9056, 9057, 4711, 4707, 6861, 6856, 11232, 11231, 356, 361],
   [4731, 4732, 6882, 6881, 9086, 9082, 11261, 11256, 2531, 2536, 4761, 4757, 6911, 6906, 9106, 9107, 11282, 11281, 386, 2561, 4782, 6931, 9132, 11306, 406, 2582, 4806, 6957, 9161, 11336, 431, 432],
   [2607, 2606, 4831, 4836, 6982, 6986, 9186, 9181, 456, 457, 4856, 4861, 7007, 7011, 2632, 2631, 9211, 9206, 11361, 11357, 2657, 2656, 9236, 9231, 11386, 11382, 482, 2681, 4886, 7036, 9256, 11407],
   [506, 511, 2707, 2711, 4906, 4907, 7057, 7056, 11436, 11431, 531, 532, 536, 2732, 2731, 2736, 4931, 4936, 4932, 7082, 7086, 7081, 9286, 9281, 9282, 11461, 11457, 11456, 4956, 4961, 4957, 7107],
   [7111, 7106, 9311, 9306, 9307, 11486, 11482, 11481, 556, 557, 561, 2757, 2756, 2761, 9336, 9331, 9332, 11511, 11507, 11506, 582, 586, 2781, 2786, 9356, 9357, 606, 611, 2807, 2811, 4981, 4982],
   [631, 632, 636, 2832, 2831, 2836, 9386, 9381, 9382, 11536, 11532, 11531, 656, 657, 661, 2857, 2856, 2861, 5006, 5011, 5007, 7132, 7136, 7131, 682, 686, 2881, 2886, 9406, 9407, 7157, 7156],
   [9436, 9432, 11561, 11556, 706, 707, 711, 2907, 2906, 2911, 5031, 5036, 5032, 9461, 9456, 9457, 5061, 5057, 7186, 7181, 11582, 11581, 731, 736, 5081, 5082, 7207, 7206, 9486, 9482, 11611, 11606],
   [2931, 2936, 5111, 5107, 7236, 7231, 9506, 9507, 11632, 11631, 761, 2961, 5132, 7256, 9532, 11656, 781, 2982, 5156, 7282, 9561, 11686, 806, 807, 5181, 5186, 7307, 7311, 831, 832, 5206, 5211],
   [7332, 7336, 3007, 3006, 9586, 9581, 11711, 11707, 856, 857, 3032, 3031, 5231, 5236, 9611, 9606, 11736, 11732, 882, 3056, 5261, 7361, 9631, 11757, 906, 911, 3082, 3086, 5281, 5282, 931, 932],
   [936, 3107, 3106, 3111, 5306, 5311, 5307, 7382, 7386, 7381, 5331, 5336, 5332, 7407, 7411, 7406, 9661, 9656, 9657, 11786, 11782, 11781, 956, 957, 961, 5356, 5361, 5357, 7432, 7436, 7431, 11811],
   [11807, 11806, 982, 986, 3131, 3136, 7461, 7456, 9681, 9682, 11832, 11831, 1006, 1011, 3157, 3161, 5381, 5382, 1031, 1032, 1036, 3182, 3181, 3186, 9711, 9706, 9707, 11861, 11857, 11856, 1056, 1057],
   [1061, 3207, 3206, 3211, 5406, 5411, 5407, 7482, 7486, 7481, 1082, 1086, 3231, 3236, 9731, 9732, 7507, 7506, 9761, 9757, 11886, 11881, 1106, 1107, 1111, 3257, 3256, 3261, 5431, 5436, 5432, 7532],
   [7536, 7531, 9786, 9781, 9782, 11911, 11907, 11906, 5461, 5457, 7561, 7556, 11932, 11931, 1131, 1136, 5481, 5482, 7582, 7581, 9811, 9807, 11961, 11956, 3281, 3286, 5511, 5507, 7611, 7606, 9831, 9832],
   [11982, 11981, 1161, 3311, 5532, 7631, 9857, 12006, 1181, 3332, 5556, 7657, 9886, 12036, 1206, 1207, 3357, 3356, 5581, 5586, 7682, 7686, 9911, 9906, 1231, 1232, 5606, 5611, 7707, 7711, 3382, 3381],
   [9936, 9931, 12061, 12057, 1256, 1257, 3407, 3406, 5631, 5636, 9961, 9956, 12086, 12082, 1282, 3431, 5661, 7736, 9981, 12107, 1306, 1311, 3457, 3461, 5681, 5682, 7757, 7756, 12136, 12131, 1331, 1332],
   [1336, 3482, 3481, 3486, 5706, 5711, 5707, 7782, 7786, 7781, 10011, 10006, 10007, 12161, 12157, 12156, 5731, 5736, 5732, 7807, 7811, 7806, 10036, 10031, 10032, 12186, 12182, 12181, 1356, 1357, 1361, 5756],
   [5761, 5757, 7832, 7836, 7831, 12211, 12207, 12206, 1382, 1386, 3506, 3511, 7861, 7856, 10056, 10057, 12232, 12231, 1406, 1411, 3532, 3536, 5781, 5782, 1431, 1432, 1436, 3557, 3556, 3561, 10086, 10081],
   [10082, 12261, 12257, 12256, 1456, 1457, 1461, 3582, 3581, 3586, 5806, 5811, 5807, 7882, 7886, 7881, 1482, 1486, 3606, 3611, 10106, 10107, 7907, 7906, 10136, 10132, 12286, 12281, 5831, 5836, 5832, 7932],
   [7936, 7931, 10161, 10156, 10157, 12311, 12307, 12306, 5861, 5857, 7961, 7956, 12332, 12331, 7982, 7981, 10186, 10182, 12361, 12356, 5886, 5882, 8011, 8006, 12382, 12381, 1511, 3636, 5907, 8031, 10207, 12406],
   [1531, 3657, 5931, 8057, 10236, 12436, 1556, 1557, 3682, 3681, 5956, 5961, 8082, 8086, 10261, 10256, 1581, 1582, 5981, 5986, 8107, 8111, 3707, 3706, 10286, 10281, 12461, 12457, 3732, 3731, 10311, 10306],
   [12486, 12482, 1607, 3756, 6011, 8136, 10331, 12507, 1631, 1636, 3782, 3786, 6031, 6032, 8157, 8156, 12536, 12531, 3807, 3806, 3811, 8182, 8186, 8181, 10361, 10356, 10357, 12561, 12557, 12556, 6056, 6061],
   [6057, 8207, 8211, 8206, 10386, 10381, 10382, 12586, 12582, 12581, 1656, 1657, 1661, 3832, 3831, 3836, 10411, 10406, 10407, 12611, 12607, 12606, 1682, 1686, 3856, 3861, 10431, 10432, 1706, 1711, 3882, 3886],
   [6081, 6082, 1731, 1732, 1736, 3907, 3906, 3911, 10461, 10456, 10457, 12636, 12632, 12631, 1756, 1757, 1761, 3932, 3931, 3936, 6106, 6111, 6107, 8232, 8236, 8231, 1782, 1786, 3956, 3961, 10481, 10482],
   [8257, 8256, 10511, 10507, 12661, 12656, 1806, 1807, 1811, 3982, 3981, 3986, 6131, 6136, 6132, 8282, 8286, 8281, 10536, 10531, 10532, 12686, 12682, 12681, 6161, 6157, 8311, 8306, 12707, 12706, 1831, 1836],
   [6181, 6182, 8332, 8331, 10561, 10557, 12736, 12731, 4006, 4011, 6211, 6207, 8361, 8356, 10581, 10582, 12757, 12756, 1861, 4036, 6232, 8381, 10607, 12781, 1881, 4057, 6256, 8407, 10636, 12811, 1906, 1907],
   [4082, 4081, 6281, 6286, 8432, 8436, 10661, 10656, 1931, 1932, 6306, 6311, 8457, 8461, 4107, 4106, 10686, 10681, 12836, 12832, 1956, 1957, 4132, 4131, 6331, 6336, 10711, 10706, 12861, 12857, 1982, 4156],
   [6361, 8486, 10731, 12882, 2006, 2011, 4182, 4186, 6381, 6382, 8507, 8506, 12911, 12906, 4207, 4206, 4211, 8532, 8536, 8531, 10761, 10756, 10757, 12936, 12932, 12931, 6406, 6411, 6407, 8557, 8561, 8556],
   [10786, 10781, 10782, 12961, 12957, 12956, 2031, 2032, 2036, 4232, 4231, 4236, 6431, 6436, 6432, 8582, 8586, 8581, 10811, 10806, 10807, 12986, 12982, 12981, 2057, 2061, 4256, 4261, 8611, 8606, 10831, 10832],
   [13007, 13006, 2081, 2086, 4282, 4286, 6456, 6457, 2106, 2107, 2111, 4307, 4306, 4311, 10861, 10856, 10857, 13036, 13032, 13031, 2131, 2132, 2136, 4332, 4331, 4336, 6481, 6486, 6482, 8632, 8636, 8631],
   [2157, 2161, 4356, 4361, 10881, 10882, 8657, 8656, 10911, 10907, 13061, 13056, 6506, 6511, 6507, 8682, 8686, 8681, 10936, 10931, 10932, 13086, 13082, 13081, 6536, 6532, 8711, 8706, 13107, 13106, 8732, 8731],
   [10961, 10957, 13136, 13131, 6561, 6557, 8761, 8756, 13157, 13156, 2186, 4386, 6582, 8781, 10982, 13181]]

def phiCode (r : Fin 1104) : ℕ := (phiTab.getD (r.val / 32) []).getD (r.val % 32) 0

def mkSplit (P : Fin 3 → ℕ) (hP : P 0 + P 1 + P 2 = 2 * (2 * 2 ^ (2 - 1))) (a b : ℕ) :
    RecursiveThinSplit.Split (2 * 2 ^ (2 - 1)) P :=
  if h : a ≤ 4 ∧ b + a ≤ 4 ∧ a ≤ P 0 ∧ b ≤ P 1 ∧ 4 - a - b ≤ P 2 then
    ⟨![⟨a, by norm_num <;> omega⟩, ⟨b, by norm_num <;> omega⟩, ⟨4 - a - b, by norm_num <;> omega⟩],
      by
        refine ⟨?_, fun i ↦ ?_⟩
        · simp <;> omega
        · fin_cases i <;> simp <;> omega⟩
  else
    ⟨![⟨min (P 0) 4, by norm_num <;> omega⟩, ⟨min (P 1) (4 - min (P 0) 4), by norm_num <;> omega⟩,
      ⟨4 - min (P 0) 4 - min (P 1) (4 - min (P 0) 4), by norm_num <;> omega⟩],
      by
        norm_num at hP
        refine ⟨?_, fun i ↦ ?_⟩
        · simp <;> omega
        · fin_cases i <;> simp <;> omega⟩

def phiOf (code : ℕ) : (ρ : Fin 6) × Cell (2 * 2 ^ (2 - 1)) 88 (RecStage.parent3 ρ) :=
  ⟨⟨code / 2200 % 6, Nat.mod_lt _ (by norm_num)⟩,
    ⟨code / 25 % 88, Nat.mod_lt _ (by norm_num)⟩,
    mkSplit _ (RecStage.htotal3 _ _) (code / 5 % 5) (code % 5)⟩

def phi (r2 : Fin 1104) : (ρ : Fin 6) × Cell (2 * 2 ^ (2 - 1)) 88 (RecStage.parent3 ρ) :=
  phiOf (phiCode r2)

inductive KT where
  | leaf : KT
  | node : KT → ℕ → ℕ → KT → KT

def KT.find : KT → ℕ → Option ℕ
  | .leaf, _ => none
  | .node l k v r, x => if x < k then l.find x else if k < x then r.find x else some v

def ktree : KT := (.node (.node (.node (.node (.node (.node (.node (.node (.node (.node (.node .leaf 6 0 .leaf) 31 6 .leaf) 32 7 (.node .leaf 56 12 .leaf)) 57 13 (.node (.node .leaf 81 24 .leaf) 82 25 (.node .leaf 107 34 .leaf))) 131 40 (.node (.node (.node (.node .leaf 136 41 .leaf) 156 46 .leaf) 157 47 (.node .leaf 161 48 .leaf)) 181 70 (.node (.node .leaf 182 71 .leaf) 186 72 (.node .leaf 207 88 .leaf)))) 211 89 (.node (.node (.node (.node (.node .leaf 231 98 .leaf) 236 99 .leaf) 256 104 (.node .leaf 257 105 .leaf)) 261 106 (.node (.node .leaf 281 116 .leaf) 282 117 (.node .leaf 286 118 .leaf))) 307 128 (.node (.node (.node .leaf 311 129 .leaf) 331 140 (.node .leaf 332 141 .leaf)) 336 142 (.node (.node .leaf 356 158 .leaf) 361 159 (.node .leaf 386 178 .leaf))))) 406 184 (.node (.node (.node (.node (.node (.node .leaf 431 190 .leaf) 432 191 .leaf) 456 200 (.node .leaf 457 201 .leaf)) 482 218 (.node (.node .leaf 506 224 .leaf) 511 225 (.node .leaf 531 234 .leaf))) 532 235 (.node (.node (.node (.node .leaf 536 236 .leaf) 556 264 .leaf) 557 265 (.node .leaf 561 266 .leaf)) 582 276 (.node (.node .leaf 586 277 .leaf) 606 282 (.node .leaf 611 283 .leaf)))) 631 288 (.node (.node (.node (.node (.node .leaf 632 289 .leaf) 636 290 .leaf) 656 300 (.node .leaf 657 301 .leaf)) 661 302 (.node (.node .leaf 682 312 .leaf) 686 313 (.node .leaf 706 324 .leaf))) 707 325 (.node (.node (.node .leaf 711 326 .leaf) 731 342 (.node .leaf 736 343 .leaf)) 761 362 (.node (.node .leaf 781 368 .leaf) 806 374 (.node .leaf 807 375 .leaf)))))) 831 380 (.node (.node (.node (.node (.node (.node (.node .leaf 832 381 .leaf) 856 392 .leaf) 857 393 (.node .leaf 882 402 .leaf)) 906 408 (.node (.node .leaf 911 409 .leaf) 931 414 (.node .leaf 932 415 .leaf))) 936 416 (.node (.node (.node (.node .leaf 956 438 .leaf) 957 439 .leaf) 961 440 (.node .leaf 982 450 .leaf)) 986 451 (.node (.node .leaf 1006 460 .leaf) 1011 461 (.node .leaf 1031 466 .leaf)))) 1032 467 (.node (.node (.node (.node (.node .leaf 1036 468 .leaf) 1056 478 .leaf) 1057 479 (.node .leaf 1061 480 .leaf)) 1082 490 (.node (.node .leaf 1086 491 .leaf) 1106 502 (.node .leaf 1107 503 .leaf))) 1111 504 (.node (.node (.node .leaf 1131 526 .leaf) 1136 527 (.node .leaf 1161 546 .leaf)) 1181 552 (.node (.node .leaf 1206 558 .leaf) 1207 559 (.node .leaf 1231 568 .leaf))))) 1232 569 (.node (.node (.node (.node (.node (.node .leaf 1256 580 .leaf) 1257 581 .leaf) 1282 590 (.node .leaf 1306 596 .leaf)) 1311 597 (.node (.node .leaf 1331 606 .leaf) 1332 607 (.node .leaf 1336 608 .leaf))) 1356 636 (.node (.node (.node .leaf 1357 637 .leaf) 1361 638 (.node .leaf 1382 648 .leaf)) 1386 649 (.node (.node .leaf 1406 658 .leaf) 1411 659 (.node .leaf 1431 664 .leaf)))) 1432 665 (.node (.node (.node (.node (.node .leaf 1436 666 .leaf) 1456 676 .leaf) 1457 677 (.node .leaf 1461 678 .leaf)) 1482 688 (.node (.node .leaf 1486 689 .leaf) 1511 730 (.node .leaf 1531 736 .leaf))) 1556 742 (.node (.node (.node .leaf 1557 743 .leaf) 1581 752 (.node .leaf 1582 753 .leaf)) 1607 770 (.node (.node .leaf 1631 776 .leaf) 1636 777 (.node .leaf 1656 810 .leaf))))))) 1657 811 (.node (.node (.node (.node (.node (.node (.node (.node .leaf 1661 812 .leaf) 1682 822 .leaf) 1686 823 (.node .leaf 1706 828 .leaf)) 1711 829 (.node (.node .leaf 1731 834 .leaf) 1732 835 (.node .leaf 1736 836 .leaf))) 1756 846 (.node (.node (.node (.node .leaf 1757 847 .leaf) 1761 848 .leaf) 1782 858 (.node .leaf 1786 859 .leaf)) 1806 870 (.node (.node .leaf 1807 871 .leaf) 1811 872 (.node .leaf 1831 894 .leaf)))) 1836 895 (.node (.node (.node (.node (.node .leaf 1861 914 .leaf) 1881 920 .leaf) 1906 926 (.node .leaf 1907 927 .leaf)) 1931 936 (.node (.node .leaf 1932 937 .leaf) 1956 948 (.node .leaf 1957 949 .leaf))) 1982 958 (.node (.node (.node .leaf 2006 964 .leaf) 2011 965 (.node .leaf 2031 998 .leaf)) 2032 999 (.node (.node .leaf 2036 1000 .leaf) 2057 1016 (.node .leaf 2061 1017 .leaf))))) 2081 1026 (.node (.node (.node (.node (.node (.node .leaf 2086 1027 .leaf) 2106 1032 .leaf) 2107 1033 (.node .leaf 2111 1034 .leaf)) 2131 1044 (.node (.node .leaf 2132 1045 .leaf) 2136 1046 (.node .leaf 2157 1056 .leaf))) 2161 1057 (.node (.node (.node .leaf 2186 1098 .leaf) 2207 1 (.node .leaf 2231 19 .leaf)) 2232 18 (.node (.node .leaf 2256 27 .leaf) 2257 26 (.node .leaf 2281 35 .leaf)))) 2307 42 (.node (.node (.node (.node (.node .leaf 2311 43 .leaf) 2331 50 .leaf) 2332 49 (.node .leaf 2336 51 .leaf)) 2356 74 (.node (.node .leaf 2357 73 .leaf) 2361 75 (.node .leaf 2381 90 .leaf))) 2386 91 (.node (.node (.node .leaf 2407 100 .leaf) 2411 101 (.node .leaf 2431 108 .leaf)) 2432 107 (.node (.node .leaf 2436 109 .leaf) 2456 120 (.node .leaf 2457 119 .leaf)))))) 2461 121 (.node (.node (.node (.node (.node (.node (.node .leaf 2481 130 .leaf) 2486 131 .leaf) 2506 144 (.node .leaf 2507 143 .leaf)) 2511 145 (.node (.node .leaf 2531 168 .leaf) 2536 169 (.node .leaf 2561 179 .leaf))) 2582 185 (.node (.node (.node (.node .leaf 2606 193 .leaf) 2607 192 .leaf) 2631 207 (.node .leaf 2632 206 .leaf)) 2656 213 (.node (.node .leaf 2657 212 .leaf) 2681 219 (.node .leaf 2707 226 .leaf)))) 2711 227 (.node (.node (.node (.node (.node .leaf 2731 238 .leaf) 2732 237 .leaf) 2736 239 (.node .leaf 2756 268 .leaf)) 2757 267 (.node (.node .leaf 2761 269 .leaf) 2781 278 (.node .leaf 2786 279 .leaf))) 2807 284 (.node (.node (.node .leaf 2811 285 .leaf) 2831 292 (.node .leaf 2832 291 .leaf)) 2836 293 (.node (.node .leaf 2856 304 .leaf) 2857 303 (.node .leaf 2861 305 .leaf))))) 2881 314 (.node (.node (.node (.node (.node (.node .leaf 2886 315 .leaf) 2906 328 .leaf) 2907 327 (.node .leaf 2911 329 .leaf)) 2931 352 (.node (.node .leaf 2936 353 .leaf) 2961 363 (.node .leaf 2982 369 .leaf))) 3006 387 (.node (.node (.node .leaf 3007 386 .leaf) 3031 395 (.node .leaf 3032 394 .leaf)) 3056 403 (.node (.node .leaf 3082 410 .leaf) 3086 411 (.node .leaf 3106 418 .leaf)))) 3107 417 (.node (.node (.node (.node (.node .leaf 3111 419 .leaf) 3131 452 .leaf) 3136 453 (.node .leaf 3157 462 .leaf)) 3161 463 (.node (.node .leaf 3181 470 .leaf) 3182 469 (.node .leaf 3186 471 .leaf))) 3206 482 (.node (.node (.node .leaf 3207 481 .leaf) 3211 483 (.node .leaf 3231 492 .leaf)) 3236 493 (.node (.node .leaf 3256 506 .leaf) 3257 505 (.node .leaf 3261 507 .leaf)))))))) 3281 536 (.node (.node (.node (.node (.node (.node (.node (.node (.node .leaf 3286 537 .leaf) 3311 547 .leaf) 3332 553 (.node .leaf 3356 561 .leaf)) 3357 560 (.node (.node .leaf 3381 575 .leaf) 3382 574 (.node .leaf 3406 583 .leaf))) 3407 582 (.node (.node (.node (.node .leaf 3431 591 .leaf) 3457 598 .leaf) 3461 599 (.node .leaf 3481 610 .leaf)) 3482 609 (.node (.node .leaf 3486 611 .leaf) 3506 650 (.node .leaf 3511 651 .leaf)))) 3532 660 (.node (.node (.node (.node (.node .leaf 3536 661 .leaf) 3556 668 .leaf) 3557 667 (.node .leaf 3561 669 .leaf)) 3581 680 (.node (.node .leaf 3582 679 .leaf) 3586 681 (.node .leaf 3606 690 .leaf))) 3611 691 (.node (.node (.node .leaf 3636 731 .leaf) 3657 737 (.node .leaf 3681 745 .leaf)) 3682 744 (.node (.node .leaf 3706 759 .leaf) 3707 758 (.node .leaf 3731 765 .leaf))))) 3732 764 (.node (.node (.node (.node (.node (.node .leaf 3756 771 .leaf) 3782 778 .leaf) 3786 779 (.node .leaf 3806 787 .leaf)) 3807 786 (.node (.node .leaf 3811 788 .leaf) 3831 814 (.node .leaf 3832 813 .leaf))) 3836 815 (.node (.node (.node .leaf 3856 824 .leaf) 3861 825 (.node .leaf 3882 830 .leaf)) 3886 831 (.node (.node .leaf 3906 838 .leaf) 3907 837 (.node .leaf 3911 839 .leaf)))) 3931 850 (.node (.node (.node (.node (.node .leaf 3932 849 .leaf) 3936 851 .leaf) 3956 860 (.node .leaf 3961 861 .leaf)) 3981 874 (.node (.node .leaf 3982 873 .leaf) 3986 875 (.node .leaf 4006 904 .leaf))) 4011 905 (.node (.node (.node .leaf 4036 915 .leaf) 4057 921 (.node .leaf 4081 929 .leaf)) 4082 928 (.node (.node .leaf 4106 943 .leaf) 4107 942 (.node .leaf 4131 951 .leaf)))))) 4132 950 (.node (.node (.node (.node (.node (.node (.node .leaf 4156 959 .leaf) 4182 966 .leaf) 4186 967 (.node .leaf 4206 975 .leaf)) 4207 974 (.node (.node .leaf 4211 976 .leaf) 4231 1002 (.node .leaf 4232 1001 .leaf))) 4236 1003 (.node (.node (.node (.node .leaf 4256 1018 .leaf) 4261 1019 .leaf) 4282 1028 (.node .leaf 4286 1029 .leaf)) 4306 1036 (.node (.node .leaf 4307 1035 .leaf) 4311 1037 (.node .leaf 4331 1048 .leaf)))) 4332 1047 (.node (.node (.node (.node (.node .leaf 4336 1049 .leaf) 4356 1058 .leaf) 4361 1059 (.node .leaf 4386 1099 .leaf)) 4406 2 (.node (.node .leaf 4431 8 .leaf) 4436 9 (.node .leaf 4456 14 .leaf))) 4461 15 (.node (.node (.node .leaf 4481 28 .leaf) 4486 29 (.node .leaf 4511 36 .leaf)) 4531 44 (.node (.node .leaf 4532 45 .leaf) 4556 52 (.node .leaf 4557 54 .leaf))))) 4561 53 (.node (.node (.node (.node (.node (.node .leaf 4581 58 .leaf) 4582 60 .leaf) 4586 59 (.node .leaf 4606 76 .leaf)) 4607 78 (.node (.node .leaf 4611 77 .leaf) 4631 102 (.node .leaf 4632 103 .leaf))) 4656 122 (.node (.node (.node .leaf 4657 124 .leaf) 4661 123 (.node .leaf 4681 146 .leaf)) 4682 148 (.node (.node .leaf 4686 147 .leaf) 4707 153 (.node .leaf 4711 152 .leaf)))) 4731 160 (.node (.node (.node (.node (.node .leaf 4732 161 .leaf) 4757 171 .leaf) 4761 170 (.node .leaf 4782 180 .leaf)) 4806 186 (.node (.node .leaf 4831 194 .leaf) 4836 195 (.node .leaf 4856 202 .leaf))) 4861 203 (.node (.node (.node .leaf 4886 220 .leaf) 4906 228 (.node .leaf 4907 229 .leaf)) 4931 240 (.node (.node .leaf 4932 242 .leaf) 4936 241 (.node .leaf 4956 252 .leaf))))))) 4957 254 (.node (.node (.node (.node (.node (.node (.node (.node .leaf 4961 253 .leaf) 4981 286 .leaf) 4982 287 (.node .leaf 5006 306 .leaf)) 5007 308 (.node (.node .leaf 5011 307 .leaf) 5031 330 (.node .leaf 5032 332 .leaf))) 5036 331 (.node (.node (.node (.node .leaf 5057 337 .leaf) 5061 336 .leaf) 5081 344 (.node .leaf 5082 345 .leaf)) 5107 355 (.node (.node .leaf 5111 354 .leaf) 5132 364 (.node .leaf 5156 370 .leaf)))) 5181 376 (.node (.node (.node (.node (.node .leaf 5186 377 .leaf) 5206 382 .leaf) 5211 383 (.node .leaf 5231 396 .leaf)) 5236 397 (.node (.node .leaf 5261 404 .leaf) 5281 412 (.node .leaf 5282 413 .leaf))) 5306 420 (.node (.node (.node .leaf 5307 422 .leaf) 5311 421 (.node .leaf 5331 426 .leaf)) 5332 428 (.node (.node .leaf 5336 427 .leaf) 5356 441 (.node .leaf 5357 443 .leaf))))) 5361 442 (.node (.node (.node (.node (.node (.node .leaf 5381 464 .leaf) 5382 465 .leaf) 5406 484 (.node .leaf 5407 486 .leaf)) 5411 485 (.node (.node .leaf 5431 508 .leaf) 5432 510 (.node .leaf 5436 509 .leaf))) 5457 521 (.node (.node (.node .leaf 5461 520 .leaf) 5481 528 (.node .leaf 5482 529 .leaf)) 5507 539 (.node (.node .leaf 5511 538 .leaf) 5532 548 (.node .leaf 5556 554 .leaf)))) 5581 562 (.node (.node (.node (.node (.node .leaf 5586 563 .leaf) 5606 570 .leaf) 5611 571 (.node .leaf 5631 584 .leaf)) 5636 585 (.node (.node .leaf 5661 592 .leaf) 5681 600 (.node .leaf 5682 601 .leaf))) 5706 612 (.node (.node (.node .leaf 5707 614 .leaf) 5711 613 (.node .leaf 5731 624 .leaf)) 5732 626 (.node (.node .leaf 5736 625 .leaf) 5756 639 (.node .leaf 5757 641 .leaf)))))) 5761 640 (.node (.node (.node (.node (.node (.node (.node .leaf 5781 662 .leaf) 5782 663 .leaf) 5806 682 (.node .leaf 5807 684 .leaf)) 5811 683 (.node (.node .leaf 5831 700 .leaf) 5832 702 (.node .leaf 5836 701 .leaf))) 5857 713 (.node (.node (.node (.node .leaf 5861 712 .leaf) 5882 725 .leaf) 5886 724 (.node .leaf 5907 732 .leaf)) 5931 738 (.node (.node .leaf 5956 746 .leaf) 5961 747 (.node .leaf 5981 754 .leaf)))) 5986 755 (.node (.node (.node (.node (.node .leaf 6011 772 .leaf) 6031 780 .leaf) 6032 781 (.node .leaf 6056 798 .leaf)) 6057 800 (.node (.node .leaf 6061 799 .leaf) 6081 832 (.node .leaf 6082 833 .leaf))) 6106 852 (.node (.node (.node .leaf 6107 854 .leaf) 6111 853 (.node .leaf 6131 876 .leaf)) 6132 878 (.node (.node .leaf 6136 877 .leaf) 6157 889 (.node .leaf 6161 888 .leaf))))) 6181 896 (.node (.node (.node (.node (.node (.node .leaf 6182 897 .leaf) 6207 907 .leaf) 6211 906 (.node .leaf 6232 916 .leaf)) 6256 922 (.node (.node .leaf 6281 930 .leaf) 6286 931 (.node .leaf 6306 938 .leaf))) 6311 939 (.node (.node (.node .leaf 6331 952 .leaf) 6336 953 (.node .leaf 6361 960 .leaf)) 6381 968 (.node (.node .leaf 6382 969 .leaf) 6406 986 (.node .leaf 6407 988 .leaf)))) 6411 987 (.node (.node (.node (.node (.node .leaf 6431 1004 .leaf) 6432 1006 .leaf) 6436 1005 (.node .leaf 6456 1030 .leaf)) 6457 1031 (.node (.node .leaf 6481 1050 .leaf) 6482 1052 (.node .leaf 6486 1051 .leaf))) 6506 1068 (.node (.node (.node .leaf 6507 1070 .leaf) 6511 1069 (.node .leaf 6532 1081 .leaf)) 6536 1080 (.node (.node .leaf 6557 1093 .leaf) 6561 1092 (.node .leaf 6582 1100 .leaf))))))))) 6607 3 (.node (.node (.node (.node (.node (.node (.node (.node (.node (.node .leaf 6632 10 .leaf) 6636 11 .leaf) 6657 16 (.node .leaf 6661 17 .leaf)) 6686 37 (.node (.node .leaf 6706 57 .leaf) 6707 55 (.node .leaf 6711 56 .leaf))) 6731 63 (.node (.node (.node (.node .leaf 6732 61 .leaf) 6736 62 .leaf) 6756 81 (.node .leaf 6757 79 .leaf)) 6761 80 (.node (.node .leaf 6781 93 .leaf) 6786 92 (.node .leaf 6806 127 .leaf)))) 6807 125 (.node (.node (.node (.node (.node .leaf 6811 126 .leaf) 6831 135 .leaf) 6832 134 (.node .leaf 6856 155 .leaf)) 6861 154 (.node (.node .leaf 6881 163 .leaf) 6882 162 (.node .leaf 6906 173 .leaf))) 6911 172 (.node (.node (.node .leaf 6931 181 .leaf) 6957 187 (.node .leaf 6982 196 .leaf)) 6986 197 (.node (.node .leaf 7007 204 .leaf) 7011 205 (.node .leaf 7036 221 .leaf))))) 7056 231 (.node (.node (.node (.node (.node (.node .leaf 7057 230 .leaf) 7081 245 .leaf) 7082 243 (.node .leaf 7086 244 .leaf)) 7106 257 (.node (.node .leaf 7107 255 .leaf) 7111 256 (.node .leaf 7131 311 .leaf))) 7132 309 (.node (.node (.node .leaf 7136 310 .leaf) 7156 319 (.node .leaf 7157 318 .leaf)) 7181 339 (.node (.node .leaf 7186 338 .leaf) 7206 347 (.node .leaf 7207 346 .leaf)))) 7231 357 (.node (.node (.node (.node (.node .leaf 7236 356 .leaf) 7256 365 .leaf) 7282 371 (.node .leaf 7307 378 .leaf)) 7311 379 (.node (.node .leaf 7332 384 .leaf) 7336 385 (.node .leaf 7361 405 .leaf))) 7381 425 (.node (.node (.node .leaf 7382 423 .leaf) 7386 424 (.node .leaf 7406 431 .leaf)) 7407 429 (.node (.node .leaf 7411 430 .leaf) 7431 446 (.node .leaf 7432 444 .leaf)))))) 7436 445 (.node (.node (.node (.node (.node (.node (.node .leaf 7456 455 .leaf) 7461 454 .leaf) 7481 489 (.node .leaf 7482 487 .leaf)) 7486 488 (.node (.node .leaf 7506 497 .leaf) 7507 496 (.node .leaf 7531 513 .leaf))) 7532 511 (.node (.node (.node (.node .leaf 7536 512 .leaf) 7556 523 .leaf) 7561 522 (.node .leaf 7581 531 .leaf)) 7582 530 (.node (.node .leaf 7606 541 .leaf) 7611 540 (.node .leaf 7631 549 .leaf)))) 7657 555 (.node (.node (.node (.node (.node .leaf 7682 564 .leaf) 7686 565 .leaf) 7707 572 (.node .leaf 7711 573 .leaf)) 7736 593 (.node (.node .leaf 7756 603 .leaf) 7757 602 (.node .leaf 7781 617 .leaf))) 7782 615 (.node (.node (.node .leaf 7786 616 .leaf) 7806 629 (.node .leaf 7807 627 .leaf)) 7811 628 (.node (.node .leaf 7831 644 .leaf) 7832 642 (.node .leaf 7836 643 .leaf))))) 7856 653 (.node (.node (.node (.node (.node (.node .leaf 7861 652 .leaf) 7881 687 .leaf) 7882 685 (.node .leaf 7886 686 .leaf)) 7906 695 (.node (.node .leaf 7907 694 .leaf) 7931 705 (.node .leaf 7932 703 .leaf))) 7936 704 (.node (.node (.node .leaf 7956 715 .leaf) 7961 714 (.node .leaf 7981 719 .leaf)) 7982 718 (.node (.node .leaf 8006 727 .leaf) 8011 726 (.node .leaf 8031 733 .leaf)))) 8057 739 (.node (.node (.node (.node (.node .leaf 8082 748 .leaf) 8086 749 .leaf) 8107 756 (.node .leaf 8111 757 .leaf)) 8136 773 (.node (.node .leaf 8156 783 .leaf) 8157 782 (.node .leaf 8181 791 .leaf))) 8182 789 (.node (.node (.node .leaf 8186 790 .leaf) 8206 803 (.node .leaf 8207 801 .leaf)) 8211 802 (.node (.node .leaf 8231 857 .leaf) 8232 855 (.node .leaf 8236 856 .leaf))))))) 8256 865 (.node (.node (.node (.node (.node (.node (.node (.node .leaf 8257 864 .leaf) 8281 881 .leaf) 8282 879 (.node .leaf 8286 880 .leaf)) 8306 891 (.node (.node .leaf 8311 890 .leaf) 8331 899 (.node .leaf 8332 898 .leaf))) 8356 909 (.node (.node (.node (.node .leaf 8361 908 .leaf) 8381 917 .leaf) 8407 923 (.node .leaf 8432 932 .leaf)) 8436 933 (.node (.node .leaf 8457 940 .leaf) 8461 941 (.node .leaf 8486 961 .leaf)))) 8506 971 (.node (.node (.node (.node (.node .leaf 8507 970 .leaf) 8531 979 .leaf) 8532 977 (.node .leaf 8536 978 .leaf)) 8556 991 (.node (.node .leaf 8557 989 .leaf) 8561 990 (.node .leaf 8581 1009 .leaf))) 8582 1007 (.node (.node (.node .leaf 8586 1008 .leaf) 8606 1021 (.node .leaf 8611 1020 .leaf)) 8631 1055 (.node (.node .leaf 8632 1053 .leaf) 8636 1054 (.node .leaf 8656 1063 .leaf))))) 8657 1062 (.node (.node (.node (.node (.node (.node .leaf 8681 1073 .leaf) 8682 1071 .leaf) 8686 1072 (.node .leaf 8706 1083 .leaf)) 8711 1082 (.node (.node .leaf 8731 1087 .leaf) 8732 1086 (.node .leaf 8756 1095 .leaf))) 8761 1094 (.node (.node (.node .leaf 8781 1101 .leaf) 8811 4 (.node .leaf 8831 21 .leaf)) 8836 20 (.node (.node .leaf 8856 31 .leaf) 8861 30 (.node .leaf 8881 38 .leaf)))) 8906 65 (.node (.node (.node (.node (.node .leaf 8907 66 .leaf) 8911 64 .leaf) 8931 83 (.node .leaf 8932 84 .leaf)) 8936 82 (.node (.node .leaf 8956 94 .leaf) 8957 95 (.node .leaf 8981 111 .leaf))) 8982 112 (.node (.node (.node .leaf 8986 110 .leaf) 9006 132 (.node .leaf 9007 133 .leaf)) 9032 137 (.node (.node .leaf 9036 136 .leaf) 9056 150 (.node .leaf 9057 151 .leaf)))))) 9061 149 (.node (.node (.node (.node (.node (.node (.node .leaf 9082 165 .leaf) 9086 164 .leaf) 9106 174 (.node .leaf 9107 175 .leaf)) 9132 182 (.node (.node .leaf 9161 188 .leaf) 9181 199 (.node .leaf 9186 198 .leaf))) 9206 209 (.node (.node (.node (.node .leaf 9211 208 .leaf) 9231 215 .leaf) 9236 214 (.node .leaf 9256 222 .leaf)) 9281 247 (.node (.node .leaf 9282 248 .leaf) 9286 246 (.node .leaf 9306 259 .leaf)))) 9307 260 (.node (.node (.node (.node (.node .leaf 9311 258 .leaf) 9331 271 .leaf) 9332 272 (.node .leaf 9336 270 .leaf)) 9356 280 (.node (.node .leaf 9357 281 .leaf) 9381 295 (.node .leaf 9382 296 .leaf))) 9386 294 (.node (.node (.node .leaf 9406 316 .leaf) 9407 317 (.node .leaf 9432 321 .leaf)) 9436 320 (.node (.node .leaf 9456 334 .leaf) 9457 335 (.node .leaf 9461 333 .leaf))))) 9482 349 (.node (.node (.node (.node (.node (.node .leaf 9486 348 .leaf) 9506 358 .leaf) 9507 359 (.node .leaf 9532 366 .leaf)) 9561 372 (.node (.node .leaf 9581 389 .leaf) 9586 388 (.node .leaf 9606 399 .leaf))) 9611 398 (.node (.node (.node .leaf 9631 406 .leaf) 9656 433 (.node .leaf 9657 434 .leaf)) 9661 432 (.node (.node .leaf 9681 456 .leaf) 9682 457 (.node .leaf 9706 473 .leaf)))) 9707 474 (.node (.node (.node (.node (.node .leaf 9711 472 .leaf) 9731 494 .leaf) 9732 495 (.node .leaf 9757 499 .leaf)) 9761 498 (.node (.node .leaf 9781 515 .leaf) 9782 516 (.node .leaf 9786 514 .leaf))) 9807 533 (.node (.node (.node .leaf 9811 532 .leaf) 9831 542 (.node .leaf 9832 543 .leaf)) 9857 550 (.node (.node .leaf 9886 556 .leaf) 9906 567 (.node .leaf 9911 566 .leaf)))))))) 9931 577 (.node (.node (.node (.node (.node (.node (.node (.node (.node .leaf 9936 576 .leaf) 9956 587 .leaf) 9961 586 (.node .leaf 9981 594 .leaf)) 10006 619 (.node (.node .leaf 10007 620 .leaf) 10011 618 (.node .leaf 10031 631 .leaf))) 10032 632 (.node (.node (.node (.node .leaf 10036 630 .leaf) 10056 654 .leaf) 10057 655 (.node .leaf 10081 671 .leaf)) 10082 672 (.node (.node .leaf 10086 670 .leaf) 10106 692 (.node .leaf 10107 693 .leaf)))) 10132 697 (.node (.node (.node (.node (.node .leaf 10136 696 .leaf) 10156 707 .leaf) 10157 708 (.node .leaf 10161 706 .leaf)) 10182 721 (.node (.node .leaf 10186 720 .leaf) 10207 734 (.node .leaf 10236 740 .leaf))) 10256 751 (.node (.node (.node .leaf 10261 750 .leaf) 10281 761 (.node .leaf 10286 760 .leaf)) 10306 767 (.node (.node .leaf 10311 766 .leaf) 10331 774 (.node .leaf 10356 793 .leaf))))) 10357 794 (.node (.node (.node (.node (.node (.node .leaf 10361 792 .leaf) 10381 805 .leaf) 10382 806 (.node .leaf 10386 804 .leaf)) 10406 817 (.node (.node .leaf 10407 818 .leaf) 10411 816 (.node .leaf 10431 826 .leaf))) 10432 827 (.node (.node (.node .leaf 10456 841 .leaf) 10457 842 (.node .leaf 10461 840 .leaf)) 10481 862 (.node (.node .leaf 10482 863 .leaf) 10507 867 (.node .leaf 10511 866 .leaf)))) 10531 883 (.node (.node (.node (.node (.node .leaf 10532 884 .leaf) 10536 882 .leaf) 10557 901 (.node .leaf 10561 900 .leaf)) 10581 910 (.node (.node .leaf 10582 911 .leaf) 10607 918 (.node .leaf 10636 924 .leaf))) 10656 935 (.node (.node (.node .leaf 10661 934 .leaf) 10681 945 (.node .leaf 10686 944 .leaf)) 10706 955 (.node (.node .leaf 10711 954 .leaf) 10731 962 (.node .leaf 10756 981 .leaf)))))) 10757 982 (.node (.node (.node (.node (.node (.node (.node .leaf 10761 980 .leaf) 10781 993 .leaf) 10782 994 (.node .leaf 10786 992 .leaf)) 10806 1011 (.node (.node .leaf 10807 1012 .leaf) 10811 1010 (.node .leaf 10831 1022 .leaf))) 10832 1023 (.node (.node (.node (.node .leaf 10856 1039 .leaf) 10857 1040 .leaf) 10861 1038 (.node .leaf 10881 1060 .leaf)) 10882 1061 (.node (.node .leaf 10907 1065 .leaf) 10911 1064 (.node .leaf 10931 1075 .leaf)))) 10932 1076 (.node (.node (.node (.node (.node .leaf 10936 1074 .leaf) 10957 1089 .leaf) 10961 1088 (.node .leaf 10982 1102 .leaf)) 11011 5 (.node (.node .leaf 11032 23 .leaf) 11036 22 (.node .leaf 11057 33 .leaf))) 11061 32 (.node (.node (.node .leaf 11082 39 .leaf) 11106 69 (.node .leaf 11107 68 .leaf)) 11111 67 (.node (.node .leaf 11131 87 .leaf) 11132 86 (.node .leaf 11136 85 .leaf))))) 11156 97 (.node (.node (.node (.node (.node (.node .leaf 11157 96 .leaf) 11181 115 .leaf) 11182 114 (.node .leaf 11186 113 .leaf)) 11206 139 (.node (.node .leaf 11211 138 .leaf) 11231 157 (.node .leaf 11232 156 .leaf))) 11256 167 (.node (.node (.node .leaf 11261 166 .leaf) 11281 177 (.node .leaf 11282 176 .leaf)) 11306 183 (.node (.node .leaf 11336 189 .leaf) 11357 211 (.node .leaf 11361 210 .leaf)))) 11382 217 (.node (.node (.node (.node (.node .leaf 11386 216 .leaf) 11407 223 .leaf) 11431 233 (.node .leaf 11436 232 .leaf)) 11456 251 (.node (.node .leaf 11457 250 .leaf) 11461 249 (.node .leaf 11481 263 .leaf))) 11482 262 (.node (.node (.node .leaf 11486 261 .leaf) 11506 275 (.node .leaf 11507 274 .leaf)) 11511 273 (.node (.node .leaf 11531 299 .leaf) 11532 298 (.node .leaf 11536 297 .leaf))))))) 11556 323 (.node (.node (.node (.node (.node (.node (.node (.node .leaf 11561 322 .leaf) 11581 341 .leaf) 11582 340 (.node .leaf 11606 351 .leaf)) 11611 350 (.node (.node .leaf 11631 361 .leaf) 11632 360 (.node .leaf 11656 367 .leaf))) 11686 373 (.node (.node (.node (.node .leaf 11707 391 .leaf) 11711 390 .leaf) 11732 401 (.node .leaf 11736 400 .leaf)) 11757 407 (.node (.node .leaf 11781 437 .leaf) 11782 436 (.node .leaf 11786 435 .leaf)))) 11806 449 (.node (.node (.node (.node (.node .leaf 11807 448 .leaf) 11811 447 .leaf) 11831 459 (.node .leaf 11832 458 .leaf)) 11856 477 (.node (.node .leaf 11857 476 .leaf) 11861 475 (.node .leaf 11881 501 .leaf))) 11886 500 (.node (.node (.node .leaf 11906 519 .leaf) 11907 518 (.node .leaf 11911 517 .leaf)) 11931 525 (.node (.node .leaf 11932 524 .leaf) 11956 535 (.node .leaf 11961 534 .leaf))))) 11981 545 (.node (.node (.node (.node (.node (.node .leaf 11982 544 .leaf) 12006 551 .leaf) 12036 557 (.node .leaf 12057 579 .leaf)) 12061 578 (.node (.node .leaf 12082 589 .leaf) 12086 588 (.node .leaf 12107 595 .leaf))) 12131 605 (.node (.node (.node .leaf 12136 604 .leaf) 12156 623 (.node .leaf 12157 622 .leaf)) 12161 621 (.node (.node .leaf 12181 635 .leaf) 12182 634 (.node .leaf 12186 633 .leaf)))) 12206 647 (.node (.node (.node (.node (.node .leaf 12207 646 .leaf) 12211 645 .leaf) 12231 657 (.node .leaf 12232 656 .leaf)) 12256 675 (.node (.node .leaf 12257 674 .leaf) 12261 673 (.node .leaf 12281 699 .leaf))) 12286 698 (.node (.node (.node .leaf 12306 711 .leaf) 12307 710 (.node .leaf 12311 709 .leaf)) 12331 717 (.node (.node .leaf 12332 716 .leaf) 12356 723 (.node .leaf 12361 722 .leaf)))))) 12381 729 (.node (.node (.node (.node (.node (.node (.node .leaf 12382 728 .leaf) 12406 735 .leaf) 12436 741 (.node .leaf 12457 763 .leaf)) 12461 762 (.node (.node .leaf 12482 769 .leaf) 12486 768 (.node .leaf 12507 775 .leaf))) 12531 785 (.node (.node (.node (.node .leaf 12536 784 .leaf) 12556 797 .leaf) 12557 796 (.node .leaf 12561 795 .leaf)) 12581 809 (.node (.node .leaf 12582 808 .leaf) 12586 807 (.node .leaf 12606 821 .leaf)))) 12607 820 (.node (.node (.node (.node (.node .leaf 12611 819 .leaf) 12631 845 .leaf) 12632 844 (.node .leaf 12636 843 .leaf)) 12656 869 (.node (.node .leaf 12661 868 .leaf) 12681 887 (.node .leaf 12682 886 .leaf))) 12686 885 (.node (.node (.node .leaf 12706 893 .leaf) 12707 892 (.node .leaf 12731 903 .leaf)) 12736 902 (.node (.node .leaf 12756 913 .leaf) 12757 912 (.node .leaf 12781 919 .leaf))))) 12811 925 (.node (.node (.node (.node (.node (.node .leaf 12832 947 .leaf) 12836 946 .leaf) 12857 957 (.node .leaf 12861 956 .leaf)) 12882 963 (.node (.node .leaf 12906 973 .leaf) 12911 972 (.node .leaf 12931 985 .leaf))) 12932 984 (.node (.node (.node .leaf 12936 983 .leaf) 12956 997 (.node .leaf 12957 996 .leaf)) 12961 995 (.node (.node .leaf 12981 1015 .leaf) 12982 1014 (.node .leaf 12986 1013 .leaf)))) 13006 1025 (.node (.node (.node (.node (.node .leaf 13007 1024 .leaf) 13031 1043 .leaf) 13032 1042 (.node .leaf 13036 1041 .leaf)) 13056 1067 (.node (.node .leaf 13061 1066 .leaf) 13081 1079 (.node .leaf 13082 1078 .leaf))) 13086 1077 (.node (.node (.node .leaf 13106 1085 .leaf) 13107 1084 (.node .leaf 13131 1091 .leaf)) 13136 1090 (.node (.node .leaf 13156 1097 .leaf) 13157 1096 (.node .leaf 13181 1103 .leaf))))))))))

def codeOf (z : (ρ : Fin 6) × Cell (2 * 2 ^ (2 - 1)) 88 (RecStage.parent3 ρ)) : ℕ :=
  ((z.1.val * 88 + z.2.1.val) * 5 + (z.2.2.val 0).val) * 5 + (z.2.2.val 1).val

def ok3 (z : (ρ : Fin 6) × Cell (2 * 2 ^ (2 - 1)) 88 (RecStage.parent3 ρ)) : Bool :=
  match ktree.find (codeOf z) with
  | some v => if h : v < 1104 then decide (codeOf (phi ⟨v, h⟩) = codeOf z) else false
  | none => false

theorem codeOf_injective : Function.Injective codeOf := by
  rintro ⟨ρ1, r1, s1⟩ ⟨ρ2, r2, s2⟩ h
  simp only [codeOf] at h
  have a0 := (s1.val 0).isLt
  have a1 := (s1.val 1).isLt
  have b0 := (s2.val 0).isLt
  have b1 := (s2.val 1).isLt
  have hr1 := r1.isLt
  have hr2 := r2.isLt
  have hρ1 := ρ1.isLt
  have hρ2 := ρ2.isLt
  norm_num at a0 a1 b0 b1
  have e0 : (s1.val 0).val = (s2.val 0).val := by omega
  have e1 : (s1.val 1).val = (s2.val 1).val := by omega
  have er : r1.val = r2.val := by omega
  have eρ : ρ1.val = ρ2.val := by omega
  obtain rfl : ρ1 = ρ2 := Fin.ext eρ
  obtain rfl : r1 = r2 := Fin.ext er
  have hs1 := s1.property.1
  have hs2 := s2.property.1
  have e2 : (s1.val 2).val = (s2.val 2).val := by omega
  have : s1 = s2 := by
    apply Subtype.ext
    funext i
    fin_cases i
    · exact Fin.ext e0
    · exact Fin.ext e1
    · exact Fin.ext e2
  rw [this]

def jwG (u v a0 a1 a2 e0 e1 e2 : ℕ) : ℕ :=
  if e0 ≤ a0 ∧ e1 ≤ a1 ∧ e2 ≤ a2 ∧ a0 - e0 ≤ 2 ∧ a1 - e1 ≤ 2 ∧ a2 - e2 ≤ 2 then
    (if e0 = 2 ∨ e1 = 2 ∨ e2 = 2 ∨ a0 - e0 = 2 ∨ a1 - e1 = 2 ∨ a2 - e2 = 2 then u else v)
  else 0

theorem jw_pos (a0 a1 a2 s0 e0 e1 e2 : ℕ) (h0 : a0 ≠ 0) (h1 : a1 ≠ 0) (h2 : a2 ≠ 0) :
    RecStage.jw a0 a1 a2 s0 e0 e1 e2 = jwG s0 (RecStage.D / 2 - s0) a0 a1 a2 e0 e1 e2 := by
  unfold RecStage.jw jwG
  have : ¬ (a0 = 0 ∨ a1 = 0 ∨ a2 = 0) := by omega
  simp only [this, if_false]

theorem jwG_lin (u v a0 a1 a2 e0 e1 e2 : ℕ) :
    jwG u v a0 a1 a2 e0 e1 e2 = jwG 1 0 a0 a1 a2 e0 e1 e2 * u + jwG 0 1 a0 a1 a2 e0 e1 e2 * v := by
  unfold jwG
  split_ifs <;> simp

def J2g (P : Fin 3 → ℕ) (u v : ℕ) (i : Fin 3) (x y : ℕ) : ℕ :=
  ∑ e : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) P,
    if x = (e.val i).val ∧ y = P i - (e.val i).val then
      jwG u v (P 0) (P 1) (P 2) (e.val 0).val (e.val 1).val (e.val 2).val else 0

def childWG (a0 a1 a2 k x y u v : ℕ) : ℕ :=
  (RecStage.elemT.map fun e ↦
    if RecStage.coord k e = x ∧ RecStage.coord k (a0 - e.1, a1 - e.2.1, a2 - e.2.2) = y then
      jwG u v a0 a1 a2 e.1 e.2.1 e.2.2 else 0).sum

theorem U_id : ∀ (c0 c1 c2 : Fin 5) (ρ : Fin 6) (i x y : Fin 3),
    c0.val + c1.val + c2.val = 4 → c0.val ≠ 0 → c1.val ≠ 0 → c2.val ≠ 0 →
    J2g (fun j ↦ (![c0, c1, c2] ((ReleasedJointInterior.roleEquiv ρ).symm j)).val) 1 0 i x.val y.val =
      childWG c0.val c1.val c2.val ((ReleasedJointInterior.roleEquiv ρ).symm i).val x.val y.val 1 0 ∧
    J2g (fun j ↦ (![c0, c1, c2] ((ReleasedJointInterior.roleEquiv ρ).symm j)).val) 0 1 i x.val y.val =
      childWG c0.val c1.val c2.val ((ReleasedJointInterior.roleEquiv ρ).symm i).val x.val y.val 0 1 := by
  decide +kernel

theorem S_id : ∀ (c0 c1 c2 : Fin 5) (k : Fin 3),
    c0.val + c1.val + c2.val = 4 → c0.val ≠ 0 → c1.val ≠ 0 → c2.val ≠ 0 →
    (∑ x : Fin 3, ∑ y : Fin 3, childWG c0.val c1.val c2.val k.val x.val y.val 1 0) = 2 ∧
    (∑ x : Fin 3, ∑ y : Fin 3, childWG c0.val c1.val c2.val k.val x.val y.val 0 1) = 2 := by
  decide +kernel

theorem card_cw1 : ∀ x : Fin 3,
    (Finset.univ.filter (fun U : CompleteSplit.CompleteWord 1 ↦ (U 0).val = x.val)).card = 1 := by
  decide +kernel

theorem list_lin {α : Type} (L : List α) (u v : ℕ) (f g k : α → ℕ)
    (hf : ∀ e, f e = g e * u + k e * v) :
    (L.map f).sum = (L.map g).sum * u + (L.map k).sum * v := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ih, hf]; ring

theorem childWG_lin (a0 a1 a2 k x y u v : ℕ) :
    childWG a0 a1 a2 k x y u v = childWG a0 a1 a2 k x y 1 0 * u + childWG a0 a1 a2 k x y 0 1 * v := by
  unfold childWG
  apply list_lin
  intro e
  split_ifs
  · exact jwG_lin _ _ _ _ _ _ _ _
  · simp

theorem J2g_lin (P : Fin 3 → ℕ) (u v : ℕ) (i : Fin 3) (x y : ℕ) :
    J2g P u v i x y = J2g P 1 0 i x y * u + J2g P 0 1 i x y * v := by
  unfold J2g
  rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  split_ifs
  · exact jwG_lin _ _ _ _ _ _ _ _
  · simp

theorem childW_pos (a0 a1 a2 s0 k x y : ℕ) (h0 : a0 ≠ 0) (h1 : a1 ≠ 0) (h2 : a2 ≠ 0) :
    RecStage.childW a0 a1 a2 s0 k x y = childWG a0 a1 a2 k x y s0 (RecStage.D / 2 - s0) := by
  unfold RecStage.childW childWG
  congr 1
  apply List.map_congr_left
  intro e _
  split_ifs
  · exact jw_pos _ _ _ _ _ _ _ h0 h1 h2
  · rfl

/-- Per-term data checks. -/
theorem rowChecks : ∀ r : Fin 1104,
    (RecStage.l2At r).2.2 = (RecStage.cellRec (phi r).1 (phi r).2.1 (phi r).2.2).2 ∧
    2 * (RecStage.l2At r).2.2 ≤ RecStage.D ∧ 0 < (RecStage.l2At r).2.1 := by
  decide +kernel

theorem d1a : ∀ r, codeOf (phi r) = phiCode r ∧ ktree.find (phiCode r) = some r.val := by
  decide +kernel

theorem d2 : ∀ r j, ((phi r).2.2.val j).val ≠ 0 := by decide +kernel

theorem d3a : ∀ (ρ : Fin 6) (c : Cell (2 * 2 ^ (2 - 1)) 88 (RecStage.parent3 ρ)),
    (∀ j, (c.2.val j).val ≠ 0) →
    0 < RecStage.m3 ρ c.1 c.2 + RecStage.m3 ρ c.1 (complement (RecStage.htotal3 ρ c.1) c.2) →
    ok3 ⟨ρ, c⟩ = true := by
  decide +kernel

theorem d4 : ∀ r, RecStage.n2 r = RecStage.m3 (phi r).1 (phi r).2.1 (phi r).2.2 +
    RecStage.m3 (phi r).1 (phi r).2.1
      (complement (RecStage.htotal3 (phi r).1 (phi r).2.1) (phi r).2.2) := by
  decide +kernel

theorem d5 : ∀ r i, RecStage.parent2 r i =
    ((phi r).2.2.val ((ReleasedJointInterior.roleEquiv (phi r).1).symm i)).val := by
  decide +kernel

theorem sum_mu2 (i : Fin 3) (c : Cell (2 * 2 ^ (1 - 1)) 1104 RecStage.parent2) :
    ∑ U, RecStage.mu2 i c U =
      RecStage.m2 c.1 c.2 + RecStage.m2 c.1 (complement (RecStage.htotal2 c.1) c.2) := by
  unfold RecStage.mu2
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
  have := card_cw1 ⟨(c.2.val i).val, (c.2.val i).isLt⟩
  rw [this, one_mul]

theorem mixture_formula (r : Fin 1104) (i : Fin 3) (w : CompleteSplit.CompleteWord 2) :
    parentMixture RecStage.htotal2 RecStage.n2 RecStage.m2 (RecStage.mu2 i) r (fun h _ ↦ w h) =
      ((∑ e : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (RecStage.parent2 r),
        if (w 0).val = (e.val i).val ∧
            (w 1).val = ((complement (RecStage.htotal2 r) e).val i).val then
          RecStage.m2 r e else 0 : ℕ) : ℝ) / RecStage.n2 r := by
  unfold parentMixture
  congr 1
  push_cast
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  unfold cellFrequency
  rw [sum_mu2, sum_mu2]
  simp only [complement_complement]
  by_cases hm : RecStage.m2 r e = 0
  · simp [hm]
  have hM : (0 : ℝ) < ((RecStage.m2 r e + RecStage.m2 r (complement (RecStage.htotal2 r) e) : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < RecStage.m2 r e + RecStage.m2 r (complement (RecStage.htotal2 r) e))
  have hM' : (0 : ℝ) < ((RecStage.m2 r (complement (RecStage.htotal2 r) e) + RecStage.m2 r e : ℕ) : ℝ) := by
    rw [add_comm]; exact hM
  simp only [RecStage.mu2]
  split_ifs with h1 h2 h3 h3 <;> simp_all
  all_goals (rw [div_self hM.ne', div_self hM'.ne']; ring)

theorem sum_cw2 (g : ℕ → ℕ → ℕ) :
    ∑ v : CompleteSplit.CompleteWord 2, g (v 0).val (v 1).val =
      ∑ x : Fin 3, ∑ y : Fin 3, g x.val y.val := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (finTwoArrowEquiv (Fin 3)) _ _ (fun v ↦ rfl)

theorem mu3_formula (ρ : Fin 6) (i : Fin 3) (c : Cell (2 * 2 ^ (2 - 1)) 88 (RecStage.parent3 ρ))
    (w : CompleteSplit.CompleteWord 2) :
    RecStage.mu3 ρ i c w =
      ((RecStage.m3 ρ c.1 c.2 + RecStage.m3 ρ c.1 (complement (RecStage.htotal3 ρ c.1) c.2)) /
        RecStage.D) * (RecStage.cellDist ρ i c.1 c.2).getD (3 * (w 0).val + (w 1).val) 0 := by
  unfold RecStage.mu3
  have hD : 0 < RecStage.D := by unfold RecStage.D; norm_num
  obtain ⟨q, hq⟩ : RecStage.D ∣
      RecStage.m3 ρ c.1 c.2 + RecStage.m3 ρ c.1 (complement (RecStage.htotal3 ρ c.1) c.2) := by
    unfold RecStage.m3
    exact Dvd.dvd.add (Dvd.dvd.mul_left (dvd_pow_self _ two_ne_zero) _)
      (Dvd.dvd.mul_left (dvd_pow_self _ two_ne_zero) _)
  rw [hq, Nat.mul_div_cancel_left q hD, mul_assoc, Nat.mul_div_cancel_left _ hD]

theorem dist_eq (ρ : Fin 6) (k : Fin 3) (r : Fin 88)
    (c : RecursiveThinSplit.Split (2 * 2 ^ (2 - 1)) (RecStage.parent3 ρ r)) (x y : ℕ)
    (hx : x < 3) (hy : y < 3) :
    (RecStage.cellDist ρ k r c).getD (3 * x + y) 0 =
      RecStage.childW (c.val 0).val (c.val 1).val (c.val 2).val (RecStage.cellRec ρ r c).2
        k.val x y := by
  unfold RecStage.cellDist
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
  simp only [Option.map_some, Option.getD_some]
  have h1 : (3 * x + y) / 3 = x := by omega
  have h2 : (3 * x + y) % 3 = y := by omega
  rw [h1, h2]

theorem d6 (r : Fin 1104) (i : Fin 3) (w : CompleteSplit.CompleteWord 2) :
    parentMixture RecStage.htotal2 RecStage.n2 RecStage.m2 (RecStage.mu2 i) r (fun h _ ↦ w h) =
      cellFrequency (RecStage.mu3 (phi r).1 ((ReleasedJointInterior.roleEquiv (phi r).1).symm i))
        (phi r).2 w := by
  obtain ⟨C1, C4, C5⟩ := rowChecks r
  have hpos := d2 r
  have hpar := d5 r
  have hn := d4 r
  generalize phi r = z at C1 hpos hpar hn ⊢
  obtain ⟨ρ, c⟩ := z
  dsimp only at C1 hpos hpar hn ⊢
  set σ := ReleasedJointInterior.roleEquiv ρ with hσ
  set s0 := (RecStage.l2At r).2.2 with hs0
  set W := (RecStage.l2At r).2.1 with hW
  set D := RecStage.D with hDdef
  have hD : 0 < D := by rw [hDdef]; unfold RecStage.D; norm_num
  have hDeven : D = 2 * (D / 2) := by rw [hDdef]; unfold RecStage.D; norm_num
  set c0 := c.2.val 0 with hc0
  set c1 := c.2.val 1 with hc1
  set c2 := c.2.val 2 with hc2
  have hsum : c0.val + c1.val + c2.val = 4 := c.2.property.1
  have hcv : c.2.val = ![c0, c1, c2] := by
    funext k; fin_cases k <;> rfl
  have hP : RecStage.parent2 r = fun j ↦ (![c0, c1, c2] (σ.symm j)).val := by
    funext j; rw [hpar j, hcv]
  have hpar0 : RecStage.parent2 r 0 ≠ 0 := by rw [hpar]; exact hpos _
  have hpar1 : RecStage.parent2 r 1 ≠ 0 := by rw [hpar]; exact hpos _
  have hpar2 : RecStage.parent2 r 2 ≠ 0 := by rw [hpar]; exact hpos _
  have hc0p : c0.val ≠ 0 := hpos 0
  have hc1p : c1.val ≠ 0 := hpos 1
  have hc2p : c2.val ≠ 0 := hpos 2
  -- the level-2 numerator
  have hnum : (∑ e : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (RecStage.parent2 r),
        if (w 0).val = (e.val i).val ∧
            (w 1).val = ((complement (RecStage.htotal2 r) e).val i).val then
          RecStage.m2 r e else 0) =
      W * D * J2g (RecStage.parent2 r) s0 (D / 2 - s0) i (w 0).val (w 1).val := by
    unfold J2g
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ ↦ ?_
    have hce : ((complement (RecStage.htotal2 r) e).val i).val =
        RecStage.parent2 r i - (e.val i).val := rfl
    rw [hce]
    split_ifs with h
    · show W * RecStage.jw _ _ _ _ _ _ _ * D = _
      rw [jw_pos _ _ _ _ _ _ _ hpar0 hpar1 hpar2]
      ring
    · simp
  have hJ : J2g (RecStage.parent2 r) s0 (D / 2 - s0) i (w 0).val (w 1).val =
      RecStage.childW c0.val c1.val c2.val s0 (σ.symm i).val (w 0).val (w 1).val := by
    rw [hP, J2g_lin, (U_id c0 c1 c2 ρ i (w 0) (w 1) hsum hc0p hc1p hc2p).1,
      (U_id c0 c1 c2 ρ i (w 0) (w 1) hsum hc0p hc1p hc2p).2, ← childWG_lin,
      childW_pos _ _ _ _ _ _ _ hc0p hc1p hc2p]
  have hdist : ∀ v : CompleteSplit.CompleteWord 2,
      (RecStage.cellDist ρ (σ.symm i) c.1 c.2).getD (3 * (v 0).val + (v 1).val) 0 =
        RecStage.childW c0.val c1.val c2.val s0 (σ.symm i).val (v 0).val (v 1).val := by
    intro v
    rw [dist_eq _ _ _ _ _ _ (v 0).isLt (v 1).isLt, C1]
  have hdsum : ∑ v : CompleteSplit.CompleteWord 2,
      RecStage.childW c0.val c1.val c2.val s0 (σ.symm i).val (v 0).val (v 1).val = D := by
    rw [sum_cw2 (fun x y ↦ RecStage.childW c0.val c1.val c2.val s0 (σ.symm i).val x y)]
    simp only [childW_pos _ _ _ _ _ _ _ hc0p hc1p hc2p, childWG_lin _ _ _ _ _ _ s0]
    rw [Finset.sum_congr rfl fun x _ ↦ Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp only [← Finset.sum_mul]
    rw [(S_id c0 c1 c2 (σ.symm i) hsum hc0p hc1p hc2p).1,
      (S_id c0 c1 c2 (σ.symm i) hsum hc0p hc1p hc2p).2]
    omega
  set M := RecStage.m3 ρ c.1 c.2 + RecStage.m3 ρ c.1 (complement (RecStage.htotal3 ρ c.1) c.2)
    with hM
  have hn2 : RecStage.n2 r = W * D ^ 2 := rfl
  have hq : 0 < M / D := by
    rw [← hn, hn2]
    rw [show W * D ^ 2 = D * (W * D) by ring, Nat.mul_div_cancel_left _ hD]
    exact Nat.mul_pos C5 hD
  rw [mixture_formula, hnum, hJ]
  unfold cellFrequency
  simp only [mu3_formula ρ _ c]
  rw [← Finset.mul_sum]
  simp only [hdist]
  rw [hdsum, hn2]
  have hWD : (0 : ℝ) < W := by exact_mod_cast C5
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hqR : (0 : ℝ) < ((M / D : ℕ) : ℝ) := by exact_mod_cast hq
  push_cast
  field_simp
  exact (mul_div_cancel_right₀ _ (by exact_mod_cast hq.ne')).symm

end C9Corr

open C9Corr in
theorem solution :
    ∃ φ : Fin 1104 → (ρ : Fin 6) × Cell (2 * 2 ^ (2 - 1)) 88 (RecStage.parent3 ρ),
      Function.Injective φ ∧
      (∀ r j, ((φ r).2.2.val j).val ≠ 0) ∧
      (∀ (ρ : Fin 6) (c : Cell (2 * 2 ^ (2 - 1)) 88 (RecStage.parent3 ρ)),
        (∀ j, (c.2.val j).val ≠ 0) →
        0 < RecStage.m3 ρ c.1 c.2 + RecStage.m3 ρ c.1 (complement (RecStage.htotal3 ρ c.1) c.2) →
        ∃ r, φ r = ⟨ρ, c⟩) ∧
      (∀ r, RecStage.n2 r = RecStage.m3 (φ r).1 (φ r).2.1 (φ r).2.2 +
        RecStage.m3 (φ r).1 (φ r).2.1 (complement (RecStage.htotal3 (φ r).1 (φ r).2.1) (φ r).2.2)) ∧
      (∀ r i, RecStage.parent2 r i =
        ((φ r).2.2.val ((ReleasedJointInterior.roleEquiv (φ r).1).symm i)).val) ∧
      (∀ r i (w : CompleteSplit.CompleteWord 2),
        parentMixture RecStage.htotal2 RecStage.n2 RecStage.m2 (RecStage.mu2 i) r
            (fun h _ ↦ w h) =
          cellFrequency (RecStage.mu3 (φ r).1 ((ReleasedJointInterior.roleEquiv (φ r).1).symm i))
            (φ r).2 w) := by
  refine ⟨phi, ?_, d2, ?_, d4, d5, d6⟩
  · intro a b h
    have ha := d1a a
    have hb := d1a b
    have hcode : phiCode a = phiCode b := by rw [← ha.1, ← hb.1, h]
    have : some a.val = some b.val := by rw [← ha.2, ← hb.2, hcode]
    exact Fin.ext (Option.some.inj this)
  · intro ρ c hpos hm
    have h := d3a ρ c hpos hm
    unfold ok3 at h
    split at h
    · rename_i v _
      split_ifs at h with hv
      exact ⟨⟨v, hv⟩, codeOf_injective (of_decide_eq_true h)⟩
    · exact absurd h (by simp)

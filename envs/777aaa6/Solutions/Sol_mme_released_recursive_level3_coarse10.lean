-- Prove2me | solution 1 for mme_released_recursive_level3_coarse10
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T10:38:11.545965+00:00
-- url     : https://prove2.me/submissions/d71078ab-9bae-47ed-875c-43b3e0489edd

import Mathlib
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_certified_entropy_bridge_data
import Definitions.Def_mme_certified_generic_floor_data
open BigOperators MME MME.RecursiveYZ MME.RecStage MME.Cert MME.RegionRate
  MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace L3C

theorem cr_4_44 :
    (768127764301229741304997858058 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (44 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 1 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 4) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 3 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (44 : Fin 88) = fun j => if j.val = 1 then 393541014929840759542 * 7155215530 * 10 ^ 24 else if j.val = 2 then 393541014929840759542 * 492844912060 * 10 ^ 24 else if j.val = 3 then 393541014929840759542 * 492844661887 * 10 ^ 24 else if j.val = 4 then 393541014929840759542 * 7155210523 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_45 :
    (814051919860347967453034530207 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (45 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 8 else 6) else if j.val = 1 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else -2) else if j.val = 2 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else -2) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 8 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (45 : Fin 88) = fun j => if j.val = 0 then 5915395272961903373937 * 13048883465 * 10 ^ 24 else if j.val = 1 then 5915395272961903373937 * 486951125473 * 10 ^ 24 else if j.val = 2 then 5915395272961903373937 * 486950961555 * 10 ^ 24 else if j.val = 3 then 5915395272961903373937 * 13049029507 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_46 :
    (913523074985922241635849950810 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (46 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else -4) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else -8) else if j.val = 2 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (46 : Fin 88) = fun j => if j.val = 0 then 2832800375735216448583 * 184227999454 * 10 ^ 24 else if j.val = 1 then 2832800375735216448583 * 631543985477 * 10 ^ 24 else if j.val = 2 then 2832800375735216448583 * 184228015069 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_47 :
    (693147176320240717253036000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (47 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (47 : Fin 88) = fun j => if j.val = 0 then 111384194560710480108 * 499967443493 * 10 ^ 24 else if j.val = 1 then 111384194560710480108 * 500032556507 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_48 :
    (541180737380624197153392581904 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (48 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -6 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else 0) else if j.val = 2 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -5 else if k.val = 2 then -6 else 2) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else 0) else if j.val = 4 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -6 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (48 : Fin 88) = fun j => if j.val = 0 then 18004967325945071968206 * 328747175 * 10 ^ 24 else if j.val = 1 then 18004967325945071968206 * 76797778150 * 10 ^ 24 else if j.val = 2 then 18004967325945071968206 * 845746954199 * 10 ^ 24 else if j.val = 3 then 18004967325945071968206 * 76797773174 * 10 ^ 24 else if j.val = 4 then 18004967325945071968206 * 328747302 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_49 :
    (811877301077083471639443609560 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (49 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 1 else if k.val = 2 then 3 else -6) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 1 else if k.val = 2 then 3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (49 : Fin 88) = fun j => if j.val = 0 then 25400639798265866149852 * 12749619837 * 10 ^ 24 else if j.val = 1 then 25400639798265866149852 * 487250415338 * 10 ^ 24 else if j.val = 2 then 25400639798265866149852 * 487250520145 * 10 ^ 24 else if j.val = 3 then 25400639798265866149852 * 12749444680 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_50 :
    (693147180557850018427088000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (50 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (50 : Fin 88) = fun j => if j.val = 0 then 3234276892914791088544 * 500000723756 * 10 ^ 24 else if j.val = 1 then 3234276892914791088544 * 499999276244 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_51 :
    (808497084789076486700589988053 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (51 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 0) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 2) else if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 2) else if j.val = 3 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (51 : Fin 88) = fun j => if j.val = 0 then 35384309302883979821004 * 12288013201 * 10 ^ 24 else if j.val = 1 then 35384309302883979821004 * 487711984267 * 10 ^ 24 else if j.val = 2 then 35384309302883979821004 * 487711984918 * 10 ^ 24 else if j.val = 3 then 35384309302883979821004 * 12288017614 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_52 :
    (693147180559945169515648000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (52 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (52 : Fin 88) = fun j => if j.val = 0 then 10444169626336467793416 * 500000005914 * 10 ^ 24 else if j.val = 1 then 10444169626336467793416 * 499999994086 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_53 :
    (809606773586689517385998719850 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (53 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -3) else if j.val = 1 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -4) else if j.val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -4) else if j.val = 3 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (53 : Fin 88) = fun j => if j.val = 0 then 39246437638786422208520 * 12439006405 * 10 ^ 24 else if j.val = 1 then 39246437638786422208520 * 487560988713 * 10 ^ 24 else if j.val = 2 then 39246437638786422208520 * 487561009507 * 10 ^ 24 else if j.val = 3 then 39246437638786422208520 * 12438995375 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_54 :
    (904101392715791484866693310392 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (54 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else if j.val = 1 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -1 else if k.val = 2 then -7 else -1) else if j.val = 2 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (54 : Fin 88) = fun j => if j.val = 0 then 1362867476596803749250 * 180454082338 * 10 ^ 24 else if j.val = 1 then 1362867476596803749250 * 639091843667 * 10 ^ 24 else if j.val = 2 then 1362867476596803749250 * 180454073995 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_55 :
    (900199270264291755529499818451 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (55 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 6 else if k.val = 2 then -2 else 7) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else -1) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 6 else if k.val = 2 then -2 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (55 : Fin 88) = fun j => if j.val = 0 then 2331298842478376446770 * 178919287752 * 10 ^ 24 else if j.val = 1 then 2331298842478376446770 * 642161401086 * 10 ^ 24 else if j.val = 2 then 2331298842478376446770 * 178919311162 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_56 :
    (693147035098486360120508801025 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (56 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (56 : Fin 88) = fun j => if j.val = 0 then 109659994126070730500 * 500267424229 * 10 ^ 24 else if j.val = 1 then 109659994126070730500 * 499732575771 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_57 :
    (711920765226528674414692795685 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (57 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (57 : Fin 88) = fun j => if j.val = 2 then 110788246444993592814 * 118512873508 * 10 ^ 24 else if j.val = 3 then 110788246444993592814 * 762974366372 * 10 ^ 24 else if j.val = 4 then 110788246444993592814 * 118512760120 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_58 :
    (769499588009452763230169921478 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (58 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else -8) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -2) else if j.val = 3 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -2) else if j.val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -1 else if k.val = 2 then -6 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (58 : Fin 88) = fun j => if j.val = 1 then 925028797380252713577 * 7317727920 * 10 ^ 24 else if j.val = 2 then 925028797380252713577 * 492682248444 * 10 ^ 24 else if j.val = 3 then 925028797380252713577 * 492682318999 * 10 ^ 24 else if j.val = 4 then 925028797380252713577 * 7317704637 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_59 :
    (809613051837585436886761574279 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (59 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -3) else if j.val = 1 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -4) else if j.val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -4) else if j.val = 3 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (59 : Fin 88) = fun j => if j.val = 0 then 1323357534643892744457 * 12439797000 * 10 ^ 24 else if j.val = 1 then 1323357534643892744457 * 487560203454 * 10 ^ 24 else if j.val = 2 then 1323357534643892744457 * 487560083417 * 10 ^ 24 else if j.val = 3 then 1323357534643892744457 * 12439916129 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_60 :
    (900553977589347009069508420834 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (60 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -7) else if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else -5) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (60 : Fin 88) = fun j => if j.val = 0 then 3442557872355166768400 * 179058139540 * 10 ^ 24 else if j.val = 1 then 3442557872355166768400 * 641883700448 * 10 ^ 24 else if j.val = 2 then 3442557872355166768400 * 179058160012 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_61 :
    (693146832004325337769191326700 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (61 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else 8) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (61 : Fin 88) = fun j => if j.val = 0 then 109646617331017308087 * 500417464940 * 10 ^ 24 else if j.val = 1 then 109646617331017308087 * 499582535060 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_62 :
    (555861117124767761723585701433 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (62 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else 5) else if j.val = 1 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else 3) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else 3) else if j.val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (62 : Fin 88) = fun j => if j.val = 0 then 28849530224411760060120 * 336116794 * 10 ^ 24 else if j.val = 1 then 28849530224411760060120 * 79863153005 * 10 ^ 24 else if j.val = 2 then 28849530224411760060120 * 839601460725 * 10 ^ 24 else if j.val = 3 then 28849530224411760060120 * 79863154392 * 10 ^ 24 else if j.val = 4 then 28849530224411760060120 * 336115084 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_63 :
    (812598407739909718941214269880 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (63 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -7 else if k.val = 2 then -5 else 3) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -7 else if k.val = 2 then -5 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (63 : Fin 88) = fun j => if j.val = 0 then 36331063141478532832742 * 12848663888 * 10 ^ 24 else if j.val = 1 then 36331063141478532832742 * 487151361243 * 10 ^ 24 else if j.val = 2 then 36331063141478532832742 * 487151418681 * 10 ^ 24 else if j.val = 3 then 36331063141478532832742 * 12848556188 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_64 :
    (911273294943225870210586493818 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (64 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (26 : Int) else if k.val = 1 then -8 else if k.val = 2 then -8 else 1) else if j.val = 1 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 2 else if k.val = 2 then -4 else 8) else if j.val = 2 then (if k.val = 0 then (26 : Int) else if k.val = 1 then -8 else if k.val = 2 then -8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (64 : Fin 88) = fun j => if j.val = 0 then 34713345380975204700145 * 183317850179 * 10 ^ 24 else if j.val = 1 then 34713345380975204700145 * 633364330640 * 10 ^ 24 else if j.val = 2 then 34713345380975204700145 * 183317819181 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_65 :
    (693147180559934353608332000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (65 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (65 : Fin 88) = fun j => if j.val = 0 then 3877674156037861098468 * 499999947665 * 10 ^ 24 else if j.val = 1 then 3877674156037861098468 * 500000052335 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_66 :
    (809334046260627355902765110426 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (66 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -1) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -1) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -1) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (66 : Fin 88) = fun j => if j.val = 0 then 35536457924913754292998 * 12401840701 * 10 ^ 24 else if j.val = 1 then 35536457924913754292998 * 487598154659 * 10 ^ 24 else if j.val = 2 then 35536457924913754292998 * 487598154286 * 10 ^ 24 else if j.val = 3 then 35536457924913754292998 * 12401850354 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_67 :
    (693147180559943320614016000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (67 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (67 : Fin 88) = fun j => if j.val = 0 then 7086635326284777546190 * 500000022298 * 10 ^ 24 else if j.val = 1 then 7086635326284777546190 * 499999977702 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_68 :
    (811730108517287143723935714060 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (68 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (19 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -8) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (19 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (68 : Fin 88) = fun j => if j.val = 0 then 32297437831669942155216 * 12729341230 * 10 ^ 24 else if j.val = 1 then 32297437831669942155216 * 487270654020 * 10 ^ 24 else if j.val = 2 then 32297437831669942155216 * 487270674518 * 10 ^ 24 else if j.val = 3 then 32297437831669942155216 * 12729330232 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_69 :
    (904173537277117988515101760103 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (69 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -3 else -6) else if j.val = 1 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -4) else if j.val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (69 : Fin 88) = fun j => if j.val = 0 then 7869749807762197479852 * 180482608497 * 10 ^ 24 else if j.val = 1 then 7869749807762197479852 * 639034790747 * 10 ^ 24 else if j.val = 2 then 7869749807762197479852 * 180482600756 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_70 :
    (908308807483168200389391263148 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (70 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 4) else if j.val = 1 then (if k.val = 0 then (35 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else -8) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (70 : Fin 88) = fun j => if j.val = 0 then 2051930839037285587360 * 182127240327 * 10 ^ 24 else if j.val = 1 then 2051930839037285587360 * 635745531285 * 10 ^ 24 else if j.val = 2 then 2051930839037285587360 * 182127228388 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_71 :
    (693147180559945176706832000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (71 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (71 : Fin 88) = fun j => if j.val = 0 then 517324085058055137746 * 500000005760 * 10 ^ 24 else if j.val = 1 then 517324085058055137746 * 499999994240 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_72 :
    (693147180559945229850832000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (72 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (72 : Fin 88) = fun j => if j.val = 0 then 110206010965453588824 * 499999995540 * 10 ^ 24 else if j.val = 1 then 110206010965453588824 * 500000004460 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_73 :
    (712047937852289715885666312985 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (73 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 3 then (if k.val = 0 then (36 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -8) else if j.val = 4 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (73 : Fin 88) = fun j => if j.val = 2 then 110864782856322348018 * 118540505151 * 10 ^ 24 else if j.val = 3 then 110864782856322348018 * 762906068330 * 10 ^ 24 else if j.val = 4 then 110864782856322348018 * 118553426519 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_74 :
    (769485884848233496374812645712 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (74 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 0) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -2) else if j.val = 3 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -2) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (74 : Fin 88) = fun j => if j.val = 1 then 911604919615666516775 * 7316081859 * 10 ^ 24 else if j.val = 2 then 911604919615666516775 * 492683929170 * 10 ^ 24 else if j.val = 3 then 911604919615666516775 * 492683893382 * 10 ^ 24 else if j.val = 4 then 911604919615666516775 * 7316095589 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_75 :
    (812699318882261418586821284031 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (75 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else 3) else if j.val = 1 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 6) else if j.val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 6) else if j.val = 3 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (75 : Fin 88) = fun j => if j.val = 0 then 4639269892467041474888 * 12862404921 * 10 ^ 24 else if j.val = 1 then 4639269892467041474888 * 487137615305 * 10 ^ 24 else if j.val = 2 then 4639269892467041474888 * 487137400163 * 10 ^ 24 else if j.val = 3 then 4639269892467041474888 * 12862579611 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_76 :
    (908834842071177326249467244559 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (76 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 5 else 2) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 6) else if j.val = 2 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (76 : Fin 88) = fun j => if j.val = 0 then 3137014326140716983246 * 182337765707 * 10 ^ 24 else if j.val = 1 then 3137014326140716983246 * 635324428680 * 10 ^ 24 else if j.val = 2 then 3137014326140716983246 * 182337805613 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_77 :
    (693147126156656193543936308395 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (77 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (77 : Fin 88) = fun j => if j.val = 0 then 110602898391032769120 * 500158809456 * 10 ^ 24 else if j.val = 1 then 110602898391032769120 * 499841190544 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_78 :
    (555860243632069264890026838967 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (78 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else -6) else if j.val = 1 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else 3) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else 3) else if j.val = 4 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (78 : Fin 88) = fun j => if j.val = 0 then 28413854865319997008170 * 336184767 * 10 ^ 24 else if j.val = 1 then 28413854865319997008170 * 79862757452 * 10 ^ 24 else if j.val = 2 then 28413854865319997008170 * 839602147902 * 10 ^ 24 else if j.val = 3 then 28413854865319997008170 * 79862726929 * 10 ^ 24 else if j.val = 4 then 28413854865319997008170 * 336182950 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_79 :
    (812616744654764801123986716370 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (79 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else -5) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (79 : Fin 88) = fun j => if j.val = 0 then 33357649585939236593184 * 12851195399 * 10 ^ 24 else if j.val = 1 then 33357649585939236593184 * 487148875654 * 10 ^ 24 else if j.val = 2 then 33357649585939236593184 * 487148859617 * 10 ^ 24 else if j.val = 3 then 33357649585939236593184 * 12851069330 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_80 :
    (911391161240935185140221050852 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (80 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else 1) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else 5) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (80 : Fin 88) = fun j => if j.val = 0 then 10400408203599984948846 * 183365429796 * 10 ^ 24 else if j.val = 1 then 10400408203599984948846 * 633269248878 * 10 ^ 24 else if j.val = 2 then 10400408203599984948846 * 183365321326 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_81 :
    (693147180559945024280236000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (81 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (81 : Fin 88) = fun j => if j.val = 0 then 3579244673565198867426 * 499999991557 * 10 ^ 24 else if j.val = 1 then 3579244673565198867426 * 500000008443 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_82 :
    (809263012016830707453111634956 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (82 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 6 else if k.val = 2 then 0 else -6) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -1) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -1) else if j.val = 3 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 6 else if k.val = 2 then 0 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (82 : Fin 88) = fun j => if j.val = 0 then 37813502464119196381712 * 12392164674 * 10 ^ 24 else if j.val = 1 then 37813502464119196381712 * 487607829320 * 10 ^ 24 else if j.val = 2 then 37813502464119196381712 * 487607824408 * 10 ^ 24 else if j.val = 3 then 37813502464119196381712 * 12392181598 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_83 :
    (693147180559945273176832000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (83 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (83 : Fin 88) = fun j => if j.val = 0 then 9511621958048838330626 * 500000003010 * 10 ^ 24 else if j.val = 1 then 9511621958048838330626 * 499999996990 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_84 :
    (810301755187771029935204828691 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (84 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 2 else if k.val = 2 then -2 else -6) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else -2) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else -2) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 2 else if k.val = 2 then -2 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (84 : Fin 88) = fun j => if j.val = 0 then 38214206077707233028225 * 12533825124 * 10 ^ 24 else if j.val = 1 then 38214206077707233028225 * 487466170705 * 10 ^ 24 else if j.val = 2 then 38214206077707233028225 * 487466183976 * 10 ^ 24 else if j.val = 3 then 38214206077707233028225 * 12533820195 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_85 :
    (904069347799499958805262237154 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (85 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else if j.val = 1 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -1 else if k.val = 2 then -7 else -1) else if j.val = 2 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (85 : Fin 88) = fun j => if j.val = 0 then 1125538641257240351228 * 180441408889 * 10 ^ 24 else if j.val = 1 then 1125538641257240351228 * 639117185941 * 10 ^ 24 else if j.val = 2 then 1125538641257240351228 * 180441405170 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_86 :
    (900150591845555583510334824602 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (86 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else 4) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -7 else 2) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (86 : Fin 88) = fun j => if j.val = 0 then 2339014932834883227790 * 178900236053 * 10 ^ 24 else if j.val = 1 then 2339014932834883227790 * 642199489198 * 10 ^ 24 else if j.val = 2 then 2339014932834883227790 * 178900274749 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cr_4_87 :
    (693147033294038099932950429760 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (87 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) := by
  have hM : marginalCounts (m3 4) 0 (87 : Fin 88) = fun j => if j.val = 0 then 109673245439577490555 * 499730651980 * 10 ^ 24 else if j.val = 1 then 109673245439577490555 * 500269348020 * 10 ^ 24 else 0 := by decide +kernel
  unfold regFloorG normQ
  rw [hM]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    ((768127764301229741304997858058 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (44 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 1 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 4) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 3 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((814051919860347967453034530207 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (45 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 8 else 6) else if j.val = 1 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else -2) else if j.val = 2 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else -2) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 8 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((913523074985922241635849950810 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (46 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else -4) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else -8) else if j.val = 2 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147176320240717253036000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (47 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((541180737380624197153392581904 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (48 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -6 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else 0) else if j.val = 2 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -5 else if k.val = 2 then -6 else 2) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else 0) else if j.val = 4 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -6 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((811877301077083471639443609560 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (49 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 1 else if k.val = 2 then 3 else -6) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 1 else if k.val = 2 then 3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180557850018427088000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (50 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((808497084789076486700589988053 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (51 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 0) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 2) else if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 2) else if j.val = 3 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559945169515648000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (52 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((809606773586689517385998719850 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (53 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -3) else if j.val = 1 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -4) else if j.val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -4) else if j.val = 3 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((904101392715791484866693310392 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (54 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else if j.val = 1 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -1 else if k.val = 2 then -7 else -1) else if j.val = 2 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((900199270264291755529499818451 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (55 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 6 else if k.val = 2 then -2 else 7) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else -1) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 6 else if k.val = 2 then -2 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147035098486360120508801025 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (56 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((711920765226528674414692795685 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (57 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((769499588009452763230169921478 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (58 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else -8) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -2) else if j.val = 3 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -2) else if j.val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -1 else if k.val = 2 then -6 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((809613051837585436886761574279 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (59 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -3) else if j.val = 1 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -4) else if j.val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -4) else if j.val = 3 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((900553977589347009069508420834 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (60 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -7) else if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else -5) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693146832004325337769191326700 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (61 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else 8) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((555861117124767761723585701433 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (62 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else 5) else if j.val = 1 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else 3) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else 3) else if j.val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((812598407739909718941214269880 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (63 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -7 else if k.val = 2 then -5 else 3) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -7 else if k.val = 2 then -5 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((911273294943225870210586493818 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (64 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (26 : Int) else if k.val = 1 then -8 else if k.val = 2 then -8 else 1) else if j.val = 1 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 2 else if k.val = 2 then -4 else 8) else if j.val = 2 then (if k.val = 0 then (26 : Int) else if k.val = 1 then -8 else if k.val = 2 then -8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559934353608332000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (65 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((809334046260627355902765110426 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (66 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -1) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -1) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -1) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559943320614016000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (67 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((811730108517287143723935714060 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (68 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (19 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -8) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (19 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((904173537277117988515101760103 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (69 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -3 else -6) else if j.val = 1 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -4) else if j.val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((908308807483168200389391263148 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (70 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 4) else if j.val = 1 then (if k.val = 0 then (35 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else -8) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559945176706832000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (71 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559945229850832000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (72 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((712047937852289715885666312985 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (73 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 3 then (if k.val = 0 then (36 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -8) else if j.val = 4 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((769485884848233496374812645712 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (74 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 0) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -2) else if j.val = 3 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -2) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((812699318882261418586821284031 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (75 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else 3) else if j.val = 1 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 6) else if j.val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 6) else if j.val = 3 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((908834842071177326249467244559 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (76 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 5 else 2) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 6) else if j.val = 2 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147126156656193543936308395 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (77 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((555860243632069264890026838967 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (78 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else -6) else if j.val = 1 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else 3) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else 3) else if j.val = 4 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((812616744654764801123986716370 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (79 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else -5) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((911391161240935185140221050852 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (80 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else 1) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else 5) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559945024280236000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (81 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((809263012016830707453111634956 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (82 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 6 else if k.val = 2 then 0 else -6) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -1) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -1) else if j.val = 3 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 6 else if k.val = 2 then 0 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559945273176832000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (83 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((810301755187771029935204828691 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (84 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 2 else if k.val = 2 then -2 else -6) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else -2) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else -2) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 2 else if k.val = 2 then -2 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((904069347799499958805262237154 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (85 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else if j.val = 1 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -1 else if k.val = 2 then -7 else -1) else if j.val = 2 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((900150591845555583510334824602 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (86 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else 4) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -7 else 2) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147033294038099932950429760 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (87 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) :=
  ⟨L3C.cr_4_44, L3C.cr_4_45, L3C.cr_4_46, L3C.cr_4_47, L3C.cr_4_48, L3C.cr_4_49, L3C.cr_4_50, L3C.cr_4_51, L3C.cr_4_52, L3C.cr_4_53, L3C.cr_4_54, L3C.cr_4_55, L3C.cr_4_56, L3C.cr_4_57, L3C.cr_4_58, L3C.cr_4_59, L3C.cr_4_60, L3C.cr_4_61, L3C.cr_4_62, L3C.cr_4_63, L3C.cr_4_64, L3C.cr_4_65, L3C.cr_4_66, L3C.cr_4_67, L3C.cr_4_68, L3C.cr_4_69, L3C.cr_4_70, L3C.cr_4_71, L3C.cr_4_72, L3C.cr_4_73, L3C.cr_4_74, L3C.cr_4_75, L3C.cr_4_76, L3C.cr_4_77, L3C.cr_4_78, L3C.cr_4_79, L3C.cr_4_80, L3C.cr_4_81, L3C.cr_4_82, L3C.cr_4_83, L3C.cr_4_84, L3C.cr_4_85, L3C.cr_4_86, L3C.cr_4_87⟩

-- Prove2me | solution 1 for mme_released_recursive_level3_penalty6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T07:39:41.899607+00:00
-- url     : https://prove2.me/submissions/0c970271-4c20-4228-82e2-91a2515c8143

import Mathlib
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_certified_generic_rate_data
import Definitions.Def_mme_certified_entropy_rational_data
open BigOperators MME MME.RecursiveYZ MME.RecStage MME.Cert MME.RegionRate
  MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace L3C

theorem pn_0_84 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (84 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -4 else if k.val = 2 then 5 else 4) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 3 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -4 else if k.val = 2 then 5 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -2) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -2) else if j.val = 3 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (84 : Fin 88)), (alphaG (n3 0) (m3 0) (84 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -4 else if k.val = 2 then 5 else 4) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 3 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -4 else if k.val = 2 then 5 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -2) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -2) else if j.val = 3 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (864660157221114527612213 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (84 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (84 : Fin 88)))) =
        {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (84 : Fin 88) = 22620795235393111106080000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (84 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 37122360148084480951506694098880000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (84 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((820536143 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (84 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 249698334638928332901895261040480000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (84 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((11038441931 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (84 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 274384148769962737503651756136000000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (84 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((242594609 : ℚ)/20000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (84 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 7096314761948121234902153901770240000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (84 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((19606723283 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (84 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 3652878066096813812722576152743040000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (84 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((40370796297 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (84 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 3652878200577441487134621678388640000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (84 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((161483191133 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 0 (84 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 7096315281298959044292591786260960000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 0) (m3 0) (84 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((313707595487 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 0 (84 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 274384056522359767570544665541760000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 0) (m3 0) (84 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((3032431593 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 0 (84 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 249697765952136115119082054189280000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 0) (m3 0) (84 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((11038416791 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 0 (84 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 37122259440304092981376049830720000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 0) (m3 0) (84 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((820533917 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_85 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (85 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 6 else if k.val = 2 then 6 else 0) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 3 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 6 else if k.val = 2 then 6 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -2) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -2) else if j.val = 3 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else -6) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (85 : Fin 88)), (alphaG (n3 0) (m3 0) (85 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 6 else if k.val = 2 then 6 else 0) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 3 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 6 else if k.val = 2 then 6 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -2) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -2) else if j.val = 3 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else -6) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3207622933714578931909069 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (85 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (85 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (85 : Fin 88) = 30605083537277768597728000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (85 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 328366499102913884839434360044672000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (85 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((2682287231 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (85 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 46051833337825784939892097367744000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (85 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((752355949 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (85 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 5002160884504327097755802595907744000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (85 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((163442157523 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (85 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 9572834248423010994483673111153440000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (85 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((62557151571 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (85 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 353128767611133964423503000255616000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (85 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((2884559743 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (85 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 353126797072225333257094066940608000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (85 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((5769087293 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 0 (85 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 9572837675855711250683700602114432000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 0) (m3 0) (85 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((78196467461 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 0 (85 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 5002160787088346198600665149339520000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 0) (m3 0) (85 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((8172107717 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 0 (85 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 46051310786629469459271059759872000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 0) (m3 0) (85 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((188086853 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 0 (85 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 328364733495644619284963957116352000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 0) (m3 0) (85 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((5364545617 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_86 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (86 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else 0) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 0) else if j.val = 1 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 1) else if j.val = 2 then (if k.val = 0 then (-37 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else 4) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 1) else if j.val = 4 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (86 : Fin 88)), (alphaG (n3 0) (m3 0) (86 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else 0) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 0) else if j.val = 1 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 1) else if j.val = 2 then (if k.val = 0 then (-37 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else 4) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 1) else if j.val = 4 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (122888741227564042452 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (86 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (86 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (86 : Fin 88) = 32938786922516743302419000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (86 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 403102256086526220601595356016109000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (86 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((12237920511 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (86 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 10672472700715639630395089053158000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (86 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((162004641 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (86 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 13992692909717786558598425027945962000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (86 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((212404496599 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (86 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2062925966465270575319635555438868000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (86 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((15657270343 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (86 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 2062926003126140420080770851031215000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (86 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((12525816497 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (86 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 13992692619527073771225916533634572000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (86 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((106202246097 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 0 (86 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 10672154017952164280903638149333000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 0) (m3 0) (86 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((323999607 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 0 (86 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 403102540875277952681357948730783000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 0) (m3 0) (86 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((12237929157 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_87 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (87 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (-40 : Int) else if k.val = 1 then 8 else if k.val = 2 then 8 else 2) else if j.val = 3 then (if k.val = 0 then (46 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -8) else if j.val = 4 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -8) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 4) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (87 : Fin 88)), (alphaG (n3 0) (m3 0) (87 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (-40 : Int) else if k.val = 1 then 8 else if k.val = 2 then 8 else 2) else if j.val = 3 then (if k.val = 0 then (46 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -8) else if j.val = 4 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -8) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 4) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2647371288251910612293 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (87 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (87 : Fin 88)))) =
        {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (87 : Fin 88) = 109625649474791310308000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (87 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 12526845331011209270134608701176000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (87 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((57134645911 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (87 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 42236732463111494686479286464888000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (87 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((192640739943 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (87 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 42344666125756146585350739283896000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (87 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((193133022831 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (87 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 12517405554912459766035365550040000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (87 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((11418318263 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    (((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (84 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -4 else if k.val = 2 then 5 else 4) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 3 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -4 else if k.val = 2 then 5 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -2) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -2) else if j.val = 3 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (84 : Fin 88)), (alphaG (n3 0) (m3 0) (84 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -4 else if k.val = 2 then 5 else 4) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 3 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -4 else if k.val = 2 then 5 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -2) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -2) else if j.val = 3 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (864660157221114527612213 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (85 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 6 else if k.val = 2 then 6 else 0) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 3 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 6 else if k.val = 2 then 6 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -2) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -2) else if j.val = 3 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else -6) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (85 : Fin 88)), (alphaG (n3 0) (m3 0) (85 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 6 else if k.val = 2 then 6 else 0) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 3 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 6 else if k.val = 2 then 6 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -2) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -2) else if j.val = 3 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else -6) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3207622933714578931909069 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (86 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else 0) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 0) else if j.val = 1 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 1) else if j.val = 2 then (if k.val = 0 then (-37 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else 4) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 1) else if j.val = 4 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (86 : Fin 88)), (alphaG (n3 0) (m3 0) (86 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else 0) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 0) else if j.val = 1 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 1) else if j.val = 2 then (if k.val = 0 then (-37 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else 4) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 1) else if j.val = 4 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (122888741227564042452 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (87 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (-40 : Int) else if k.val = 1 then 8 else if k.val = 2 then 8 else 2) else if j.val = 3 then (if k.val = 0 then (46 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -8) else if j.val = 4 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -8) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 4) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (87 : Fin 88)), (alphaG (n3 0) (m3 0) (87 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (-40 : Int) else if k.val = 1 then 8 else if k.val = 2 then 8 else 2) else if j.val = 3 then (if k.val = 0 then (46 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -8) else if j.val = 4 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -8) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 4) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2647371288251910612293 : ℚ)/10^30) :=
  ⟨L3C.pn_0_84, L3C.pn_0_85, L3C.pn_0_86, L3C.pn_0_87⟩

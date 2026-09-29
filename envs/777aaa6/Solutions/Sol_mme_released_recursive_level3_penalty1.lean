-- Prove2me | solution 1 for mme_released_recursive_level3_penalty1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T07:31:16.968308+00:00
-- url     : https://prove2.me/submissions/3c30a03b-3521-4532-8a23-58c8ccc12eca

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

theorem pn_0_4 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (4 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then -8 else if k.val = 2 then 6 else 7) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 6) else if j.val = 4 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (4 : Fin 88)), (alphaG (n3 0) (m3 0) (4 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then -8 else if k.val = 2 then 6 else 7) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 6) else if j.val = 4 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (7109219312118849430876 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (4 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (4 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (4 : Fin 88) = 110289097036677861328000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (4 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 42233259771939349756983244934640000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (4 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((76586463951 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (4 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12929884813283465690121159721280000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (4 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((5861814613 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (4 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 12888924077578375172578388186576000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (4 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((116864898017 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (4 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 42237028373876670708317207157504000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (4 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((23935405623 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_5 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (5 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -2 else if k.val = 2 then 7 else 0) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else -6) else if j.val = 2 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 4 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (5 : Fin 88)), (alphaG (n3 0) (m3 0) (5 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -2 else if k.val = 2 then 7 else 0) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else -6) else if j.val = 2 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 4 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1806477837867133455433 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (5 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (5 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (5 : Fin 88) = 3445987995162632557134000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (5 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 22769876618123125379954783815314000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (5 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((6607648271 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (5 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 594264993923508506213109752125764000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (5 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((86225633223 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (5 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 1105958954237170641548563254017358000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (5 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((320941035137 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (5 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1105959690031419344664192118383306000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (5 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((320941248659 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (5 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 594265278300221819014198897051980000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (5 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((17245134897 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (5 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 22769202052189120313981194606278000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (5 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((6607452517 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_6 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (6 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else -1) else if j.val = 1 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else 0) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 4) else if j.val = 2 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -6 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -6 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (6 : Fin 88)), (alphaG (n3 0) (m3 0) (6 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else -1) else if j.val = 1 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else 0) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 4) else if j.val = 2 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -6 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -6 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5715345147168321087093 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (6 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (6 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (6 : Fin 88) = 34686765484393209730085000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (6 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 11115953511264751815360698780095000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (6 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((320466707 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (6 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1258263852140056166164876084824495000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (6 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((36275041347 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (6 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 5089353588284937194948175710269155000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (6 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((146723210343 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (6 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 1273176321319421211654765984115120000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (6 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((2294059967 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (6 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 19422945983190223023725281614109040000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (6 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((34997040139 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (6 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 1273176185173866685411417793531495000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (6 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((36704955547 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 0 (6 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 5089353611975998020788737955917210000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 0) (m3 0) (6 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((73361605513 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 0 (6 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 1258263721509697351940048241324385000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 0) (m3 0) (6 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((36275037581 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 0 (6 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 11116267287745323636335917129005000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 0) (m3 0) (6 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((320475753 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_7 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (7 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 2) else if j.val = 1 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else -3) else if j.val = 2 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else -6) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else -6) else if j.val = 4 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else 4) else if j.val = 1 then (if k.val = 0 then (36 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else -8) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (7 : Fin 88)), (alphaG (n3 0) (m3 0) (7 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 2) else if j.val = 1 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else -3) else if j.val = 2 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else -6) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else -6) else if j.val = 4 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else 4) else if j.val = 1 then (if k.val = 0 then (36 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else -8) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (4042033449649072882303 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (7 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (7 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (7 : Fin 88) = 8057439934147016710640000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (7 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 1163149584008208373076771074109600000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (7 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((14435721439 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (7 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 288350476815514090636618200953600000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (7 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((447335753 : ℚ)/12500000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (7 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 2648268692373135536012078695680000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (7 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((20542107 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (7 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 325490399620923203139708544140720000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (7 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((40396255173 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (7 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 4498163458236055877066057565429600000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (7 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((55826211489 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (7 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 325490082480087395113130813350320000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (7 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((40396215813 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 0 (7 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 2648107906159249632293617874480000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 0) (m3 0) (7 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((328653757 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 0 (7 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 288350625265787437361254077784960000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 0) (m3 0) (7 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((4473359833 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 0 (7 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 1163148931121907949078154027661040000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 0) (m3 0) (7 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((144357133361 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_8 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (8 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 4) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -2) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 4) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 4 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 5 else if k.val = 2 then -6 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (8 : Fin 88)), (alphaG (n3 0) (m3 0) (8 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 4) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -2) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 4) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 4 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 5 else if k.val = 2 then -6 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2144430482013711457001 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (8 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (8 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (8 : Fin 88) = 2051193866366244883624000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (8 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 359162102238141863809754555807000000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (8 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((1400792419 : ℚ)/8000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (8 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 14436377759529179924922818207776000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (8 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((1759509181 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (8 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 651998758837951813044205224564712000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (8 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((317863059913 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (8 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 651998413115379218612728824390384000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (8 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((158931445683 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (8 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 14436010604031875832553629046272000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (8 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((109966527 : ℚ)/15625000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (8 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 359162203811210932399834947983856000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (8 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((87549550947 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_9 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (9 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 6 else if k.val = 2 then -3 else 5) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 6 else if k.val = 2 then -3 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else 4) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 1) else if j.val = 2 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else -1) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 1) else if j.val = 4 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (9 : Fin 88)), (alphaG (n3 0) (m3 0) (9 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 6 else if k.val = 2 then -3 else 5) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 6 else if k.val = 2 then -3 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else 4) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 1) else if j.val = 2 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else -1) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 1) else if j.val = 4 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (11933690530745060755653 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (9 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (9 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (9 : Fin 88) = 1295593320304577826288000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (9 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 421123586253120421354932130368000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (9 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((81260759 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (9 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 15698297272218488962880812845408000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (9 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((6058342933 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (9 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 79703809547199171070987779754320000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (9 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((12303831503 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (9 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 551973410229800355620616100067472000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (9 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((426039098519 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (9 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 551973456031615415028051415000848000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (9 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((426039133871 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (9 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 79703860615601077516531958548416000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (9 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((15379799233 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 0 (9 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 15698237527228116437578931400576000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 0) (m3 0) (9 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((1514579969 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 0 (9 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 421125494662081229998070252592000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 0) (m3 0) (9 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((325044509 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_10 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (10 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 2 else if k.val = 2 then 3 else -2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 3 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 2 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (10 : Fin 88)), (alphaG (n3 0) (m3 0) (10 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 2 else if k.val = 2 then 3 else -2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 3 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 2 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (871454052861244718270106 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (10 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (10 : Fin 88)))) =
        {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (10 : Fin 88) = 36188731164822098624546000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (10 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 59347459428673995894512223964410000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (10 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((327988617 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (10 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 405695554574363444206180432745978000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (10 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((11210549293 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (10 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 431947172868151389776180315847964000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (10 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((5967978967 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (10 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 11353939940894675435998428598970444000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (10 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((156871207907 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (10 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 5843435408576930273579166879424146000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (10 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((161471132601 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (10 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 5843435645178854629186047686705894000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (10 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((161471139139 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 0 (10 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 11353940629493852040233321226831732000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 0) (m3 0) (10 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((156871217421 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 0 (10 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 431947153398614023101891255842216000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 0) (m3 0) (10 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((2983989349 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 0 (10 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 405694851246373255888693664694468000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 0) (m3 0) (10 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((5605264929 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 0 (10 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 59347349161610136681577714972748000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 0) (m3 0) (10 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((819970019 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_11 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (11 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else 5) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 4 else -1) else if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (11 : Fin 88)), (alphaG (n3 0) (m3 0) (11 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else 5) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 4 else -1) else if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3349469266002474352819743 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (11 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (11 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (11 : Fin 88) = 35228386754955218842465000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (11 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 383380203950267546772561108892140000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (11 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((2720676699 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (11 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 53685184946316437912387735047820000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (11 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((380979587 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (11 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 5757537255138914302160139395405025000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (11 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((32686919757 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (11 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 11013776801537986414286219550262255000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (11 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((312639261007 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (11 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 405816124025718933944639901619850000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (11 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((1151957729 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (11 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 405814191502106717366199860517345000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (11 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((11519522433 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 0 (11 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 11013780645095894926920416138563615000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 0) (m3 0) (11 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((312639370111 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 0 (11 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 5757533631406139140446508384085265000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 0) (m3 0) (11 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((163434495921 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 0 (11 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 53684614915790355981991645121655000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 0) (m3 0) (11 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((1523902167 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 0 (11 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 383378102436084066673936280485030000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 0) (m3 0) (11 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((5441323571 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_12 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (12 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 3) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 6 else if k.val = 2 then -4 else 2) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else 8) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 0 else if k.val = 2 then -3 else 1) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else 8) else if j.val = 4 then (if k.val = 0 then (38 : Int) else if k.val = 1 then -7 else if k.val = 2 then -5 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (12 : Fin 88)), (alphaG (n3 0) (m3 0) (12 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 3) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 6 else if k.val = 2 then -4 else 2) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else 8) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 0 else if k.val = 2 then -3 else 1) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else 8) else if j.val = 4 then (if k.val = 0 then (38 : Int) else if k.val = 1 then -7 else if k.val = 2 then -5 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1972207062608914998541 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (12 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (12 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (12 : Fin 88) = 32510439714784868825464000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (12 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 403170476997083183884306027116032000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (12 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((193769717 : ℚ)/15625000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (12 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 10670846749961598937723471336768000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (12 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((41028539 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (12 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 13810102459632799349410791609956512000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (12 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((106197444427 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (12 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2031276283997520398294646635262664000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (12 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((62480738551 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (12 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 2031276095762074449690256135826104000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (12 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((62480732761 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (12 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 13810101944667434267218469414606752000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (12 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((106197440467 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 0 (12 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 10670505975532508562728442823120000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 0) (m3 0) (12 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((32821783 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 0 (12 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 403171101002463069465078263072048000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 0) (m3 0) (12 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((6200640541 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_13 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (13 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else 5) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 1) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 2 else if k.val = 2 then -2 else 6) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (13 : Fin 88)), (alphaG (n3 0) (m3 0) (13 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else 5) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 1) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 2 else if k.val = 2 then -2 else 6) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (10819062260817313423183 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (13 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (13 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (13 : Fin 88) = 27740228017858073490550000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (13 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 9326662454473660392296764487000000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (13 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((16810717 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (13 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1147664572299404114472817416262150000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (13 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((41371850713 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (13 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 1067713936866566051365972363357700000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (13 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((19244865907 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (13 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 3967065442787406052788912481101800000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (13 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((35751918119 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (13 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 15356690044080729347976345330719700000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (13 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((276794589327 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (13 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 3967063200517035141302974166454750000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (13 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((28601518329 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 0 (13 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 1067714795648545028216211483804600000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 0) (m3 0) (13 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((9622440693 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 0 (13 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 1147664837412763281142425765448500000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 0) (m3 0) (13 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((4137186027 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 0 (13 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 9324525791150812892044228363800000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 0) (m3 0) (13 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((84034329 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_14 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (14 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (14 : Fin 88)), (alphaG (n3 0) (m3 0) (14 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2312565321027765191235 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (14 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (14 : Fin 88)))) =
        {(⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (14 : Fin 88) = 931693031558138297864000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (14 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 6815634388454909541011912634808000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (14 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((7315321847 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (14 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 164910819478586510298746127977288000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (14 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((177001237417 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (14 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 294120106522421773127461799414088000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (14 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((315683488617 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (14 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 294120115586863277156589299332944000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (14 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((157841749173 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (14 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 164910724822301276118127618186344000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (14 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((177001135821 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (14 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 6815630759510551622063242454528000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (14 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((114301843 : ℚ)/15625000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_15 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (15 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (15 : Fin 88)), (alphaG (n3 0) (m3 0) (15 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1450461200091686510238 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (15 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (15 : Fin 88)))) =
        {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (15 : Fin 88) = 110814156364102961487000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (15 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 13134544937910074193763208818446000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (15 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((59263840329 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (15 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 42272533775606100471974594473206000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (15 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((190736162069 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (15 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 42272533776270985410159212242128000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (15 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((23842020259 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (15 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 13134543874315801411102984466220000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (15 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((5926383553 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_16 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (16 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else 4) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -1) else if j.val = 4 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (16 : Fin 88)), (alphaG (n3 0) (m3 0) (16 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else 4) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -1) else if j.val = 4 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (4055120999378668650485 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (16 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (16 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (16 : Fin 88) = 110627947222325545200000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (16 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 12969161259524315308381230658800000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (16 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((117232232769 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (16 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 42344780793910232651033745589200000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (16 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((382767481971 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (16 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 42344788700600248577862786578400000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (16 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((191383776721 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (16 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 12969216468290748662722237173600000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (16 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((58616365909 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_17 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (17 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -1) else if j.val = 1 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 1) else if j.val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else -6) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 4 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (17 : Fin 88)), (alphaG (n3 0) (m3 0) (17 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -1) else if j.val = 1 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 1) else if j.val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else -6) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 4 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (31919087163200583534222 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (17 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (17 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (17 : Fin 88) = 3550889743445516325670000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (17 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 25116734986833251167530770374350000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (17 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((1414672761 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (17 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1126346732501152385229792360992480000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (17 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((19825079309 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (17 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 623981427688399281895312199683520000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (17 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((5491417933 : ℚ)/31250000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (17 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 623981367465309233059355316320320000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (17 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((5491417403 : ℚ)/31250000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (17 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1126346805230476110480857743365420000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (17 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((158600644713 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (17 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 25116675573346063837151609263910000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (17 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((7073347073 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_18 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (18 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -2) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else -2) else if j.val = 1 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -3) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -1 else if k.val = 2 then 5 else 1) else if j.val = 3 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -3) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (18 : Fin 88)), (alphaG (n3 0) (m3 0) (18 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -2) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else -2) else if j.val = 1 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -3) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -1 else if k.val = 2 then 5 else 1) else if j.val = 3 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -3) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (493058573169950761293 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (18 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (18 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (18 : Fin 88) = 9234929677293873464436000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (18 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 3022437225740550120309218701968000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (18 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((81820797 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (18 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 602260155749074274234401197301884000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (18 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((65215456619 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (18 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 3896811972688817820299989885860708000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (18 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((421964444653 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (18 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 115370637190460700679081388562408000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (18 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((6246427489 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (18 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 115369901166565420357366273013208000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (18 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((6246387639 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (18 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 3896812525750286334075483924003876000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (18 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((421964504541 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 0 (18 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 602259604312953383662628888899452000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 0) (m3 0) (18 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((65215396907 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 0 (18 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 3022443209974981006739223656496000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 0) (m3 0) (18 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((81820959 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_19 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (19 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 4) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else -8) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 2) else if j.val = 4 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (19 : Fin 88)), (alphaG (n3 0) (m3 0) (19 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 4) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else -8) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 2) else if j.val = 4 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (7133785681944554038732 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (19 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (19 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (19 : Fin 88) = 109587035889638380852000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (19 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 42225732411294633876876286099532000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (19 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((385316858591 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (19 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12609890218661330411585645924732000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (19 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((115067353691 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (19 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 12517906321713335421257821192596000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (19 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((114227985273 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (19 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 42233506937969081142280246783140000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (19 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((77077560489 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    (((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (4 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then -8 else if k.val = 2 then 6 else 7) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 6) else if j.val = 4 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (4 : Fin 88)), (alphaG (n3 0) (m3 0) (4 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then -8 else if k.val = 2 then 6 else 7) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 6) else if j.val = 4 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (7109219312118849430876 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (5 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -2 else if k.val = 2 then 7 else 0) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else -6) else if j.val = 2 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 4 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (5 : Fin 88)), (alphaG (n3 0) (m3 0) (5 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -2 else if k.val = 2 then 7 else 0) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else -6) else if j.val = 2 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 4 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1806477837867133455433 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (6 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else -1) else if j.val = 1 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else 0) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 4) else if j.val = 2 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -6 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -6 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (6 : Fin 88)), (alphaG (n3 0) (m3 0) (6 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else -1) else if j.val = 1 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else 0) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 4) else if j.val = 2 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -6 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -6 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5715345147168321087093 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (7 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 2) else if j.val = 1 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else -3) else if j.val = 2 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else -6) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else -6) else if j.val = 4 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else 4) else if j.val = 1 then (if k.val = 0 then (36 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else -8) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (7 : Fin 88)), (alphaG (n3 0) (m3 0) (7 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 2) else if j.val = 1 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else -3) else if j.val = 2 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else -6) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else -6) else if j.val = 4 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else 4) else if j.val = 1 then (if k.val = 0 then (36 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else -8) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (4042033449649072882303 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (8 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 4) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -2) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 4) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 4 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 5 else if k.val = 2 then -6 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (8 : Fin 88)), (alphaG (n3 0) (m3 0) (8 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 4) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -2) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 4) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 4 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 5 else if k.val = 2 then -6 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2144430482013711457001 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (9 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 6 else if k.val = 2 then -3 else 5) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 6 else if k.val = 2 then -3 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else 4) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 1) else if j.val = 2 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else -1) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 1) else if j.val = 4 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (9 : Fin 88)), (alphaG (n3 0) (m3 0) (9 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 6 else if k.val = 2 then -3 else 5) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 6 else if k.val = 2 then -3 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else 4) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 1) else if j.val = 2 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else -1) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 1) else if j.val = 4 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (11933690530745060755653 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (10 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 2 else if k.val = 2 then 3 else -2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 3 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 2 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (10 : Fin 88)), (alphaG (n3 0) (m3 0) (10 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 2 else if k.val = 2 then 3 else -2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 3 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 2 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (871454052861244718270106 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (11 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else 5) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 4 else -1) else if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (11 : Fin 88)), (alphaG (n3 0) (m3 0) (11 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else 5) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 4 else -1) else if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3349469266002474352819743 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (12 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 3) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 6 else if k.val = 2 then -4 else 2) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else 8) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 0 else if k.val = 2 then -3 else 1) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else 8) else if j.val = 4 then (if k.val = 0 then (38 : Int) else if k.val = 1 then -7 else if k.val = 2 then -5 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (12 : Fin 88)), (alphaG (n3 0) (m3 0) (12 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 3) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 6 else if k.val = 2 then -4 else 2) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else 8) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 0 else if k.val = 2 then -3 else 1) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else 8) else if j.val = 4 then (if k.val = 0 then (38 : Int) else if k.val = 1 then -7 else if k.val = 2 then -5 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1972207062608914998541 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (13 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else 5) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 1) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 2 else if k.val = 2 then -2 else 6) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (13 : Fin 88)), (alphaG (n3 0) (m3 0) (13 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else 5) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 1) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 2 else if k.val = 2 then -2 else 6) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (10819062260817313423183 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (14 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (14 : Fin 88)), (alphaG (n3 0) (m3 0) (14 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2312565321027765191235 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (15 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (15 : Fin 88)), (alphaG (n3 0) (m3 0) (15 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1450461200091686510238 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (16 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else 4) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -1) else if j.val = 4 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (16 : Fin 88)), (alphaG (n3 0) (m3 0) (16 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else 4) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -1) else if j.val = 4 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (4055120999378668650485 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (17 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -1) else if j.val = 1 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 1) else if j.val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else -6) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 4 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (17 : Fin 88)), (alphaG (n3 0) (m3 0) (17 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -1) else if j.val = 1 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 1) else if j.val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else -6) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 4 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (31919087163200583534222 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (18 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -2) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else -2) else if j.val = 1 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -3) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -1 else if k.val = 2 then 5 else 1) else if j.val = 3 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -3) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (18 : Fin 88)), (alphaG (n3 0) (m3 0) (18 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -2) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else -2) else if j.val = 1 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -3) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -1 else if k.val = 2 then 5 else 1) else if j.val = 3 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -3) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (493058573169950761293 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (19 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 4) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else -8) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 2) else if j.val = 4 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (19 : Fin 88)), (alphaG (n3 0) (m3 0) (19 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 4) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else -8) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 2) else if j.val = 4 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (7133785681944554038732 : ℚ)/10^30) :=
  ⟨L3C.pn_0_4, L3C.pn_0_5, L3C.pn_0_6, L3C.pn_0_7, L3C.pn_0_8, L3C.pn_0_9, L3C.pn_0_10, L3C.pn_0_11, L3C.pn_0_12, L3C.pn_0_13, L3C.pn_0_14, L3C.pn_0_15, L3C.pn_0_16, L3C.pn_0_17, L3C.pn_0_18, L3C.pn_0_19⟩

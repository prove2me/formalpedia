-- Prove2me | solution 1 for mme_released_recursive_level3_penalty32
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T09:45:57.363977+00:00
-- url     : https://prove2.me/submissions/c41d56b2-12fe-4653-822e-3470acfa98fc

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

theorem pn_5_16 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (16 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 5) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -8 else if k.val = 2 then 1 else 4) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 2) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (16 : Fin 88)), (alphaG (n3 5) (m3 5) (16 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 5) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -8 else if k.val = 2 then 1 else 4) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 2) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (4199130130780042712780 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (16 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (16 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (16 : Fin 88) = 109586382826684735904000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (16 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 42233501974528876656774883730144000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (16 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((385390053811 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (16 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12609882846681851936524838129984000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (16 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((57533986073 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (16 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 12517872018232090347753344034880000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (16 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((11422835297 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (16 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 42225125987241916962946934104992000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (16 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((385313621073 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_17 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (17 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -8) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else -6) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -1) else if j.val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (17 : Fin 88)), (alphaG (n3 5) (m3 5) (17 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -8) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else -6) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -1) else if j.val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (26422551596231736066826 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (17 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (17 : Fin 88)))) =
        {(⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (17 : Fin 88) = 401802796822751075096000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (17 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 2873003004319276585676270750000000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (17 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((228809 : ℚ)/32000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (17 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 70643325891591322491581164874992000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (17 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((87907956901 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (17 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 127385078284810979127284778345208000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (17 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((317033826773 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (17 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 127385011703274926019672377412336000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (17 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((158516830533 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (17 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 70643292969879164819471826884232000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (17 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((175815831867 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (17 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 2873084968875406052313581733232000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (17 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((3575242621 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_18 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (18 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-52 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else 7) else if j.val = 1 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -1) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (-52 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 2) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 2) else if j.val = 2 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then 2 else -2) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 1 else if k.val = 2 then -7 else 5) else if j.val = 2 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then 2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (18 : Fin 88)), (alphaG (n3 5) (m3 5) (18 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-52 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else 7) else if j.val = 1 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -1) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (-52 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 2) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 2) else if j.val = 2 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then 2 else -2) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 1 else if k.val = 2 then -7 else 5) else if j.val = 2 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then 2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (976814212686926171792 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (18 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (18 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (18 : Fin 88) = 18064915803317425248780000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (18 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 5939245056052713138117263467140000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (18 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((328772363 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (18 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 717898640719203352540233968186160000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (18 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((9934984593 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (18 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 669515760801353186828204708497740000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (18 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((37061659633 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (18 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 2607035696740205042881405241690460000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (18 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((144314854557 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (18 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 10064137196494594677060462385427040000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (18 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((69638694321 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (18 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 2607035619639144394322634279897420000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (18 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((144314850289 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 5 (18 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 669515649991159649279118232481220000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 5) (m3 5) (18 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((37061653499 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 5 (18 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 717898524941157969078855548755140000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 5) (m3 5) (18 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((39739931963 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 5 (18 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 5939468934554263650968371597680000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 5) (m3 5) (18 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((82196189 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_19 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (19 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 7) else if j.val = 1 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 3 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then -2 else if k.val = 2 then 6 else 7) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (19 : Fin 88)), (alphaG (n3 5) (m3 5) (19 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 7) else if j.val = 1 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 3 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then -2 else if k.val = 2 then 6 else 7) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3312231898049162419646005 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (19 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (19 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (19 : Fin 88) = 35187280785783124345430000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (19 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 379629310398950929026469508586340000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (19 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((5394411019 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (19 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 52859860254014950807735288971140000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (19 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((751121699 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (19 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 5752595454289342480483766689499340000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (19 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((81742540569 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (19 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 11005479554557126899668490965521730000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (19 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((312768685411 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (19 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 403077249270485965397935152535220000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (19 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((5727598727 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (19 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 403072438113584125271343401891320000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (19 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((2863765181 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 5 (19 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 11005488404932364701411492576766190000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 5) (m3 5) (19 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((312768936933 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 5 (19 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 5752595345701393975557044959502360000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 5) (m3 5) (19 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((40871269513 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 5 (19 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 52858532321225376138405616788370000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 5) (m3 5) (19 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((1502205659 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 5 (19 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 379624635944634941667315839937990000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 5) (m3 5) (19 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((10788689193 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_20 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (20 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else -2) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 3 else if k.val = 2 then -4 else 5) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else -2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else 4) else if j.val = 1 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else 0) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (20 : Fin 88)), (alphaG (n3 5) (m3 5) (20 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else -2) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 3 else if k.val = 2 then -4 else 5) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else -2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else 4) else if j.val = 1 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else 0) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5372190693753135477095 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (20 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (20 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (20 : Fin 88) = 869510295952860162172000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (20 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 127077889260101432782994758011404000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (20 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((146148803357 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (20 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 29576883380627034319317233497428000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (20 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((34015564299 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (20 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 277284843939809965572599750464000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (20 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((19931107 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (20 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 32825419968611058408706267748996000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (20 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((37751617343 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (20 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 489995358864306475884828725212040000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (20 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((56353025507 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (20 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 32825393191171984244424713500084000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (20 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((37751586547 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 5 (20 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 277266990284903165494889872788000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 5) (m3 5) (20 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((318877179 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 5 (20 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 29576906845231880903201569871020000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 5) (m3 5) (20 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((6803118257 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 5 (20 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 127077892608585582497459242535776000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 5) (m3 5) (20 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((18268600901 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_21 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (21 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 3 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 8) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 3 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (21 : Fin 88)), (alphaG (n3 5) (m3 5) (21 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 3 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 8) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 3 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (887975818187850469141966 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (21 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (21 : Fin 88)))) =
        {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (21 : Fin 88) = 25776017261143089147688000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (21 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 42521382129868126315117927419520000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (21 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((20620613 : ℚ)/12500000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (21 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 286133786699678189762165890273800000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (21 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((444031029 : ℚ)/40000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (21 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 312555705742251248678916586509048000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (21 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((12125833971 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (21 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 8084253023708595050307483718269720000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (21 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((62726936763 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (21 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 4162544595214292164021367790123128000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (21 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((161489052131 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (21 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 4162544730203294560627725656565184000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (21 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((20186132171 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 5 (21 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 8084252326286896015558920649275504000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 5) (m3 5) (21 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((156817328379 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 5 (21 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 312556094238383408627556220462584000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 5) (m3 5) (21 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((12125849043 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 5 (21 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 286134127303970278506945887823032000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 5) (m3 5) (21 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((11100788939 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 5 (21 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 42521489615860105281799673278480000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 5) (m3 5) (21 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((164965321 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_22 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (22 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -8) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else -5) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else -1) else if j.val = 2 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 8) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else -1) else if j.val = 4 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (22 : Fin 88)), (alphaG (n3 5) (m3 5) (22 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -8) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else -5) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else -1) else if j.val = 2 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 8) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else -1) else if j.val = 4 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (685928244451897818526 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (22 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (22 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (22 : Fin 88) = 6001867832152358351808000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (22 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 1973076070000445948033229758976000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (22 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((41092959 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (22 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 76328956634410802831079596594688000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (22 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((1589691717 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (22 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 406713601442829800044432646104896000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (22 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((67764504787 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (22 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 2515918226039544874077693555505344000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (22 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((419189208493 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (22 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 2515918389206323758971707707757632000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (22 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((419189235679 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (22 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 406713753182052332520356496514752000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (22 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((67764530069 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 5 (22 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 76328756370086847403338471817152000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 5) (m3 5) (22 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((12717500369 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 5 (22 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 1973073207109490011358295946560000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 5) (m3 5) (22 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((65748639 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_23 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (23 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 5 else if k.val = 2 then -3 else -5) else if j.val = 1 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -7 else if k.val = 2 then 7 else 5) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -7 else if k.val = 2 then 7 else 5) else if j.val = 4 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 5 else if k.val = 2 then -3 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (23 : Fin 88)), (alphaG (n3 5) (m3 5) (23 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 5 else if k.val = 2 then -3 else -5) else if j.val = 1 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -7 else if k.val = 2 then 7 else 5) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -7 else if k.val = 2 then 7 else 5) else if j.val = 4 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 5 else if k.val = 2 then -3 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (6761316728577792053219 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (23 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (23 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (23 : Fin 88) = 10542882298557265212720000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (23 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 3465696774935535277738265670240000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (23 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((164361921 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (23 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 715051991032195467415733436230880000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (23 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((33911598877 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (23 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 4418887391748084824199115573373520000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (23 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((419134660391 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (23 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 134036230122828069717645671047440000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (23 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((12713433227 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (23 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 134035940583651504439471134118080000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (23 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((3178351441 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (23 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 4418887547540256549979823621736960000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (23 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((13097958599 : ℚ)/31250000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 5 (23 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 715051804834351192595872514382960000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 5) (m3 5) (23 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((67823180093 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 5 (23 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 3465695920962069094599783439920000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 5) (m3 5) (23 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((328723761 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_24 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (24 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 5) else if j.val = 1 then (if k.val = 0 then (-47 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else 8) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 4 else if k.val = 2 then -2 else 0) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 4 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 4 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (24 : Fin 88)), (alphaG (n3 5) (m3 5) (24 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 5) else if j.val = 1 then (if k.val = 0 then (-47 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else 8) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 4 else if k.val = 2 then -2 else 0) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 4 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 4 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (11361489068929764913962 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (24 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (24 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (24 : Fin 88) = 2790334194060608310558000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (24 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 20512878007119181952672590362216000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (24 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((1837851363 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (24 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 493543968543551035953946400947392000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (24 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((5527384157 : ℚ)/31250000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (24 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 881110275840981427189249943352054000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (24 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((315772310613 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (24 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 881110096570380461377347814932228000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (24 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((157886123183 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (24 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 493543907234328124054260601367016000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (24 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((44219067763 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (24 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 20513067864248080030522649039094000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (24 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((7351473493 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_25 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (25 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else -1) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else -5) else if j.val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 2 else if k.val = 2 then -6 else 8) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 4 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 2 else if k.val = 2 then -6 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (25 : Fin 88)), (alphaG (n3 5) (m3 5) (25 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else -1) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else -5) else if j.val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 2 else if k.val = 2 then -6 else 8) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 4 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 2 else if k.val = 2 then -6 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (4142792599906142382639 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (25 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (25 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (25 : Fin 88) = 3219520559390971939995000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (25 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 23728439323711787242535854210425000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (25 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((1474035583 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (25 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1015214872924657875478431597434400000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (25 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((1970819207 : ℚ)/6250000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (25 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 570816948957409734694180696963890000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (25 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((88649371611 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (25 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 570816975144989964780346456883220000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (25 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((44324687839 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (25 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1015214831067671082836405405559405000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (25 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((315331060119 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (25 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 23728491972531494963099988948660000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (25 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((1842548567 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_26 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (26 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 2) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 0) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (26 : Fin 88)), (alphaG (n3 5) (m3 5) (26 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 2) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 0) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (8746938273520238993846 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (26 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (26 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (26 : Fin 88) = 111390253316595542817000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (26 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 13247055975524597915719953261141000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (26 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((118924731573 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (26 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 42448070436043762396520919399204000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (26 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((95268816553 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (26 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 42448070384915636124203565246201000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (26 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((381075265753 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (26 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 13247056520111546380555562093454000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (26 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((59462368231 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_27 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (27 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (46 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -8) else if j.val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (27 : Fin 88)), (alphaG (n3 5) (m3 5) (27 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (46 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -8) else if j.val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1123313961669751951879 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (27 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (27 : Fin 88)))) =
        {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (27 : Fin 88) = 109720629107465120480000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (27 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 12530722486673830543630132122880000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (27 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((14275713907 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (27 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 42329470135840250119671059898880000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (27 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((24112073591 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (27 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 42329920988328712459060298664480000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (27 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((385797286551 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (27 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 12530515496622327357638509313760000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (27 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((114203824737 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_28 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (28 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 7) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 3 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else 7) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else -1) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -4 else if k.val = 2 then -4 else 8) else if j.val = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else -1) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (28 : Fin 88)), (alphaG (n3 5) (m3 5) (28 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 7) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 3 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else 7) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else -1) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -4 else if k.val = 2 then -4 else 8) else if j.val = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else -1) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (6271539611496447904151 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (28 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (28 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (28 : Fin 88) = 30222456606114226140648000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (28 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 374322875047936484304194370117528000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (28 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((12385587311 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (28 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 9811778141177274770276397275088000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (28 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((162325953 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (28 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 12751942444573365712869837752151696000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (28 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((210967999901 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (28 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 1975150472672063009564735605007520000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (28 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((3267686837 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (28 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 1975149159234321364446581758586088000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (28 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((65353693281 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (28 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 12751942960621812262270249103716296000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (28 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((421936016877 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 5 (28 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 9813615001644881180712773579232000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 5) (m3 5) (28 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((81178171 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 5 (28 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 374323300821905151241412239566552000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 5) (m3 5) (28 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((12385601399 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_29 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (29 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else 3) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else 3) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 6) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 4 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (29 : Fin 88)), (alphaG (n3 5) (m3 5) (29 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else 3) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else 3) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 6) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 4 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5899236817733165037946 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (29 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (29 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (29 : Fin 88) = 1780957557734798198000000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (29 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 313638495525485554740333349332000000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (29 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((88053332367 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (29 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12927045419192447654050427320000000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (29 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((362924017 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (29 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 563913200381916737113805007706000000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (29 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((316634833847 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (29 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 563913252214905497427371762298000000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (29 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((316634862951 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (29 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 12927065243031022800089169258000000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (29 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((7258491471 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (29 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 313638498950266938264350284086000000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (29 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((176106666657 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_30 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (30 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 7 else if k.val = 2 then 1 else -1) else if j.val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (30 : Fin 88)), (alphaG (n3 5) (m3 5) (30 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 7 else if k.val = 2 then 1 else -1) else if j.val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (243961782093100247206 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (30 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (30 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (30 : Fin 88) = 110855712458535710645000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (30 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 42279032968794341029069833301865000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (30 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((381387950437 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (30 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 13149761650753804424464705303785000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (30 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((118620514533 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (30 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 13148055461282330967283704125250000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (30 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((2372102469 : ℚ)/20000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (30 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 42278862377705234224181757269100000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (30 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((19069320579 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_31 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (31 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -6) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 3 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else 1) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 3 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else 4) else if j.val = 1 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else -8) else if j.val = 2 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (31 : Fin 88)), (alphaG (n3 5) (m3 5) (31 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -6) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 3 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else 1) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 3 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else 4) else if j.val = 1 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else -8) else if j.val = 2 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3154127575729367351812739 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (31 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (31 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (31 : Fin 88) = 28049849959666960445535000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (31 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 300964287700789180783880465344095000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (31 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((10729622017 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (31 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 42603902288216455429761152489235000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (31 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((1518863821 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (31 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 4582500525184863657060452909149785000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (31 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((163369876551 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (31 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 8772270882330896567092785353944500000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (31 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((3127386027 : ℚ)/10000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (31 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 326586001725501171766440677376255000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (31 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((11643056993 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (31 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 326582470866487948808793714321525000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (31 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((2328586223 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 5 (31 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 8772278257618195712125030100689725000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 5) (m3 5) (31 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((62547773127 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 5 (31 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 4582500810003040147518769273112175000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 5) (m3 5) (31 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((32673977341 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 5 (31 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 42602799620564690961879078062850000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 5) (m3 5) (31 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((151882451 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 5 (31 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 300960022328404913987207275509855000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 5) (m3 5) (31 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((10729469953 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    (((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (16 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 5) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -8 else if k.val = 2 then 1 else 4) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 2) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (16 : Fin 88)), (alphaG (n3 5) (m3 5) (16 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 5) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -8 else if k.val = 2 then 1 else 4) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 2) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (4199130130780042712780 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (17 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -8) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else -6) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -1) else if j.val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (17 : Fin 88)), (alphaG (n3 5) (m3 5) (17 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -8) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else -6) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -1) else if j.val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (26422551596231736066826 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (18 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-52 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else 7) else if j.val = 1 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -1) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (-52 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 2) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 2) else if j.val = 2 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then 2 else -2) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 1 else if k.val = 2 then -7 else 5) else if j.val = 2 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then 2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (18 : Fin 88)), (alphaG (n3 5) (m3 5) (18 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-52 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else 7) else if j.val = 1 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -1) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (-52 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 2) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 2) else if j.val = 2 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then 2 else -2) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 1 else if k.val = 2 then -7 else 5) else if j.val = 2 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then 2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (976814212686926171792 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (19 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 7) else if j.val = 1 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 3 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then -2 else if k.val = 2 then 6 else 7) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (19 : Fin 88)), (alphaG (n3 5) (m3 5) (19 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 7) else if j.val = 1 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 3 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then -2 else if k.val = 2 then 6 else 7) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3312231898049162419646005 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (20 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else -2) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 3 else if k.val = 2 then -4 else 5) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else -2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else 4) else if j.val = 1 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else 0) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (20 : Fin 88)), (alphaG (n3 5) (m3 5) (20 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else -2) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 3 else if k.val = 2 then -4 else 5) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else -2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else 4) else if j.val = 1 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else 0) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5372190693753135477095 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (21 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 3 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 8) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 3 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (21 : Fin 88)), (alphaG (n3 5) (m3 5) (21 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 3 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 8) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 3 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (887975818187850469141966 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (22 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -8) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else -5) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else -1) else if j.val = 2 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 8) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else -1) else if j.val = 4 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (22 : Fin 88)), (alphaG (n3 5) (m3 5) (22 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -8) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else -5) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else -1) else if j.val = 2 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 8) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else -1) else if j.val = 4 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (685928244451897818526 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (23 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 5 else if k.val = 2 then -3 else -5) else if j.val = 1 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -7 else if k.val = 2 then 7 else 5) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -7 else if k.val = 2 then 7 else 5) else if j.val = 4 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 5 else if k.val = 2 then -3 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (23 : Fin 88)), (alphaG (n3 5) (m3 5) (23 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 5 else if k.val = 2 then -3 else -5) else if j.val = 1 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -7 else if k.val = 2 then 7 else 5) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -7 else if k.val = 2 then 7 else 5) else if j.val = 4 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 5 else if k.val = 2 then -3 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (6761316728577792053219 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (24 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 5) else if j.val = 1 then (if k.val = 0 then (-47 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else 8) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 4 else if k.val = 2 then -2 else 0) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 4 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 4 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (24 : Fin 88)), (alphaG (n3 5) (m3 5) (24 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 5) else if j.val = 1 then (if k.val = 0 then (-47 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else 8) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 4 else if k.val = 2 then -2 else 0) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 4 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 4 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (11361489068929764913962 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (25 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else -1) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else -5) else if j.val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 2 else if k.val = 2 then -6 else 8) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 4 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 2 else if k.val = 2 then -6 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (25 : Fin 88)), (alphaG (n3 5) (m3 5) (25 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else -1) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else -5) else if j.val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 2 else if k.val = 2 then -6 else 8) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 4 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 2 else if k.val = 2 then -6 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (4142792599906142382639 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (26 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 2) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 0) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (26 : Fin 88)), (alphaG (n3 5) (m3 5) (26 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 2) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 0) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (8746938273520238993846 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (27 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (46 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -8) else if j.val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (27 : Fin 88)), (alphaG (n3 5) (m3 5) (27 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (46 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -8) else if j.val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1123313961669751951879 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (28 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 7) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 3 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else 7) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else -1) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -4 else if k.val = 2 then -4 else 8) else if j.val = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else -1) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (28 : Fin 88)), (alphaG (n3 5) (m3 5) (28 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 7) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 3 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else 7) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else -1) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -4 else if k.val = 2 then -4 else 8) else if j.val = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else -1) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (6271539611496447904151 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (29 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else 3) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else 3) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 6) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 4 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (29 : Fin 88)), (alphaG (n3 5) (m3 5) (29 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else 3) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else 3) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 6) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 4 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5899236817733165037946 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (30 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 7 else if k.val = 2 then 1 else -1) else if j.val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (30 : Fin 88)), (alphaG (n3 5) (m3 5) (30 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 7 else if k.val = 2 then 1 else -1) else if j.val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (243961782093100247206 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (31 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -6) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 3 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else 1) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 3 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else 4) else if j.val = 1 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else -8) else if j.val = 2 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (31 : Fin 88)), (alphaG (n3 5) (m3 5) (31 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -6) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 3 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else 1) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 3 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else 4) else if j.val = 1 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else -8) else if j.val = 2 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3154127575729367351812739 : ℚ)/10^30) :=
  ⟨L3C.pn_5_16, L3C.pn_5_17, L3C.pn_5_18, L3C.pn_5_19, L3C.pn_5_20, L3C.pn_5_21, L3C.pn_5_22, L3C.pn_5_23, L3C.pn_5_24, L3C.pn_5_25, L3C.pn_5_26, L3C.pn_5_27, L3C.pn_5_28, L3C.pn_5_29, L3C.pn_5_30, L3C.pn_5_31⟩

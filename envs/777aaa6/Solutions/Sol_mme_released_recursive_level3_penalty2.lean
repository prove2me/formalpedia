-- Prove2me | solution 1 for mme_released_recursive_level3_penalty2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T07:31:06.53164+00:00
-- url     : https://prove2.me/submissions/b574e569-702e-4f50-a531-129946de7fe2

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

theorem pn_0_20 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (20 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -2) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else -1) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else -5) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else if j.val = 4 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (20 : Fin 88)), (alphaG (n3 0) (m3 0) (20 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -2) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else -1) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else -5) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else if j.val = 4 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (9485010423235182174560 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (20 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (20 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (20 : Fin 88) = 3153282838362126620496000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (20 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 22289810037020143986898545422256000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (20 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((7068763311 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (20 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 552690285349079756729476980604944000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (20 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((175274567389 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (20 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 1001661218658207012861598693395168000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (20 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((158828317979 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (20 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1001661702233049972723888706179744000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (20 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((158828394657 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (20 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 552690487651093534690072445146320000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (20 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((35054926309 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (20 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 22289334433676199504064629251568000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (20 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((7068612483 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_21 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (21 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 8 else if k.val = 2 then -6 else 6) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else 2) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 8 else if k.val = 2 then -6 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else 2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 1) else if j.val = 2 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 6) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 4) else if j.val = 3 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 4 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -5 else if k.val = 2 then -4 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (21 : Fin 88)), (alphaG (n3 0) (m3 0) (21 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 8 else if k.val = 2 then -6 else 6) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else 2) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 8 else if k.val = 2 then -6 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else 2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 1) else if j.val = 2 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 6) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 4) else if j.val = 3 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 4 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -5 else if k.val = 2 then -4 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1758481726260946848902 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (21 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (21 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (21 : Fin 88) = 10333369434714134371866000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (21 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 3445615052174608461129728825298000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (21 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((333445453 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (21 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 398212907218410799184533819608852000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (21 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((19268299161 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (21 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 1493140082237423281334823835550742000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (21 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((144496922487 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (21 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 403078231543914164255473653354990000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (21 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((7801486903 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (21 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 5737615740145543514325549800883552000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (21 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((34703199767 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (21 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 403078208738167821841379094646728000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (21 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((9751858077 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 0 (21 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 1493140108711515773072436096271434000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 0) (m3 0) (21 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((144496925049 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 0 (21 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 398212893888364228403300479901712000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 0) (m3 0) (21 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((4817074629 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 0 (21 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 3445647178620180987373490956692000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 0) (m3 0) (21 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((166724281 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_22 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (22 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -4 else if k.val = 2 then 7 else -8) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else -6) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -4 else if k.val = 2 then 7 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else -2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -4) else if j.val = 1 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 8) else if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (22 : Fin 88)), (alphaG (n3 0) (m3 0) (22 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -4 else if k.val = 2 then 7 else -8) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else -6) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -4 else if k.val = 2 then 7 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else -2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -4) else if j.val = 1 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 8) else if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (34219054551755236272143 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (22 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (22 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (22 : Fin 88) = 1002792490205440204608000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (22 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 146557362872336624851543578442752000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (22 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((9134327659 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (22 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 34093878286420165099298577602112000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (22 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((33998936589 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (22 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 319791294268354868822128134336000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (22 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((318900767 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (22 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 37875105251781869630288616898752000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (22 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((37769633919 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (22 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 565100245025005792951089165752256000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (22 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((563526602507 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (22 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 37875060156203585091642615676992000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (22 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((37769588949 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 0 (22 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 319761125256287038153572502656000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 0) (m3 0) (22 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((159435341 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 0 (22 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 34093918793220014457850202537664000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 0) (m3 0) (22 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((33998976983 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 0 (22 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 146557367400947510619311542452480000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 0) (m3 0) (22 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((7307462353 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_23 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (23 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 0) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -3) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (23 : Fin 88)), (alphaG (n3 0) (m3 0) (23 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 0) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -3) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3609723500062575406674 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (23 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (23 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (23 : Fin 88) = 2338402430621028675848000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (23 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 402820228545801322113284499108400000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (23 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((3445260091 : ℚ)/20000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (23 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 15513928137358028863685757785592000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (23 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((6634413279 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (23 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 750867178075289545499795534097696000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (23 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((80275658313 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (23 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 750867044634354842110794146831576000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (23 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((321102576187 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (23 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 15513790433515694452549094448568000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (23 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((6634354391 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (23 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 402820260794709242807890967728168000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (23 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((172263018341 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_24 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (24 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 1) else if j.val = 1 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else if j.val = 2 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else -2) else if j.val = 1 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else 1) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else 4) else if j.val = 3 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else 1) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (24 : Fin 88)), (alphaG (n3 0) (m3 0) (24 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 1) else if j.val = 1 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else if j.val = 2 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else -2) else if j.val = 1 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else 1) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else 4) else if j.val = 3 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else 1) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2483813668030671069116 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (24 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (24 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (24 : Fin 88) = 4668877469698821833048000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (24 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 1533683281116709333898938459256000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (24 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((328490797 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (24 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 58524431560857491092014083459520000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (24 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((313375281 : ℚ)/25000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (24 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 304342084522379635917705007811568000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (24 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((32592639933 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (24 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1970038518840508900704082135453536000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (24 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((105487803633 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (24 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 1970038555892720500233932202522464000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (24 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((105487805617 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (24 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 304342140240763359303444763406400000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (24 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((325926459 : ℚ)/5000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 0 (24 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 58524367485183096945383246708768000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 0) (m3 0) (24 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((3133749379 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 0 (24 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 1533687875292139517539622178488000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 0) (m3 0) (24 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((328491781 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_25 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (25 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 3 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (25 : Fin 88)), (alphaG (n3 0) (m3 0) (25 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 3 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (912113129039625577719805 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (25 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (25 : Fin 88)))) =
        {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (25 : Fin 88) = 33270232565701371597524000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (25 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 54865223816748201562529874537992000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (25 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((824539229 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (25 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 372709057887439683681679741363864000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (25 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((5601239143 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (25 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 399642027557292781237510028848156000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (25 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((12011999819 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (25 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 10435344513760948918872600558385872000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (25 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((78413522457 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (25 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 5372555462090632027875373065495748000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (25 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((161482353677 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (25 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 5372555675219741843758359519234492000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (25 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((161482360083 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 0 (25 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 10435345457703987272951915523336800000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 0) (m3 0) (25 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((1568270591 : ℚ)/5000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 0 (25 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 399641709660220615960904414506336000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 0) (m3 0) (25 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((1501498783 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 0 (25 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 372708365600440456567539540084472000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 0) (m3 0) (25 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((5601228739 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 0 (25 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 54865072403919795055587734206268000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 0) (m3 0) (25 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((1649073907 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_26 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (26 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 1) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 3 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 0 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -6) else if j.val = 1 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 3 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (26 : Fin 88)), (alphaG (n3 0) (m3 0) (26 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 1) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 3 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 0 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -6) else if j.val = 1 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 3 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3393086173175966099275570 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (26 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (26 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (26 : Fin 88) = 37848003636402927281490000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (26 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 411745150441296198852757823068920000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (26 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((2719728327 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (26 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 57286381359537175817256072267810000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (26 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((1513590569 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (26 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 6186722232091578958873537180810470000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (26 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((163462313403 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (26 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 11835163610502614555517838538799480000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (26 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((78175613463 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (26 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 433085045778934588672168797151770000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (26 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((11442744773 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (26 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 433082684858315753493967905087060000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (26 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((5721341197 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 0 (26 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 11835167345419309403031508530795660000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 0) (m3 0) (26 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((156351276267 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 0 (26 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 6186721868599352034859823569380510000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 0) (m3 0) (26 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((163462303799 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 0 (26 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 57285819278835171597383014859820000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 0) (m3 0) (26 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((756787859 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 0 (26 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 411743498073153440773758567778500000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 0) (m3 0) (26 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((217577393 : ℚ)/20000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_27 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (27 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else -6) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else 8) else if j.val = 1 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 2) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 8 else -4) else if j.val = 3 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 2) else if j.val = 4 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (27 : Fin 88)), (alphaG (n3 0) (m3 0) (27 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else -6) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else 8) else if j.val = 1 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 2) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 8 else -4) else if j.val = 3 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 2) else if j.val = 4 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (383970811569885856166 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (27 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (27 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (27 : Fin 88) = 37992807395602638462230000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (27 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 463577215457466189036804913255050000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (27 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((2440341987 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (27 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12467940603115967267108054667450000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (27 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((65633163 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (27 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 16300680414035601913233813760561100000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (27 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((42904648357 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (27 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2219678015474382114967079254088980000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (27 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((29211818863 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (27 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 2219678338033316903633479798421680000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (27 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((7302955777 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (27 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 16300680726640421164252323027789540000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (27 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((214523245899 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 0 (27 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 12467799687793336976921998256380000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 0) (m3 0) (27 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((164081053 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 0 (27 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 463576945670540872862469192959820000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 0) (m3 0) (27 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((6100851417 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_28 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (28 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else 0) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else 5) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 4 then (if k.val = 0 then (-45 : Int) else if k.val = 1 then 2 else if k.val = 2 then 5 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 0 else if k.val = 2 then -3 else -3) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else 7) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (28 : Fin 88)), (alphaG (n3 0) (m3 0) (28 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else 0) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else 5) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 4 then (if k.val = 0 then (-45 : Int) else if k.val = 1 then 2 else if k.val = 2 then 5 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 0 else if k.val = 2 then -3 else -3) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else 7) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (6602112177027429407489 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (28 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (28 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (28 : Fin 88) = 27993824086544358005983000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (28 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 9410416194221525380264409906537000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (28 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((336160439 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (28 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1156829739182788597967513428310168000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (28 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((5165557837 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (28 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 1078803978919848940255412825100426000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (28 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((19268606811 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (28 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 4003338227934866813601987715358900000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (28 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((1430079083 : ℚ)/10000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (28 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 15497059558709526635460213876672530000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (28 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((55358851691 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (28 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 4003338106581639398432195759422595000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (28 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((28601580793 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 0 (28 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 1078805001254304580855367203599586000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 0) (m3 0) (28 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((19268625071 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 0 (28 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 1156830797853227902902044498575262000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 0) (m3 0) (28 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((20662250257 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 0 (28 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 9408259913933611128000283053996000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 0) (m3 0) (28 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((84020853 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_29 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (29 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else 8) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (29 : Fin 88)), (alphaG (n3 0) (m3 0) (29 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else 8) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3910417401079444199754 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (29 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (29 : Fin 88)))) =
        {(⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (29 : Fin 88) = 953174036668402816574000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (29 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 6971441871998008667398430100120000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (29 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((365696169 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (29 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 168676697396746538098111774528002000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (29 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((176963168223 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (29 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 300938871997671379625282910475668000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (29 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((157861450491 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (29 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 300938884119185603937361528847226000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (29 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((315722913699 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (29 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 168676702102566757130016479953840000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (29 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((4424079329 : ℚ)/25000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (29 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 6971439180234529115828876095144000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (29 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((1828480139 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_30 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (30 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (-43 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (30 : Fin 88)), (alphaG (n3 0) (m3 0) (30 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (-43 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (4867556686942296877547 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (30 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (30 : Fin 88)))) =
        {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (30 : Fin 88) = 110808742479067029870000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (30 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 13131997208640219606655337919540000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (30 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((59255239771 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (30 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 42274322007697651351954042658430000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (30 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((381507100089 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (30 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 42271378126128581723027935438590000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (30 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((381480532857 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (30 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 13131045136600577188362683983440000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (30 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((14812735939 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_31 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (31 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 5) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 2) else if j.val = 4 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (31 : Fin 88)), (alphaG (n3 0) (m3 0) (31 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 5) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 2) else if j.val = 4 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1742051129387794716899 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (31 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (31 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (31 : Fin 88) = 109633903025058746440000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (31 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 12569913524981816619547024533720000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (31 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((114653525763 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (31 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 42247067727388260693013828512880000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (31 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((192673372751 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (31 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 42246983159961555477649057061600000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (31 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((19267298707 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (31 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 12569938612727113649790089891800000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (31 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((22930750919 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_32 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (32 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else 2) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 5 else if k.val = 2 then -2 else -2) else if j.val = 2 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -4 else if k.val = 2 then -4 else -1) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 4 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -4 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (32 : Fin 88)), (alphaG (n3 0) (m3 0) (32 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else 2) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 5 else if k.val = 2 then -2 else -2) else if j.val = 2 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -4 else if k.val = 2 then -4 else -1) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 4 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -4 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5748896443997790208395 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (32 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (32 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (32 : Fin 88) = 3852690397987601220578000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (32 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 25402001391407620941655236070000000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (32 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((1318663 : ℚ)/200000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (32 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1234964526360466034756697507287822000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (32 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((320546007799 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (32 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 665978667963287425903198617930300000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (32 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((3457213527 : ℚ)/20000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (32 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 665978480606953371766151261222160000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (32 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((4321515693 : ℚ)/25000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (32 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1234965005958777537845247849719574000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (32 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((320546132283 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (32 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 25401715706709229365049527770144000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (32 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((412077553 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_33 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (33 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else 6) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 3 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else -4) else if j.val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 2 else if k.val = 2 then -4 else -5) else if j.val = 3 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else -4) else if j.val = 4 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (33 : Fin 88)), (alphaG (n3 0) (m3 0) (33 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else 6) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 3 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else -4) else if j.val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 2 else if k.val = 2 then -4 else -5) else if j.val = 3 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else -4) else if j.val = 4 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5510995653572335669120 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (33 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (33 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (33 : Fin 88) = 7148580403613912966538000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (33 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 2345485666740042064435508244186000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (33 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((328105097 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (33 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 438680222627075049119411415724056000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (33 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((15341515303 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (33 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 3045696201924673903901648222436666000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (33 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((426056088057 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (33 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 87568557522807083024681121775230000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (33 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((2449956567 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (33 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 87568038950487444064206703175634000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (33 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((12249710293 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (33 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 3045696581214052958848642401009870000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (33 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((85211228223 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 0 (33 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 438679842601392212600184201597438000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 0) (m3 0) (33 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((61366008051 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 0 (33 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2345473106684272914790426036920000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 0) (m3 0) (33 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((16405167 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_34 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (34 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 6 else if k.val = 2 then 5 else 6) else if j.val = 2 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else 4) else if j.val = 2 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (34 : Fin 88)), (alphaG (n3 0) (m3 0) (34 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 6 else if k.val = 2 then 5 else 6) else if j.val = 2 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else 4) else if j.val = 2 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1494533599642995786885 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (34 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (34 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (34 : Fin 88) = 1015726222663453773600000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (34 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 179828737690565408083315706551200000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (34 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((177044496517 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (34 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 320588817659999509054636807171200000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (34 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((78906306273 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (34 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 7445613414385503944377660716000000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (34 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((1466066987 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (34 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 7445472990235220721893460516000000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (34 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((1466039337 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (34 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 320588897220818804060307439485600000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (34 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((315625303421 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (34 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 179828683687449327735468925560000000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (34 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((3540888867 : ℚ)/20000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_35 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (35 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 7 else if k.val = 2 then 1 else -1) else if j.val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (35 : Fin 88)), (alphaG (n3 0) (m3 0) (35 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 7 else if k.val = 2 then 1 else -1) else if j.val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (251369180554975911595 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (35 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (35 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (35 : Fin 88) = 110855808232269478315000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (35 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 42278882093222561070450088417950000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (35 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((38138625993 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (35 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 13149778221817225416934536135210000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (35 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((59310280767 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (35 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 13148110227570686601351410443095000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (35 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((118605515013 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (35 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 42279037689659005226263965003745000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (35 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((381387663523 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    (((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (20 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -2) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else -1) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else -5) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else if j.val = 4 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (20 : Fin 88)), (alphaG (n3 0) (m3 0) (20 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -2) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else -1) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else -5) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else if j.val = 4 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (9485010423235182174560 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (21 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 8 else if k.val = 2 then -6 else 6) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else 2) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 8 else if k.val = 2 then -6 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else 2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 1) else if j.val = 2 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 6) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 4) else if j.val = 3 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 4 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -5 else if k.val = 2 then -4 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (21 : Fin 88)), (alphaG (n3 0) (m3 0) (21 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 8 else if k.val = 2 then -6 else 6) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else 2) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 8 else if k.val = 2 then -6 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else 2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 1) else if j.val = 2 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 6) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 4) else if j.val = 3 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 4 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -5 else if k.val = 2 then -4 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1758481726260946848902 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (22 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -4 else if k.val = 2 then 7 else -8) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else -6) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -4 else if k.val = 2 then 7 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else -2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -4) else if j.val = 1 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 8) else if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (22 : Fin 88)), (alphaG (n3 0) (m3 0) (22 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -4 else if k.val = 2 then 7 else -8) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else -6) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -4 else if k.val = 2 then 7 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else -2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -4) else if j.val = 1 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 8) else if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (34219054551755236272143 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (23 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 0) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -3) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (23 : Fin 88)), (alphaG (n3 0) (m3 0) (23 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 0) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -3) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3609723500062575406674 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (24 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 1) else if j.val = 1 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else if j.val = 2 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else -2) else if j.val = 1 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else 1) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else 4) else if j.val = 3 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else 1) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (24 : Fin 88)), (alphaG (n3 0) (m3 0) (24 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 1) else if j.val = 1 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else if j.val = 2 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else -2) else if j.val = 1 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else 1) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else 4) else if j.val = 3 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else 1) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2483813668030671069116 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (25 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 3 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (25 : Fin 88)), (alphaG (n3 0) (m3 0) (25 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 3 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (912113129039625577719805 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (26 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 1) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 3 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 0 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -6) else if j.val = 1 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 3 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (26 : Fin 88)), (alphaG (n3 0) (m3 0) (26 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 1) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 3 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 0 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -6) else if j.val = 1 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 3 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3393086173175966099275570 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (27 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else -6) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else 8) else if j.val = 1 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 2) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 8 else -4) else if j.val = 3 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 2) else if j.val = 4 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (27 : Fin 88)), (alphaG (n3 0) (m3 0) (27 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else -6) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else 8) else if j.val = 1 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 2) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 8 else -4) else if j.val = 3 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 2) else if j.val = 4 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (383970811569885856166 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (28 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else 0) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else 5) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 4 then (if k.val = 0 then (-45 : Int) else if k.val = 1 then 2 else if k.val = 2 then 5 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 0 else if k.val = 2 then -3 else -3) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else 7) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (28 : Fin 88)), (alphaG (n3 0) (m3 0) (28 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else 0) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else 5) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 4 then (if k.val = 0 then (-45 : Int) else if k.val = 1 then 2 else if k.val = 2 then 5 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 0 else if k.val = 2 then -3 else -3) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else 7) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (6602112177027429407489 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (29 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else 8) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (29 : Fin 88)), (alphaG (n3 0) (m3 0) (29 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else 8) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3910417401079444199754 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (30 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (-43 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (30 : Fin 88)), (alphaG (n3 0) (m3 0) (30 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (-43 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (4867556686942296877547 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (31 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 5) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 2) else if j.val = 4 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (31 : Fin 88)), (alphaG (n3 0) (m3 0) (31 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 5) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 2) else if j.val = 4 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1742051129387794716899 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (32 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else 2) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 5 else if k.val = 2 then -2 else -2) else if j.val = 2 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -4 else if k.val = 2 then -4 else -1) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 4 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -4 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (32 : Fin 88)), (alphaG (n3 0) (m3 0) (32 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else 2) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 5 else if k.val = 2 then -2 else -2) else if j.val = 2 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -4 else if k.val = 2 then -4 else -1) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 4 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -4 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5748896443997790208395 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (33 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else 6) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 3 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else -4) else if j.val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 2 else if k.val = 2 then -4 else -5) else if j.val = 3 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else -4) else if j.val = 4 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (33 : Fin 88)), (alphaG (n3 0) (m3 0) (33 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else 6) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 3 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else -4) else if j.val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 2 else if k.val = 2 then -4 else -5) else if j.val = 3 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else -4) else if j.val = 4 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5510995653572335669120 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (34 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 6 else if k.val = 2 then 5 else 6) else if j.val = 2 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else 4) else if j.val = 2 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (34 : Fin 88)), (alphaG (n3 0) (m3 0) (34 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 6 else if k.val = 2 then 5 else 6) else if j.val = 2 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else 4) else if j.val = 2 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1494533599642995786885 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (35 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 7 else if k.val = 2 then 1 else -1) else if j.val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (35 : Fin 88)), (alphaG (n3 0) (m3 0) (35 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 7 else if k.val = 2 then 1 else -1) else if j.val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (251369180554975911595 : ℚ)/10^30) :=
  ⟨L3C.pn_0_20, L3C.pn_0_21, L3C.pn_0_22, L3C.pn_0_23, L3C.pn_0_24, L3C.pn_0_25, L3C.pn_0_26, L3C.pn_0_27, L3C.pn_0_28, L3C.pn_0_29, L3C.pn_0_30, L3C.pn_0_31, L3C.pn_0_32, L3C.pn_0_33, L3C.pn_0_34, L3C.pn_0_35⟩

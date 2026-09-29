-- Prove2me | solution 1 for mme_released_recursive_level3_penalty16
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T08:24:28.378629+00:00
-- url     : https://prove2.me/submissions/edb7ae24-5c3e-4ee8-b3a0-c98bfbd1705c

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

theorem pn_2_48 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (48 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 1) else if j.val = 1 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else if j.val = 2 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else -2) else if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -6) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else 4) else if j.val = 3 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -6) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (48 : Fin 88)), (alphaG (n3 2) (m3 2) (48 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 1) else if j.val = 1 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else if j.val = 2 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else -2) else if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -6) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else 4) else if j.val = 3 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -6) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3023164483350443953218 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (48 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (48 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (48 : Fin 88) = 4387867945939366084525000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (48 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 1441431373120899355266173216450000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (48 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((164251909 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (48 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 55001111599704495683409849925825000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (48 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((12534814693 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (48 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 286032536218204611258741208056075000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (48 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((65187134103 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (48 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1851458852681881854296980021140500000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (48 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((21097476901 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (48 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 1851458999605252156130713995375600000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (48 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((26371848219 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (48 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 286032719661799827145819103792750000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (48 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((6518717591 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 2 (48 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 55000899893851840000875003763625000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 2) (m3 2) (48 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((2506953289 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 2 (48 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 1441394905550400653194644729175000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 2) (m3 2) (48 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((328495507 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_49 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (49 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else -2) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else 5) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (49 : Fin 88)), (alphaG (n3 2) (m3 2) (49 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else -2) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else 5) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3449163574223239518631 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (49 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (49 : Fin 88)))) =
        {(⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (49 : Fin 88) = 902095366513904370935000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (49 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 6601277251429551179792225218110000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (49 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((3658857753 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (49 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 159627764609211167731009423693310000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (49 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((88476102713 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (49 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 284818666610779055986839423092765000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (49 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((315730107019 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (49 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 284818591102690592673501862720460000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (49 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((78932505829 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (49 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 159627756705953661702693229931775000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (49 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((35390439333 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (49 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 6601310233840341661163835343580000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (49 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((1829438017 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_50 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (50 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 3 then (if k.val = 0 then (35 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -8) else if j.val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (50 : Fin 88)), (alphaG (n3 2) (m3 2) (50 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 3 then (if k.val = 0 then (35 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -8) else if j.val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5484109548630232447839 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (50 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (50 : Fin 88)))) =
        {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (50 : Fin 88) = 110803976065474319230000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (50 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 13136650803733902684397246387760000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (50 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((14819696989 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (50 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 42263449386094717767972546387380000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (50 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((190712693203 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (50 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 42263758110348910913830271397980000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (50 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((190714086313 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (50 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 13140117765296787863799935826880000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (50 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((3705902033 : ℚ)/31250000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_51 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (51 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -1) else if j.val = 1 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 1) else if j.val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 6 else if k.val = 2 then -1 else 8) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 6 else if k.val = 2 then -8 else -7) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 6 else if k.val = 2 then -8 else -7) else if j.val = 4 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 6 else if k.val = 2 then -1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (51 : Fin 88)), (alphaG (n3 2) (m3 2) (51 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -1) else if j.val = 1 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 1) else if j.val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 6 else if k.val = 2 then -1 else 8) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 6 else if k.val = 2 then -8 else -7) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 6 else if k.val = 2 then -8 else -7) else if j.val = 4 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 6 else if k.val = 2 then -1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (40522031754152501405531 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (51 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (51 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (51 : Fin 88) = 3597717083863414277051000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (51 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 25427755680538174895379341783032000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (51 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((883468429 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (51 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1141192623416201938622127619845456000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (51 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((19824943791 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (51 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 632238191426024690470546298095809000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (51 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((175733159859 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (51 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 632237987978721315078332345138810000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (51 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((17573310331 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (51 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1141193229203402236627687003969887000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (51 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((317199269037 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (51 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 25427296158525921356927391167006000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (51 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((3533809853 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_52 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (52 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 8 else if k.val = 2 then -6 else 6) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else 2) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 8 else if k.val = 2 then -6 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 0) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 1) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else 8) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 4) else if j.val = 3 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 4 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (52 : Fin 88)), (alphaG (n3 2) (m3 2) (52 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 8 else if k.val = 2 then -6 else 6) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else 2) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 8 else if k.val = 2 then -6 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 0) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 1) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else 8) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 4) else if j.val = 3 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 4 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3211929163315778541012 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (52 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (52 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (52 : Fin 88) = 10365072552239755133655000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (52 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 3455965277387274802372441827840000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (52 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((651219 : ℚ)/1953125000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (52 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 399395249356956054463173328232580000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (52 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((9633199559 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (52 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 1497735241375338247860057710920095000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (52 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((144498288249 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (52 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 404347625206500515654952292500405000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (52 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((39010592851 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (52 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 5755204472354828754131298337466580000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (52 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((138812450259 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (52 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 404347664179173312076431595043205000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (52 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((39010596611 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 2 (52 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 1497735112039962941012393153173005000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 2) (m3 2) (52 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((144498275771 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 2 (52 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 399395252279906514194784275923290000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 2) (m3 2) (52 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((19266399259 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 2 (52 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 3455970169701519459536864913000000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 2) (m3 2) (52 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((1667123 : ℚ)/5000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_53 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (53 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 1) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 3 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (53 : Fin 88)), (alphaG (n3 2) (m3 2) (53 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 1) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 3 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (912170821467077854416301 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (53 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (53 : Fin 88)))) =
        {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (53 : Fin 88) = 33449169484642678123384000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (53 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 55155476146457568788329206871016000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (53 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((1648934099 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (53 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 374664249618144582728048529061504000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (53 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((700062691 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (53 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 401823863790670801657327653257952000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (53 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((3003242457 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (53 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 10491412793218466794347749153386992000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (53 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((156826207569 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (53 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 5401525096213175222946225061956112000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (53 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((80742290159 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (53 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 5401525211980750809294534046988136000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (53 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((161484583779 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 2 (53 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 10491386367036607147246324555091632000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 2) (m3 2) (53 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((156825812549 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 2 (53 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 401837916857144723554972986824640000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 2) (m3 2) (53 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((300334749 : ℚ)/25000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 2 (53 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 374678804689754130143007138375264000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 2) (m3 2) (53 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((2800359549 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 2 (53 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 55159705091506342677481668186752000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 2) (m3 2) (53 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((103066283 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_54 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (54 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-40 : Int) else if k.val = 1 then 3 else if k.val = 2 then 7 else 3) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else 5) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 3 else if k.val = 2 then -4 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else -6) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else 7) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (54 : Fin 88)), (alphaG (n3 2) (m3 2) (54 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-40 : Int) else if k.val = 1 then 3 else if k.val = 2 then 7 else 3) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else 5) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 3 else if k.val = 2 then -4 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else -6) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else 7) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (42803157972925832545183 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (54 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (54 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (54 : Fin 88) = 27645452286518544907756000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (54 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 9287621951499643866479466904704000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (54 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((10498587 : ℚ)/31250000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (54 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1142351423572168746105564368062616000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (54 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((20660747593 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (54 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 1065389814384165385100661437996084000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (54 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((38537615639 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (54 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 3953576848562758514976203377375128000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (54 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((71505012969 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (54 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 15304240718218509058969149329358836000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (54 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((553589811431 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (54 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 3953577183432122061575337845023556000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (54 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((143010038051 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 2 (54 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 1065390400605981120726406206962064000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 2) (m3 2) (54 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((9634409211 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 2 (54 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 1142352143183291764183288316951296000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 2) (m3 2) (54 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((645648769 : ℚ)/15625000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 2 (54 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 9286132608048612252909651365716000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 2) (m3 2) (54 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((335900911 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_55 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (55 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else -1) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else -2) else if j.val = 1 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -3) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -1 else if k.val = 2 then 5 else 1) else if j.val = 3 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -3) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (55 : Fin 88)), (alphaG (n3 2) (m3 2) (55 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else -1) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else -2) else if j.val = 1 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -3) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -1 else if k.val = 2 then 5 else 1) else if j.val = 3 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -3) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (887947342923922542550 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (55 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (55 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (55 : Fin 88) = 9195576949172513149155000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (55 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 3009748924664844311148251987745000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (55 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((327303979 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (55 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 599686045643828575036961235290340000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (55 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((16303654707 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (55 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 3880210410322970288001074284335750000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (55 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((8439297353 : ℚ)/20000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (55 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 114882227588246016967378518405420000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (55 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((3123301241 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (55 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 114882312647332796813125148089170000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (55 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((6246607107 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (55 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 3880210345199894333961336162020040000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (55 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((52745607571 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 2 (55 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 599686108596748369071986254405470000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 2) (m3 2) (55 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((32607312837 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 2 (55 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 3009750248827924991990145466065000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 2) (m3 2) (55 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((327304123 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_56 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (56 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-44 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else 8) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 3 then (if k.val = 0 then (-44 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -6) else if j.val = 1 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 3 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (56 : Fin 88)), (alphaG (n3 2) (m3 2) (56 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-44 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else 8) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 3 then (if k.val = 0 then (-44 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -6) else if j.val = 1 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 3 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3394601208902130670060568 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (56 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (56 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (56 : Fin 88) = 38142841962791472127125000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (56 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 414905872551292105100168713184625000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (56 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((10877686381 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (56 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 57723711710008518441517904722500000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (56 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((75667817 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (56 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 6234977424658231649454074651419500000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (56 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((40865973167 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (56 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 11927370045891470825943717182834250000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (56 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((156351354961 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (56 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 436443950424009191367691627292250000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (56 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((5721177657 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (56 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 436443413906794142742844687152000000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (56 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((89393291 : ℚ)/7812500000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 2 (56 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 11927371246475564446768093856220750000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 2) (m3 2) (56 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((156351370699 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 2 (56 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 6234977564833175862712734718603875000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 2) (m3 2) (56 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((163463896343 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 2 (56 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 57723539914648318028727444151500000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 2) (m3 2) (56 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((378337959 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 2 (56 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 414905192426277066565429214418750000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 2) (m3 2) (56 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((217553371 : ℚ)/20000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_57 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (57 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else -5) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 3 else if k.val = 2 then -4 else 5) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else -1) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else -7) else if j.val = 1 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -8) else if j.val = 2 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (57 : Fin 88)), (alphaG (n3 2) (m3 2) (57 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else -5) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 3 else if k.val = 2 then -4 else 5) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else -1) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else -7) else if j.val = 1 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -8) else if j.val = 2 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (12162392130558938746956 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (57 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (57 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (57 : Fin 88) = 1030478265515958914250000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (57 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 150609145101357362786200030749750000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (57 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((146154606207 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (57 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 35045836939524345784194985089750000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (57 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((34009292687 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (57 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 328640557117308071571518328000000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (57 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((9966263 : ℚ)/31250000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (57 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 38904479591239799193574823222250000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (57 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((37753808977 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (57 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 580702074195701863197148646596500000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (57 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((281763378049 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (57 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 38904476888295308745214591144500000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (57 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((18876903177 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 2 (57 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 328627647285597687638240604000000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 2) (m3 2) (57 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((19931743 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 2 (57 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 35045839649682184091166929567250000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 2) (m3 2) (57 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((34009295317 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 2 (57 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 150609144945755144693290234698000000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 2) (m3 2) (57 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((18269325757 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_58 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (58 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 5 else if k.val = 2 then 6 else 1) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 5 else if k.val = 2 then 6 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 6 else if k.val = 2 then -4 else -8) else if j.val = 1 then (if k.val = 0 then (24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 8 else -4) else if j.val = 3 then (if k.val = 0 then (24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (58 : Fin 88)), (alphaG (n3 2) (m3 2) (58 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 5 else if k.val = 2 then 6 else 1) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 5 else if k.val = 2 then 6 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 6 else if k.val = 2 then -4 else -8) else if j.val = 1 then (if k.val = 0 then (24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 8 else -4) else if j.val = 3 then (if k.val = 0 then (24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (418274027664518502439 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (58 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (58 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (58 : Fin 88) = 38035970983486911204704000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (58 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 464051055050758393210555664322848000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (58 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((12200320987 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (58 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12483633588318537310955791386368000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (58 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((41025749 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (58 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 16319305520381881996642034764586688000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (58 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((214524634161 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (58 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2222144901183671739831247485318272000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (58 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((14605548667 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (58 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 2222145355827632905450297115145184000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (58 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((58422206621 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (58 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 16319306435375199975403170704946112000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (58 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((214524646189 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 2 (58 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 12483824909252584250119151047488000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 2) (m3 2) (58 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((164105511 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 2 (58 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 464050257170195072605619323247040000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 2) (m3 2) (58 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((1220030001 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_59 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (59 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 0) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -3) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (59 : Fin 88)), (alphaG (n3 2) (m3 2) (59 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 0) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -3) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3116461227583235684562 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (59 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (59 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (59 : Fin 88) = 2327957928531225148713000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (59 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 401013269017007567450017040536386000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (59 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((86129835961 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (59 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 15444550081735449916322977653252000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (59 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((1658594201 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (59 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 747520273451383428830246920483947000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (59 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((321105576819 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (59 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 747521356037954639205596402531328000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (59 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((313580119 : ℚ)/976562500) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (59 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 15445641910299636560636300091243000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (59 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((6634845811 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (59 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 401012838032844426750180358703844000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (59 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((43064871697 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_60 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (60 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else 0) else if j.val = 3 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -1) else if j.val = 4 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (60 : Fin 88)), (alphaG (n3 2) (m3 2) (60 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else 0) else if j.val = 3 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -1) else if j.val = 4 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (10903004728515874921360 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (60 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (60 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (60 : Fin 88) = 109658439634580542040000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (60 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 42315769784271955479638586086680000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (60 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((385887031817 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (60 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12543070506986867221736146426160000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (60 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((57191541977 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (60 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 12529007727313069457428720292000000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (60 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((1142548423 : ℚ)/10000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (60 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 42270591616008649881196547195160000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (60 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((385475041929 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_61 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (61 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then -2 else if k.val = 2 then 7 else 6) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 3) else if j.val = 4 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (61 : Fin 88)), (alphaG (n3 2) (m3 2) (61 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then -2 else if k.val = 2 then 7 else 6) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 3) else if j.val = 4 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (9962183814745520688782 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (61 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (61 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (61 : Fin 88) = 111367461157590711288000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (61 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 13238754347593100608159147213056000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (61 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((3714828991 : ℚ)/31250000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (61 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 42447913659803217493072147920096000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (61 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((95287962073 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (61 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 42439212498457687466226618490224000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (61 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((190536859049 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (61 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 13241580651736705720542086376624000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (61 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((59449952949 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_62 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (62 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -6) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -3) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (62 : Fin 88)), (alphaG (n3 2) (m3 2) (62 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -6) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -3) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1610934345042879956294 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (62 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (62 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (62 : Fin 88) = 2827065221580752258364000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (62 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 20791668445484146342534336604040000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (62 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((735450611 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (62 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 500161660886284618076531048831832000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (62 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((88459519269 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (62 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 892579279821736601467679056971372000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (62 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((315726454773 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (62 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 892579255599441782963793707308620000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (62 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((63145289241 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (62 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 500161655664695153816881627633524000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (62 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((176919036691 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (62 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 20791701163109955696580222650612000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (62 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((7354517683 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_63 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (63 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else -3) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else -4) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else -4) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else 3) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (63 : Fin 88)), (alphaG (n3 2) (m3 2) (63 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else -3) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else -4) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else -4) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else 3) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (6391544557914451341676 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (63 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (63 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (63 : Fin 88) = 5929939676816393897659000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (63 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 1941563195552805807566876449157000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (63 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((327417023 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (63 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 75121812926498225486489437844297000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (63 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((12668225483 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (63 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 402028823880884051291199847236149000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (63 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((67796444111 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (63 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 2485877709149442210663823037542267000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (63 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((419207925313 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (63 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 2485877445765241525186871679120123000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (63 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((419207880897 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (63 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 402028497989189232492640413590486000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (63 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((33898194577 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 2 (63 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 75122212011438475229798750294997000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 2) (m3 2) (63 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((12668292783 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 2 (63 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 1941611898147371500609957922524000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 2) (m3 2) (63 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((81856309 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    (((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (48 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 1) else if j.val = 1 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else if j.val = 2 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else -2) else if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -6) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else 4) else if j.val = 3 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -6) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (48 : Fin 88)), (alphaG (n3 2) (m3 2) (48 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 1) else if j.val = 1 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else if j.val = 2 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else -2) else if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -6) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else 4) else if j.val = 3 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -6) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3023164483350443953218 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (49 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else -2) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else 5) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (49 : Fin 88)), (alphaG (n3 2) (m3 2) (49 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else -2) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else 5) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3449163574223239518631 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (50 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 3 then (if k.val = 0 then (35 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -8) else if j.val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (50 : Fin 88)), (alphaG (n3 2) (m3 2) (50 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 3 then (if k.val = 0 then (35 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -8) else if j.val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5484109548630232447839 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (51 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -1) else if j.val = 1 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 1) else if j.val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 6 else if k.val = 2 then -1 else 8) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 6 else if k.val = 2 then -8 else -7) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 6 else if k.val = 2 then -8 else -7) else if j.val = 4 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 6 else if k.val = 2 then -1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (51 : Fin 88)), (alphaG (n3 2) (m3 2) (51 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -1) else if j.val = 1 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 1) else if j.val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 6 else if k.val = 2 then -1 else 8) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 6 else if k.val = 2 then -8 else -7) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 6 else if k.val = 2 then -8 else -7) else if j.val = 4 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 6 else if k.val = 2 then -1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (40522031754152501405531 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (52 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 8 else if k.val = 2 then -6 else 6) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else 2) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 8 else if k.val = 2 then -6 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 0) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 1) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else 8) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 4) else if j.val = 3 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 4 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (52 : Fin 88)), (alphaG (n3 2) (m3 2) (52 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 8 else if k.val = 2 then -6 else 6) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else 2) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 8 else if k.val = 2 then -6 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 0) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 1) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else 8) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 4) else if j.val = 3 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 4 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3211929163315778541012 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (53 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 1) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 3 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (53 : Fin 88)), (alphaG (n3 2) (m3 2) (53 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 1) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 3 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (912170821467077854416301 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (54 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-40 : Int) else if k.val = 1 then 3 else if k.val = 2 then 7 else 3) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else 5) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 3 else if k.val = 2 then -4 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else -6) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else 7) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (54 : Fin 88)), (alphaG (n3 2) (m3 2) (54 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-40 : Int) else if k.val = 1 then 3 else if k.val = 2 then 7 else 3) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else 5) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 3 else if k.val = 2 then -4 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else -6) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else 7) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (42803157972925832545183 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (55 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else -1) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else -2) else if j.val = 1 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -3) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -1 else if k.val = 2 then 5 else 1) else if j.val = 3 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -3) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (55 : Fin 88)), (alphaG (n3 2) (m3 2) (55 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else -1) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else -2) else if j.val = 1 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -3) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -1 else if k.val = 2 then 5 else 1) else if j.val = 3 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -3) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (887947342923922542550 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (56 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-44 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else 8) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 3 then (if k.val = 0 then (-44 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -6) else if j.val = 1 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 3 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (56 : Fin 88)), (alphaG (n3 2) (m3 2) (56 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-44 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else 8) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 3 then (if k.val = 0 then (-44 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -6) else if j.val = 1 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 3 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3394601208902130670060568 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (57 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else -5) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 3 else if k.val = 2 then -4 else 5) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else -1) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else -7) else if j.val = 1 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -8) else if j.val = 2 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (57 : Fin 88)), (alphaG (n3 2) (m3 2) (57 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else -5) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 3 else if k.val = 2 then -4 else 5) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else -1) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else -7) else if j.val = 1 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -8) else if j.val = 2 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (12162392130558938746956 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (58 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 5 else if k.val = 2 then 6 else 1) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 5 else if k.val = 2 then 6 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 6 else if k.val = 2 then -4 else -8) else if j.val = 1 then (if k.val = 0 then (24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 8 else -4) else if j.val = 3 then (if k.val = 0 then (24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (58 : Fin 88)), (alphaG (n3 2) (m3 2) (58 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 5 else if k.val = 2 then 6 else 1) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 5 else if k.val = 2 then 6 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 6 else if k.val = 2 then -4 else -8) else if j.val = 1 then (if k.val = 0 then (24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 8 else -4) else if j.val = 3 then (if k.val = 0 then (24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (418274027664518502439 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (59 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 0) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -3) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (59 : Fin 88)), (alphaG (n3 2) (m3 2) (59 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 0) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -3) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3116461227583235684562 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (60 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else 0) else if j.val = 3 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -1) else if j.val = 4 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (60 : Fin 88)), (alphaG (n3 2) (m3 2) (60 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else 0) else if j.val = 3 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -1) else if j.val = 4 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (10903004728515874921360 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (61 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then -2 else if k.val = 2 then 7 else 6) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 3) else if j.val = 4 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (61 : Fin 88)), (alphaG (n3 2) (m3 2) (61 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then -2 else if k.val = 2 then 7 else 6) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 3) else if j.val = 4 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (9962183814745520688782 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (62 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -6) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -3) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (62 : Fin 88)), (alphaG (n3 2) (m3 2) (62 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -6) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -3) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1610934345042879956294 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (63 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else -3) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else -4) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else -4) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else 3) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (63 : Fin 88)), (alphaG (n3 2) (m3 2) (63 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else -3) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else -4) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else -4) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else 3) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (6391544557914451341676 : ℚ)/10^30) :=
  ⟨L3C.pn_2_48, L3C.pn_2_49, L3C.pn_2_50, L3C.pn_2_51, L3C.pn_2_52, L3C.pn_2_53, L3C.pn_2_54, L3C.pn_2_55, L3C.pn_2_56, L3C.pn_2_57, L3C.pn_2_58, L3C.pn_2_59, L3C.pn_2_60, L3C.pn_2_61, L3C.pn_2_62, L3C.pn_2_63⟩

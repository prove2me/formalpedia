-- Prove2me | solution 1 for mme_released_recursive_level3_penalty8
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T07:54:07.038557+00:00
-- url     : https://prove2.me/submissions/2d28d42d-ba8e-4d1f-a912-a0aba6766d7f

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

theorem pn_1_16 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (16 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 2) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -2) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -1) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (16 : Fin 88)), (alphaG (n3 1) (m3 1) (16 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 2) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -2) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -1) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (4451049049280026300967 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (16 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (16 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (16 : Fin 88) = 553294693951647161070000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (16 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 97302864079734967975815058435800000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (16 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((8793041497 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (16 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 175369392874762674664168644575010000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (16 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((316954770743 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (16 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 3975137279332337693103618300030000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (16 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((7184484729 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (16 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 3975122490871757753478297221070000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (16 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((7184458001 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (16 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 175369321259063963032718351479560000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (16 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((79238660327 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (16 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 97302855967881459950716029988530000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (16 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((175860815279 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_17 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (17 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else -2) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else 8) else if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else 8) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else -8) else if j.val = 1 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else 0) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -8) else if j.val = 3 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else 0) else if j.val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 6 else if k.val = 2 then -2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (17 : Fin 88)), (alphaG (n3 1) (m3 1) (17 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else -2) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else 8) else if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else 8) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else -8) else if j.val = 1 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else 0) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -8) else if j.val = 3 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else 0) else if j.val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 6 else if k.val = 2 then -2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (49565301194931842743206 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (17 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (17 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (17 : Fin 88) = 6852937681615717442160000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (17 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 2236189948354607890163418315360000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (17 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((163155573 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (17 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 420886130054907000521413963082160000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (17 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((61416891501 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (17 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 2919925153002043836985783628192400000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (17 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((85216743203 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (17 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 83419979239761413661123707624400000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (17 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((2434575743 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (17 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 83422591750929087613005595070400000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (17 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((608662997 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (17 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 2919923356524989414470303318274880000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (17 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((106520863467 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 1 (17 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 420888483977324196385813888062720000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 1) (m3 1) (17 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((3838577187 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 1 (17 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2235797117407884632392481377680000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 1) (m3 1) (17 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((326253823 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_18 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (18 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 5) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else -5) else if j.val = 2 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (20 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 4 then (if k.val = 0 then (20 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (18 : Fin 88)), (alphaG (n3 1) (m3 1) (18 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 5) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else -5) else if j.val = 2 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (20 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 4 then (if k.val = 0 then (20 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2681761330917225188651 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (18 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (18 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (18 : Fin 88) = 3875209754433415815974000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (18 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 25536666618197502964381477438940000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (18 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((658975081 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (18 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1242107397753983083326930552760924000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (18 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((160263247213 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (18 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 669960866078283718347521033834974000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (18 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((172883768501 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (18 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 669960794898430948914539326024542000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (18 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((172883750133 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (18 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1242107498052161947572598701799992000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (18 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((80131630077 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (18 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 25536531032358614848028908140628000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (18 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((3294857911 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_19 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (19 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 5) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else 8) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else -2) else if j.val = 3 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 3 else if k.val = 2 then -4 else -6) else if j.val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then -4 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (19 : Fin 88)), (alphaG (n3 1) (m3 1) (19 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 5) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else 8) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else -2) else if j.val = 3 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 3 else if k.val = 2 then -4 else -6) else if j.val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then -4 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (14897677262676305121680 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (19 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (19 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (19 : Fin 88) = 109598382243794462278000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (19 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 12645457128792814254763387561788000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (19 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((57689980773 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (19 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 42192387922236367693749626377610000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (19 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((76994545099 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (19 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 42199475464066012742881120000956000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (19 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((192518696901 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (19 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 12561061728699267586605866059646000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (19 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((114609919157 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_20 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (20 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 4) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -2) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else -4) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (20 : Fin 88)), (alphaG (n3 1) (m3 1) (20 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 4) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -2) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else -4) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1235305526894435183058 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (20 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (20 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (20 : Fin 88) = 2051847738255341859836000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (20 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 359281926694288931260270042685996000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (20 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((175101651061 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (20 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 14428523419736837672699715285020000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (20 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((1406393189 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (20 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 652213676329714472372686858482236000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (20 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((317866508401 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (20 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 652213344513105632671822653243660000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (20 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((63573269337 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (20 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 14428205602885116088033019707472000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (20 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((1757952763 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (20 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 359282061695610869770487710595616000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (20 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((21887714607 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_21 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (21 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else 6) else if j.val = 1 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 7) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else -6) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else -6) else if j.val = 4 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else 3) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 3) else if j.val = 2 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (21 : Fin 88)), (alphaG (n3 1) (m3 1) (21 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else 6) else if j.val = 1 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 7) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else -6) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else -6) else if j.val = 4 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else 3) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 3) else if j.val = 2 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (13199507361450463755916 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (21 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (21 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (21 : Fin 88) = 7869101871661276298088000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (21 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 1136002817450385303681089618954064000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (21 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((72181224489 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (21 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 281748761683248427153179504484104000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (21 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((35804436933 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (21 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 2586362751641067307073763476016000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (21 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((164336591 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (21 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 317710822315306108617195041876472000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (21 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((40374470619 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (21 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 4393004326310069053012534996337136000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (21 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((279129969211 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (21 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 317710836086234384024428563530472000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (21 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((40374472369 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 1 (21 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 2586351309966945911578026056064000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 1) (m3 1) (21 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((20541983 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 1 (21 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 281748778932319729834697149893000000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 1) (m3 1) (21 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((286435513 : ℚ)/8000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 1 (21 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 1136002814822105278546223335392672000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 1) (m3 1) (21 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((36090612161 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_22 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (22 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 7) else if j.val = 1 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else 0) else if j.val = 2 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 4) else if j.val = 2 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -8) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 4 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (22 : Fin 88)), (alphaG (n3 1) (m3 1) (22 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 7) else if j.val = 1 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else 0) else if j.val = 2 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 4) else if j.val = 2 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -8) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 4 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2560783501031201305419 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (22 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (22 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (22 : Fin 88) = 34888091120226875815908000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (22 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 11155705316690621331017778203916000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (22 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((319756827 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (22 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1265738898745552263231918377153196000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (22 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((36279969987 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (22 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 5118928511415534842011929109801752000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (22 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((73362117947 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (22 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 1280519071539344186645273270601600000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (22 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((45879519 : ℚ)/1250000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (22 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 19535406575136321226995350803082148000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (22 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((559944839281 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (22 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 1280520169676900286906416452121808000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (22 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((9175911669 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 1 (22 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 5118928510299115926164669083692696000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 1) (m3 1) (22 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((73362117931 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 1 (22 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 1265739985090933564856377532896500000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 1) (m3 1) (22 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((290240009 : ℚ)/8000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 1 (22 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 11153693006482897765047592446384000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 1) (m3 1) (22 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((79924787 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_23 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (23 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else 8) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -2 else if k.val = 2 then 7 else 0) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else 2) else if j.val = 2 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (23 : Fin 88)), (alphaG (n3 1) (m3 1) (23 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else 8) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -2 else if k.val = 2 then 7 else 0) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else 2) else if j.val = 2 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (584179876836816436502 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (23 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (23 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (23 : Fin 88) = 3447291078618988929820000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (23 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 22797316538999110587181335005120000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (23 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((413319401 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (23 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 594471046716986435632623479342320000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (23 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((43111462969 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (23 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 1106377146734298295035694337533460000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (23 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((320941029203 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (23 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1106377431046182713058187335508140000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (23 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((320941111677 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (23 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 594471121157789987331070429875400000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (23 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((17244587347 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (23 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 22797016424732388175243082735560000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (23 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((3306511679 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_24 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (24 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 3) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 6 else if k.val = 2 then -4 else 2) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else 8) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 0 else if k.val = 2 then -3 else 1) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else 8) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 6 else if k.val = 2 then -4 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (24 : Fin 88)), (alphaG (n3 1) (m3 1) (24 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 3) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 6 else if k.val = 2 then -4 else 2) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else 8) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 0 else if k.val = 2 then -3 else 1) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else 8) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 6 else if k.val = 2 then -4 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3588410158696716844221 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (24 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (24 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (24 : Fin 88) = 32291967987013664532806000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (24 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 400468663159082256219343026837358000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (24 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((12401494493 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (24 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 10599885573426560448816458331148000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (24 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((164125729 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (24 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 13717431933483042198772935645547352000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (24 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((106198482073 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (24 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2017483554820854097456324659506630000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (24 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((12495265421 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (24 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 2017483544196796629728829028213456000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (24 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((7809540847 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (24 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 13717431861633413427667532060054002000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (24 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((424793926067 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 1 (24 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 10599946443786215969574102670458000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 1) (m3 1) (24 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((328253343 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 1 (24 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 400468597703263146542645018839596000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 1) (m3 1) (24 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((6200746233 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_25 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (25 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 1) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -2) else if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (25 : Fin 88)), (alphaG (n3 1) (m3 1) (25 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 1) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -2) else if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3350355863453258710899783 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (25 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (25 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (25 : Fin 88) = 35588977010439180914298000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (25 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 387215616587331305996753478719496000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (25 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((2720053013 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (25 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 54205615762299926614374416729778000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (25 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((1523101261 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (25 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 5816769663207500134987925657141856000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (25 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((10215188367 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (25 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 11126411957858343561297170779995930000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (25 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((62527292957 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (25 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 409885714583070974667490800234612000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (25 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((5758604897 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (25 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 409884877459153735117077334117056000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (25 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((359912071 : ℚ)/31250000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 1 (25 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 11126413790263591874789717695371354000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 1) (m3 1) (25 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((312636516273 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 1 (25 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 5816769974717815907362076199992250000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 1) (m3 1) (25 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((1307544181 : ℚ)/8000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 1 (25 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 54205334324669728061331746461194000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 1) (m3 1) (25 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((1523093353 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 1 (25 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 387214465675403765404081891236474000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 1) (m3 1) (25 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((10880179713 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_26 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (26 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 6) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 3 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -8 else if k.val = 2 then -5 else 6) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -8 else if k.val = 2 then -5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (26 : Fin 88)), (alphaG (n3 1) (m3 1) (26 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 6) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 3 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -8 else if k.val = 2 then -5 else 6) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -8 else if k.val = 2 then -5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (870289708575876907955131 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (26 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (26 : Fin 88)))) =
        {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (26 : Fin 88) = 36317267733912428022238000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (26 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 59559667007074219558825180716710000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (26 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((327996409 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (26 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 407090735773968696570591808242608000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (26 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((1401161077 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (26 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 433538090561830585588702433907146000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (26 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((11937519467 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (26 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 11394273196982007898879131852805068000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (26 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((156871288893 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (26 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 5864172923060136345623881865386082000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (26 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((161470652639 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (26 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 5864172529925713126021848524659732000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (26 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((80735320907 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 1 (26 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 11394277336496818745685502683536784000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 1) (m3 1) (26 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((39217836471 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 1 (26 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 433535508113556562543770628607442000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 1) (m3 1) (26 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((11937448359 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 1 (26 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 407088748456761029148618003357010000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 1) (m3 1) (26 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((2241846779 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 1 (26 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 59558997534560812617127018781418000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 1) (m3 1) (26 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((1639963611 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_27 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (27 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (31 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else -6) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (31 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else -6) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 1) else if j.val = 2 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else -1) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 1) else if j.val = 4 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (27 : Fin 88)), (alphaG (n3 1) (m3 1) (27 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (31 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else -6) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (31 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else -6) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 1) else if j.val = 2 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else -1) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 1) else if j.val = 4 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (12591153541566864818873 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (27 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (27 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (27 : Fin 88) = 1298656623467343632725000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (27 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 422086191453315285581692058300000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (27 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((81254387 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (27 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 15734201590879655293679245996350000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (27 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((6057876003 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (27 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 79896798737778411470551837963175000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (27 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((61522651403 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (27 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 553275210802367883695574931632850000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (27 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((213018283973 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (27 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 553275240211745778737038838323200000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (27 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((208025679 : ℚ)/488281250) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (27 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 79896843798565932540441206255225000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (27 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((61522686101 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 1 (27 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 15734162227298741375026394468875000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 1) (m3 1) (27 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((2423144339 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 1 (27 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 422079907253914327105853302025000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 1) (m3 1) (27 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((325012709 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_28 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (28 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-45 : Int) else if k.val = 1 then 2 else if k.val = 2 then 5 else 7) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else 5) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 4 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 1) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else 3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (28 : Fin 88)), (alphaG (n3 1) (m3 1) (28 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-45 : Int) else if k.val = 1 then 2 else if k.val = 2 then 5 else 7) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else 5) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 4 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 1) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else 3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (8563627801536282475754 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (28 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (28 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (28 : Fin 88) = 28096363841571444039635000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (28 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 9442773465785499162921738883750000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (28 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((1344341 : ℚ)/4000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (28 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1162593351367882135849276380729660000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (28 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((10344695829 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (28 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 1081216741393770645277241098427600000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (28 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((481030547 : ℚ)/12500000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (28 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 4018001019861597821940755103071115000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (28 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((143007865449 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (28 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 15553856120950199484458211170505975000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (28 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((110717929257 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (28 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 4018001075155241862153356973072795000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (28 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((143007867417 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 1 (28 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 1081217448579248537630487576040550000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 1) (m3 1) (28 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((3848246893 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 1 (28 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 1162594130901496920248991260402735000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 1) (m3 1) (28 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((41378811061 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 1 (28 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 9441179896221132913758698865820000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 1) (m3 1) (28 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((84007133 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_29 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (29 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else 5) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (29 : Fin 88)), (alphaG (n3 1) (m3 1) (29 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else 5) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2530922439497074925815 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (29 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (29 : Fin 88)))) =
        {(⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (29 : Fin 88) = 912554197159031363655000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (29 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 6678840595942557323027469795195000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (29 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((7318842669 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (29 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 161521123193332241054073164741970000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (29 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((88499468687 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (29 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 288080724039283607380968579672285000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (29 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((315686153147 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (29 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 288072913942362113416724675627475000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (29 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((63135518929 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (29 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 161525424761192520789867126680355000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (29 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((177003651141 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (29 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 6675170626918323690338983482720000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (29 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((228588157 : ℚ)/31250000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_30 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (30 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (30 : Fin 88)), (alphaG (n3 1) (m3 1) (30 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1451476431956979011418 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (30 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (30 : Fin 88)))) =
        {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (30 : Fin 88) = 110808482762711770245000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (30 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 13133872542313368848493765875205000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (30 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((118527681409 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (30 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 42270368966472271451124769906545000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (30 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((381472319741 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (30 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 42270369143211801457650043447320000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (30 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((47684040167 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (30 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 13133872110714328487731420770930000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (30 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((59263838757 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_31 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (31 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -4) else if j.val = 3 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -1) else if j.val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (31 : Fin 88)), (alphaG (n3 1) (m3 1) (31 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -4) else if j.val = 3 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -1) else if j.val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1846165981055119532794 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (31 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (31 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (31 : Fin 88) = 109696435330058679800000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (31 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 42313318824731503795877289216200000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (31 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((385731028519 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (31 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12534903274447145015754665659400000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (31 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((114269011903 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (31 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 12534919844203398056448308129200000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (31 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((57134581477 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (31 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 42313293386676632931919736995200000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (31 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((24108174789 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    (((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (16 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 2) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -2) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -1) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (16 : Fin 88)), (alphaG (n3 1) (m3 1) (16 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 2) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -2) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -1) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (4451049049280026300967 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (17 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else -2) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else 8) else if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else 8) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else -8) else if j.val = 1 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else 0) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -8) else if j.val = 3 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else 0) else if j.val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 6 else if k.val = 2 then -2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (17 : Fin 88)), (alphaG (n3 1) (m3 1) (17 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else -2) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else 8) else if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else 8) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else -8) else if j.val = 1 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else 0) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -8) else if j.val = 3 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else 0) else if j.val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 6 else if k.val = 2 then -2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (49565301194931842743206 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (18 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 5) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else -5) else if j.val = 2 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (20 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 4 then (if k.val = 0 then (20 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (18 : Fin 88)), (alphaG (n3 1) (m3 1) (18 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 5) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else -5) else if j.val = 2 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (20 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 4 then (if k.val = 0 then (20 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2681761330917225188651 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (19 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 5) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else 8) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else -2) else if j.val = 3 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 3 else if k.val = 2 then -4 else -6) else if j.val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then -4 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (19 : Fin 88)), (alphaG (n3 1) (m3 1) (19 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 5) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else 8) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else -2) else if j.val = 3 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 3 else if k.val = 2 then -4 else -6) else if j.val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then -4 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (14897677262676305121680 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (20 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 4) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -2) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else -4) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (20 : Fin 88)), (alphaG (n3 1) (m3 1) (20 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 4) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -2) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else -4) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1235305526894435183058 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (21 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else 6) else if j.val = 1 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 7) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else -6) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else -6) else if j.val = 4 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else 3) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 3) else if j.val = 2 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (21 : Fin 88)), (alphaG (n3 1) (m3 1) (21 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else 6) else if j.val = 1 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 7) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else -6) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else -6) else if j.val = 4 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else 3) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 3) else if j.val = 2 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (13199507361450463755916 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (22 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 7) else if j.val = 1 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else 0) else if j.val = 2 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 4) else if j.val = 2 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -8) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 4 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (22 : Fin 88)), (alphaG (n3 1) (m3 1) (22 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 7) else if j.val = 1 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else 0) else if j.val = 2 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 4) else if j.val = 2 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -8) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 4 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2560783501031201305419 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (23 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else 8) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -2 else if k.val = 2 then 7 else 0) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else 2) else if j.val = 2 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (23 : Fin 88)), (alphaG (n3 1) (m3 1) (23 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else 8) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -2 else if k.val = 2 then 7 else 0) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else 2) else if j.val = 2 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (584179876836816436502 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (24 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 3) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 6 else if k.val = 2 then -4 else 2) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else 8) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 0 else if k.val = 2 then -3 else 1) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else 8) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 6 else if k.val = 2 then -4 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (24 : Fin 88)), (alphaG (n3 1) (m3 1) (24 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 3) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 6 else if k.val = 2 then -4 else 2) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else 8) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 0 else if k.val = 2 then -3 else 1) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else 8) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 6 else if k.val = 2 then -4 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3588410158696716844221 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (25 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 1) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -2) else if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (25 : Fin 88)), (alphaG (n3 1) (m3 1) (25 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 1) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -2) else if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3350355863453258710899783 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (26 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 6) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 3 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -8 else if k.val = 2 then -5 else 6) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -8 else if k.val = 2 then -5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (26 : Fin 88)), (alphaG (n3 1) (m3 1) (26 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 6) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 3 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -8 else if k.val = 2 then -5 else 6) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -8 else if k.val = 2 then -5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (870289708575876907955131 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (27 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (31 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else -6) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (31 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else -6) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 1) else if j.val = 2 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else -1) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 1) else if j.val = 4 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (27 : Fin 88)), (alphaG (n3 1) (m3 1) (27 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (31 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else -6) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (31 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else -6) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 1) else if j.val = 2 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else -1) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 1) else if j.val = 4 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (12591153541566864818873 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (28 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-45 : Int) else if k.val = 1 then 2 else if k.val = 2 then 5 else 7) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else 5) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 4 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 1) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else 3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (28 : Fin 88)), (alphaG (n3 1) (m3 1) (28 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-45 : Int) else if k.val = 1 then 2 else if k.val = 2 then 5 else 7) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else 5) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 4 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 1) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else 3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (8563627801536282475754 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (29 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else 5) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (29 : Fin 88)), (alphaG (n3 1) (m3 1) (29 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else 5) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2530922439497074925815 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (30 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (30 : Fin 88)), (alphaG (n3 1) (m3 1) (30 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1451476431956979011418 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (31 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -4) else if j.val = 3 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -1) else if j.val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (31 : Fin 88)), (alphaG (n3 1) (m3 1) (31 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -4) else if j.val = 3 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -1) else if j.val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1846165981055119532794 : ℚ)/10^30) :=
  ⟨L3C.pn_1_16, L3C.pn_1_17, L3C.pn_1_18, L3C.pn_1_19, L3C.pn_1_20, L3C.pn_1_21, L3C.pn_1_22, L3C.pn_1_23, L3C.pn_1_24, L3C.pn_1_25, L3C.pn_1_26, L3C.pn_1_27, L3C.pn_1_28, L3C.pn_1_29, L3C.pn_1_30, L3C.pn_1_31⟩

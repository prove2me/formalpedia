-- Prove2me | solution 1 for mme_released_recursive_level3_penalty10
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T07:59:46.766015+00:00
-- url     : https://prove2.me/submissions/ed59e46e-a04a-4163-92cc-6040d7a406bd

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

theorem pn_1_48 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (48 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else 7) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else -4) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 6 else if k.val = 2 then 5 else -3) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 4 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 6 else if k.val = 2 then 5 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (48 : Fin 88)), (alphaG (n3 1) (m3 1) (48 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else 7) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else -4) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 6 else if k.val = 2 then 5 else -3) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 4 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 6 else if k.val = 2 then 5 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (9936636706253861679893 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (48 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (48 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (48 : Fin 88) = 3208324357662306811846000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (48 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 23646422311264392377154732957682000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (48 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((7370334067 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (48 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1011849297536848079217460416441300000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (48 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((6307649631 : ℚ)/20000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (48 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 568666442883669307578929268757790000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (48 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((35449435873 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (48 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 568666458812999743372282589573180000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (48 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((17724718433 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (48 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1011849264619440169602192526901340000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (48 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((31538247129 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (48 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 23646471498085119697980465368708000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (48 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((3685174699 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_49 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (49 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -1 else -6) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 0) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (49 : Fin 88)), (alphaG (n3 1) (m3 1) (49 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -1 else -6) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 0) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (11037506399272813394667 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (49 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (49 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (49 : Fin 88) = 111388925357145397880000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (49 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 13244632781853477745170026751240000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (49 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((118904395023 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (49 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 42446524956226364516231307640240000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (49 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((190532967349 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (49 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 42445705875920145580762696914680000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (49 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((381058581361 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (49 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 13252061743145410037835968693840000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (49 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((59485544459 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_50 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (50 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 5) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else 6) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 7) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 4 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (50 : Fin 88)), (alphaG (n3 1) (m3 1) (50 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 5) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else 6) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 7) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 4 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (6643684017056334994646 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (50 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (50 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (50 : Fin 88) = 2066943403349748553058000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (50 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 362059397272697851105053973971530000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (50 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((35033315057 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (50 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 14536464541443995923292067778230000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (50 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((1406566287 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (50 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 656876095551966140881298714290130000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (50 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((63560143397 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (50 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 656875749520837099293193949744234000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (50 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((317800549573 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (50 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 14536195214584652644356107214714000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (50 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((7032701133 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (50 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 362059501248218813210805187001162000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (50 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((175166625589 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_51 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (51 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else 0) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 0) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 6) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 6) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 0) else if j.val = 1 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 8) else if j.val = 2 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (51 : Fin 88)), (alphaG (n3 1) (m3 1) (51 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else 0) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 0) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 6) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 6) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 0) else if j.val = 1 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 8) else if j.val = 2 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (994957147898509144998 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (51 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (51 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (51 : Fin 88) = 7481789162368785855652000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (51 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 1080077284880213782087979750850632000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (51 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((72180414433 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (51 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 268456431274440862846707325148752000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (51 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((8970328669 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (51 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 2459341489297715453473703264288000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (51 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((41088793 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (51 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 301501085294975489477097482976916000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (51 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((40297992733 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (51 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 4176800745028412783939547205857532000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (51 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((558262289191 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (51 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 301501093771842610440931857430632000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (51 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((20148996933 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 1 (51 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 2459330670630586668209355991496000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 1) (m3 1) (51 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((164354449 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 1 (51 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 268456491196090264258313243065620000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 1) (m3 1) (51 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((7176264537 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 1 (51 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 1080077358762881760479740075414132000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 1) (m3 1) (51 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((144360838741 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_52 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (52 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -6) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -3) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 4 else if k.val = 2 then -2 else 0) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (52 : Fin 88)), (alphaG (n3 1) (m3 1) (52 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -6) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -3) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 4 else if k.val = 2 then -2 else 0) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (627067234486501397573 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (52 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (52 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (52 : Fin 88) = 2848462230008540292235000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (52 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 20955516515945358070751275440500000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (52 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((73567823 : ℚ)/10000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (52 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 503955190217706141810275953157420000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (52 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((44230460993 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (52 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 899319507438741481575588271498860000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (52 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((78930264369 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (52 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 899329505498441878101885911965335000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (52 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((315724567461 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (52 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 503960207017687961981703386498705000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (52 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((176923605203 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (52 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 20942303320017470694795201439180000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (52 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((1838035897 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_53 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (53 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -2 else if k.val = 2 then 6 else 1) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -2 else if k.val = 2 then 6 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 6 else if k.val = 2 then -1 else 7) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else -6) else if j.val = 3 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -7) else if j.val = 4 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 6 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (53 : Fin 88)), (alphaG (n3 1) (m3 1) (53 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -2 else if k.val = 2 then 6 else 1) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -2 else if k.val = 2 then 6 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 6 else if k.val = 2 then -1 else 7) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else -6) else if j.val = 3 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -7) else if j.val = 4 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 6 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (520736443358957469130 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (53 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (53 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (53 : Fin 88) = 33327408005107292634894000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (53 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 407902105859415342287202024019974000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (53 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((12239238821 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (53 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 10798186508086299105969161311860000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (53 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((32400319 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (53 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 14157918701658092549020392963664758000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (53 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((424813075757 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (53 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2087084955870747478963913487870888000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (53 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((15655920163 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (53 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 2087085127240279441225612216495836000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (53 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((31311842897 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (53 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 14157918903722167283985908209027080000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (53 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((21240654091 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 1 (53 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 10798285223868810233769945867888000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 1) (m3 1) (53 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((40500769 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 1 (53 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 407901739024635430071231991741716000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 1) (m3 1) (53 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((6119613907 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_54 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (54 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else 8) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 5 else if k.val = 2 then 5 else -1) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -2) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -2) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 5 else if k.val = 2 then 5 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else -6) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (54 : Fin 88)), (alphaG (n3 1) (m3 1) (54 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else 8) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 5 else if k.val = 2 then 5 else -1) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -2) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -2) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 5 else if k.val = 2 then 5 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else -6) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3212980615079375753155298 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (54 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (54 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (54 : Fin 88) = 31115381408683537634235000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (54 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 333769358527267648541557691985750000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (54 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((214536569 : ℚ)/20000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (54 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 46796523820071803186359058537310000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (54 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((751983773 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (54 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 5085804871350182199245653257415065000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (54 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((163449864379 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (54 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 9732370206475875647309139240698025000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (54 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((62556650543 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (54 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 358949695846184191149256805396895000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (54 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((11536085357 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (54 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 358949504859973104649702806462465000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (54 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((11536079219 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 1 (54 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 9732371057419326411986526461756805000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 1) (m3 1) (54 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((312783280063 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 1 (54 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 5085805060407239638406827923026925000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 1) (m3 1) (54 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((32689974091 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 1 (54 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 46796405737199357232333736615485000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 1) (m3 1) (54 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((1503963751 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 1 (54 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 333768724240217632527643018105275000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 1) (m3 1) (54 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((2145361613 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_55 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (55 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 3 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -2) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -2) else if j.val = 3 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (55 : Fin 88)), (alphaG (n3 1) (m3 1) (55 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 3 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -2) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -2) else if j.val = 3 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (862428715797810119898255 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (55 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (55 : Fin 88)))) =
        {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (55 : Fin 88) = 22296345071760406243600000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (55 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 36599104329130157912083280597200000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (55 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((1641484477 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (55 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 246148705894980440689949282466400000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (55 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((5519933987 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (55 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 270466773104050940142426805915600000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (55 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((12130543021 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (55 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 6994566289408528461975590182422800000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (55 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((313709097473 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (55 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 3600392236003507049820068065412800000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (55 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((40369758187 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (55 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 3600392121913109317622069316911600000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (55 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((161479027631 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 1 (55 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 6994570187523130047990934563498000000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 1) (m3 1) (55 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((62741854461 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 1 (55 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 270464626701799916983398953274400000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 1) (m3 1) (55 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((6065223377 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 1 (55 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 246146555791536135618693993387600000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 1) (m3 1) (55 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((11039771541 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 1 (55 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 36598471090633774844785556113600000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 1) (m3 1) (55 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((410364019 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_56 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (56 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else -2) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else -4) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else -4) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else -5) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (56 : Fin 88)), (alphaG (n3 1) (m3 1) (56 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else -2) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else -4) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else -4) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else -5) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5481334450218445794515 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (56 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (56 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (56 : Fin 88) = 5871145362013801297388000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (56 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 1922822580803965713725936401264000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (56 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((81875957 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (56 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 74397437151885257792642546016712000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (56 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((6335853787 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (56 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 398008209721775413180448749261196000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (56 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((67790556217 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (56 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 2461244173577867810501915976815244000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (56 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((419210225913 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (56 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 2461244333918847647098829408481524000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (56 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((419210253223 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (56 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 398008410109837764073500830411024000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (56 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((16947647587 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 1 (56 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 74397178991752544683785698568964000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 1) (m3 1) (56 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((12671663603 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 1 (56 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 1922795961030894343150854044072000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 1) (m3 1) (56 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((163749647 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_57 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (57 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (46 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -8) else if j.val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (57 : Fin 88)), (alphaG (n3 1) (m3 1) (57 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (46 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -8) else if j.val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (13101150407833766336024 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (57 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (57 : Fin 88)))) =
        {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (57 : Fin 88) = 109687395161363967662000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (57 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 12530116311360971370564179897234000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (57 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((114234787807 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (57 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 42274438279778988719811122775456000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (57 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((24088022043 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (57 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 42351288058618248849686273490764000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (57 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((193054489061 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (57 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 12531552511605758721938423836546000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (57 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((114247881383 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_58 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (58 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 7 else if k.val = 2 then 1 else -1) else if j.val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (58 : Fin 88)), (alphaG (n3 1) (m3 1) (58 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 7 else if k.val = 2 then 1 else -1) else if j.val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (4430667671429767061486 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (58 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (58 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (58 : Fin 88) = 110854925858598509174000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (58 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 42279899307320478737205969742760000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (58 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((19069923587 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (58 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 13145958796279556832310435002300000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (58 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((2371741029 : ℚ)/20000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (58 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 13147093526700257471905079171750000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (58 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((948778301 : ℚ)/8000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (58 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 42281974228298216132578516083190000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (58 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((76283437837 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_59 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (59 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -5) else if j.val = 2 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else 4) else if j.val = 2 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (59 : Fin 88)), (alphaG (n3 1) (m3 1) (59 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -5) else if j.val = 2 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else 4) else if j.val = 2 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (284719525971387311085 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (59 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (59 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (59 : Fin 88) = 1044011722367959846668000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (59 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 184849553046337620316540392681072000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (59 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((44264242701 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (59 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 329505138025302742438672932272640000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (59 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((493147507 : ℚ)/1562500000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (59 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 7651188085001361143215435435908000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (59 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((7328641931 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (59 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 7651205942821872247168612692048000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (59 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((1832164759 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (59 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 329505081747850848193797397634100000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (59 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((12624574023 : ℚ)/40000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (59 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 184849555520645402328605229284232000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (59 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((88528486587 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_60 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (60 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else 3) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else 6) else if j.val = 1 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else -4) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -8) else if j.val = 3 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else -4) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (60 : Fin 88)), (alphaG (n3 1) (m3 1) (60 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else 3) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else 6) else if j.val = 1 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else -4) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -8) else if j.val = 3 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else -4) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (9972751040560212894750 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (60 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (60 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (60 : Fin 88) = 7111731094732954067723000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (60 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 2333973411525004967385459431754000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (60 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((164093199 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (60 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 436450349335882559923397214005494000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (60 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((30685239889 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (60 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 3029982430666689647070880942497377000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (60 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((426054133699 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (60 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 87097192881246733575154163518662000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (60 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((6123487497 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (60 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 87100211178152380282922999904815000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (60 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((2449479881 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (60 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 3029980321512151957739761261616375000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (60 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((3408430697 : ℚ)/8000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 1 (60 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 436453015232289000423826086581551000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 1) (m3 1) (60 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((61370854637 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 1 (60 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2333600515016783739671872443972000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 1) (m3 1) (60 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((82033491 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_61 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (61 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else 2) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 5 else if k.val = 2 then -2 else -2) else if j.val = 2 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else -5) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (61 : Fin 88)), (alphaG (n3 1) (m3 1) (61 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else 2) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 5 else if k.val = 2 then -2 else -2) else if j.val = 2 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else -5) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2354298977027994734024 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (61 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (61 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (61 : Fin 88) = 3843287194311339891060000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (61 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 25356806904623050952417591420760000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (61 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((3298843623 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (61 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1231968629332191451617676633860420000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (61 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((320550759557 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (61 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 664318180531149995530673238798000000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (61 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((1728515583 : ℚ)/10000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (61 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 664318158655159285510526578884480000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (61 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((5401611019 : ℚ)/31250000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (61 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1231968679398693731911501394699040000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (61 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((40068846573 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (61 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 25356739489522375537204562337300000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (61 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((1319533941 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_62 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (62 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 5) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else 8) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else -2) else if j.val = 3 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 3 else if k.val = 2 then -4 else -6) else if j.val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then -4 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (62 : Fin 88)), (alphaG (n3 1) (m3 1) (62 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 5) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else 8) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else -2) else if j.val = 3 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 3 else if k.val = 2 then -4 else -6) else if j.val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then -4 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (14736341817626295890389 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (62 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (62 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (62 : Fin 88) = 109646432311372884291000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (62 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 12650940750816317480712138643959000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (62 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((115379410749 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (62 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 42210915850573516614990885132033000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (62 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((384972998763 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (62 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 42218004835835072871180171881445000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (62 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((77007530379 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (62 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 12566570874147977324116804342563000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (62 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((114609938593 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_63 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (63 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 3 else 0) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else -5) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else 2) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 4 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (63 : Fin 88)), (alphaG (n3 1) (m3 1) (63 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 3 else 0) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else -5) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else 2) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 4 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (6524398665098104031364 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (63 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (63 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (63 : Fin 88) = 1778621519519143952040000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (63 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 313166508753664723435376610075480000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (63 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((176072596287 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (63 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12896633652631142335631095276440000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (63 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((7250915111 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (63 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 563247908131215228836241293907480000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (63 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((316676652087 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (63 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 563247569149075688241152906460000000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (63 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((633352923 : ℚ)/2000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (63 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 12896261308887760119959599414680000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (63 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((7250705767 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (63 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 313166638523669409071638494865920000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (63 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((2751135457 : ℚ)/15625000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    (((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (48 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else 7) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else -4) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 6 else if k.val = 2 then 5 else -3) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 4 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 6 else if k.val = 2 then 5 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (48 : Fin 88)), (alphaG (n3 1) (m3 1) (48 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else 7) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else -4) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 6 else if k.val = 2 then 5 else -3) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 4 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 6 else if k.val = 2 then 5 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (9936636706253861679893 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (49 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -1 else -6) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 0) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (49 : Fin 88)), (alphaG (n3 1) (m3 1) (49 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -1 else -6) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 0) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (11037506399272813394667 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (50 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 5) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else 6) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 7) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 4 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (50 : Fin 88)), (alphaG (n3 1) (m3 1) (50 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 5) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else 6) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 7) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 4 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (6643684017056334994646 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (51 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else 0) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 0) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 6) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 6) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 0) else if j.val = 1 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 8) else if j.val = 2 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (51 : Fin 88)), (alphaG (n3 1) (m3 1) (51 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else 0) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 0) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 6) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 6) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 0) else if j.val = 1 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 8) else if j.val = 2 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (994957147898509144998 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (52 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -6) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -3) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 4 else if k.val = 2 then -2 else 0) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (52 : Fin 88)), (alphaG (n3 1) (m3 1) (52 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -6) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -3) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 4 else if k.val = 2 then -2 else 0) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (627067234486501397573 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (53 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -2 else if k.val = 2 then 6 else 1) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -2 else if k.val = 2 then 6 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 6 else if k.val = 2 then -1 else 7) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else -6) else if j.val = 3 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -7) else if j.val = 4 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 6 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (53 : Fin 88)), (alphaG (n3 1) (m3 1) (53 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -2 else if k.val = 2 then 6 else 1) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -2 else if k.val = 2 then 6 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 6 else if k.val = 2 then -1 else 7) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else -6) else if j.val = 3 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -7) else if j.val = 4 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 6 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (520736443358957469130 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (54 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else 8) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 5 else if k.val = 2 then 5 else -1) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -2) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -2) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 5 else if k.val = 2 then 5 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else -6) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (54 : Fin 88)), (alphaG (n3 1) (m3 1) (54 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else 8) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 5 else if k.val = 2 then 5 else -1) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -2) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -2) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 5 else if k.val = 2 then 5 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else -6) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3212980615079375753155298 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (55 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 3 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -2) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -2) else if j.val = 3 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (55 : Fin 88)), (alphaG (n3 1) (m3 1) (55 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 3 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -2) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -2) else if j.val = 3 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (862428715797810119898255 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (56 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else -2) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else -4) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else -4) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else -5) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (56 : Fin 88)), (alphaG (n3 1) (m3 1) (56 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else -2) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else -4) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else -4) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else -5) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5481334450218445794515 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (57 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (46 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -8) else if j.val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (57 : Fin 88)), (alphaG (n3 1) (m3 1) (57 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (46 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -8) else if j.val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (13101150407833766336024 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (58 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 7 else if k.val = 2 then 1 else -1) else if j.val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (58 : Fin 88)), (alphaG (n3 1) (m3 1) (58 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 7 else if k.val = 2 then 1 else -1) else if j.val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (4430667671429767061486 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (59 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -5) else if j.val = 2 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else 4) else if j.val = 2 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (59 : Fin 88)), (alphaG (n3 1) (m3 1) (59 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -5) else if j.val = 2 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else 4) else if j.val = 2 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (284719525971387311085 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (60 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else 3) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else 6) else if j.val = 1 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else -4) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -8) else if j.val = 3 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else -4) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (60 : Fin 88)), (alphaG (n3 1) (m3 1) (60 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else 3) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else 6) else if j.val = 1 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else -4) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -8) else if j.val = 3 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else -4) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (9972751040560212894750 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (61 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else 2) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 5 else if k.val = 2 then -2 else -2) else if j.val = 2 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else -5) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (61 : Fin 88)), (alphaG (n3 1) (m3 1) (61 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else 2) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 5 else if k.val = 2 then -2 else -2) else if j.val = 2 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else -5) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2354298977027994734024 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (62 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 5) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else 8) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else -2) else if j.val = 3 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 3 else if k.val = 2 then -4 else -6) else if j.val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then -4 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (62 : Fin 88)), (alphaG (n3 1) (m3 1) (62 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 5) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else 8) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else -2) else if j.val = 3 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 3 else if k.val = 2 then -4 else -6) else if j.val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then -4 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (14736341817626295890389 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (63 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 3 else 0) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else -5) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else 2) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 4 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (63 : Fin 88)), (alphaG (n3 1) (m3 1) (63 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 3 else 0) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else -5) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else 2) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 4 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (6524398665098104031364 : ℚ)/10^30) :=
  ⟨L3C.pn_1_48, L3C.pn_1_49, L3C.pn_1_50, L3C.pn_1_51, L3C.pn_1_52, L3C.pn_1_53, L3C.pn_1_54, L3C.pn_1_55, L3C.pn_1_56, L3C.pn_1_57, L3C.pn_1_58, L3C.pn_1_59, L3C.pn_1_60, L3C.pn_1_61, L3C.pn_1_62, L3C.pn_1_63⟩

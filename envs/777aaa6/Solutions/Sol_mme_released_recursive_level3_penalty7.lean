-- Prove2me | solution 1 for mme_released_recursive_level3_penalty7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T07:53:46.154655+00:00
-- url     : https://prove2.me/submissions/c4b4b33f-5f0f-45c8-944f-e409f6612dae

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

theorem pn_1_0 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (0 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -4) else if j.val = 3 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -1) else if j.val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (0 : Fin 88)), (alphaG (n3 1) (m3 1) (0 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -4) else if j.val = 3 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -1) else if j.val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1863898318358101398335 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (0 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (0 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (0 : Fin 88) = 109638383225826917493000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (0 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 42290990770217024788621633935900000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (0 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((3857316163 : ℚ)/10000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (0 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12528169521641667536547884333832000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (0 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((14283512253 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (0 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 12528206396538374645366698589508000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (0 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((28567108589 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (0 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 42291016537429850522463783140760000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (0 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((9643296283 : ℚ)/25000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_1 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (1 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -2) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 3 else if k.val = 2 then 1 else 1) else if j.val = 1 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else 5) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -1 else if k.val = 2 then 5 else 1) else if j.val = 3 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else 5) else if j.val = 4 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -4 else if k.val = 2 then 5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (1 : Fin 88)), (alphaG (n3 1) (m3 1) (1 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -2) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 3 else if k.val = 2 then 1 else 1) else if j.val = 1 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else 5) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -1 else if k.val = 2 then 5 else 1) else if j.val = 3 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else 5) else if j.val = 4 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -4 else if k.val = 2 then 5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (640054964879520455779 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (1 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (1 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (1 : Fin 88) = 9088980207679028411433000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (1 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 2975798169613283105402630083611000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (1 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((327407267 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (1 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 592784986939062086813130430450101000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (1 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((65220186797 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (1 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 3835187433664936426438226770964031000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (1 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((421960148007 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (1 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 113540150897567764408798295497290000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (1 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((1249206713 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (1 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 113543564773067649897943800200688000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (1 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((780777671 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (1 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 3835185056678476593388000499360139000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (1 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((421959886483 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 1 (1 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 592787842505774755202597706058608000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 1) (m3 1) (1 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((4076281311 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 1 (1 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2975374050529852178899867385532000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 1) (m3 1) (1 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((81840151 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_2 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (2 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 6) else if j.val = 1 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 1) else if j.val = 2 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then -3 else 2) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 4 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then -3 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (2 : Fin 88)), (alphaG (n3 1) (m3 1) (2 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 6) else if j.val = 1 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 1) else if j.val = 2 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then -3 else 2) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 4 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then -3 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (53263491096941162159174 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (2 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (2 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (2 : Fin 88) = 3507497171920217738522000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (2 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 24828445801781657158655269963160000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (2 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((353933939 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (2 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1112577642104084631093291042025552000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (2 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((39649983577 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (2 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 616342661026591177110050690697496000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (2 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((43930374767 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (2 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 616342328228244510975951224253092000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (2 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((87860702093 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (2 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1112577579225182830079547643541658000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (2 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((317199850689 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (2 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 24828515534332932104504129519042000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (2 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((7078698661 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_3 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (3 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else -3) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -2) else if j.val = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -7 else if k.val = 2 then -5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (3 : Fin 88)), (alphaG (n3 1) (m3 1) (3 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else -3) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -2) else if j.val = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -7 else if k.val = 2 then -5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (7846367121391741857183 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (3 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (3 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (3 : Fin 88) = 110610548046162776326000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (3 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 12999644953673052858962944726990000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (3 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((23505253673 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (3 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 42320222365325626925384546928420000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (3 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((38260566567 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (3 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 42323224033743414165155817974766000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (3 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((382632802941 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (3 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 12967456693420682376496690369824000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (3 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((7327203939 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_4 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (4 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 0) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 4 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (4 : Fin 88)), (alphaG (n3 1) (m3 1) (4 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 0) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 4 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (4851373145645192154331 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (4 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (4 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (4 : Fin 88) = 2327532889924818009000000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (4 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 400963374381435241706333659215000000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (4 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((34453938427 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (4 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 15433399816979020464289227624000000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (4 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((828849717 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (4 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 747369933046693509287344093344000000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (4 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((10034363213 : ℚ)/31250000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (4 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 747369566041307425942040434224000000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (4 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((20068716571 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (4 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 15433072735764597999388876881000000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (4 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((6630657209 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (4 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 400963543902638213600603708712000000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (4 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((21533720621 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_5 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (5 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 2) else if j.val = 1 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else -6) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 2) else if j.val = 1 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -2) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then -6 else 3) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -2) else if j.val = 4 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 5) else if j.val = 1 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else -4) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (5 : Fin 88)), (alphaG (n3 1) (m3 1) (5 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 2) else if j.val = 1 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else -6) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 2) else if j.val = 1 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -2) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then -6 else 3) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -2) else if j.val = 4 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 5) else if j.val = 1 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else -4) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (44666469750426604072739 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (5 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (5 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (5 : Fin 88) = 1461435110486930586420000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (5 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 213602407728966517633658164623780000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (5 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((146159351309 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (5 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 49586713480096735868679680623620000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (5 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((33930150661 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (5 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 465656765275947711469442624640000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (5 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((9957181 : ℚ)/31250000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (5 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 55272804812711909411429202230700000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (5 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((7564181867 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (5 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 823579940195315828517715086830760000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (5 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((281770957289 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (5 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 55272811298560929752427144762660000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (5 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((37820913773 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 1 (5 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 465658476616462091665159322460000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 1) (m3 1) (5 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((318630963 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 1 (5 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 49586716657256666067266775500700000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 1) (m3 1) (5 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((6786030567 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 1 (5 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 213602401072129589365689343480680000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 1) (m3 1) (5 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((73079673377 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_6 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (6 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -5 else if k.val = 2 then -7 else -4) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else 2) else if j.val = 2 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -5 else if k.val = 2 then -7 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else 2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 1) else if j.val = 2 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 2) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 4) else if j.val = 3 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (6 : Fin 88)), (alphaG (n3 1) (m3 1) (6 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -5 else if k.val = 2 then -7 else -4) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else 2) else if j.val = 2 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -5 else if k.val = 2 then -7 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else 2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 1) else if j.val = 2 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 2) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 4) else if j.val = 3 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (4014108893067820188395 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (6 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (6 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (6 : Fin 88) = 11511414805550672206280000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (6 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 3840598665038789832279016936920000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (6 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((333633939 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (6 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 443653937643297752906254756203200000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (6 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((963508711 : ℚ)/25000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (6 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 1663365814950813223682668311133520000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (6 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((72248539517 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (6 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 449007648172447963127034667236840000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (6 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((39005426853 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (6 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 6391679349945675665536399927951080000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (6 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((555247070661 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (6 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 449008332905934841697669513390080000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (6 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((152365181 : ℚ)/3906250000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 1 (6 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 1663364867446260578806839012226720000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 1) (m3 1) (6 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((36124249181 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 1 (6 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 443654375123106023054001283668320000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 1) (m3 1) (6 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((9635096611 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 1 (6 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 3839880698097367636853511253320000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 1) (m3 1) (6 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((333571569 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_7 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (7 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -2) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else -1) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else 0) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else if j.val = 4 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (7 : Fin 88)), (alphaG (n3 1) (m3 1) (7 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -2) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else -1) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else 0) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else if j.val = 4 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (6040600755913978554710 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (7 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (7 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (7 : Fin 88) = 3092428028935533181843000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (7 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 21889050171101970531358646687259000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (7 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((7078273113 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (7 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 542009289466258812446514989961586000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (7 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((87634907651 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (7 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 982315699254402380476467433547169000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (7 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((317651919483 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (7 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 982315721396187067654885015543049000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (7 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((317651926643 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (7 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 542009266968844901940511092053761000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (7 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((175269808027 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (7 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 21889001678738048793262822207176000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (7 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((884782179 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_8 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (8 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else -6) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else 8) else if j.val = 1 then (if k.val = 0 then (24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 8 else -4) else if j.val = 3 then (if k.val = 0 then (24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (8 : Fin 88)), (alphaG (n3 1) (m3 1) (8 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else -6) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else 8) else if j.val = 1 then (if k.val = 0 then (24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 8 else -4) else if j.val = 3 then (if k.val = 0 then (24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (325130379640329819702 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (8 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (8 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (8 : Fin 88) = 37962630290561097863440000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (8 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 463218403975098027041190338513920000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (8 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((190655587 : ℚ)/15625000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (8 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12459235571495009305338018606560000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (8 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((164098687 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (8 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 16287890975427838219825594480580400000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (8 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((85810128807 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (8 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2217746502213771260532664743353520000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (8 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((58419200283 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (8 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 2217746538468083188018513202938720000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (8 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((29209600619 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (8 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 16287890866702865067658610199688240000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (8 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((429050641171 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 1 (8 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 12459215717039367341883836027440000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 1) (m3 1) (8 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((328196851 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 1 (8 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 463218552484907723716205180291200000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 1) (m3 1) (8 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((305049037 : ℚ)/25000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_9 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (9 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else 5) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -6) else if j.val = 1 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 3 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (9 : Fin 88)), (alphaG (n3 1) (m3 1) (9 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else 5) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -6) else if j.val = 1 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 3 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3388116574435662540975338 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (9 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (9 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (9 : Fin 88) = 37450101734117273001739000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (9 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 407610310589577588992228582033364000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (9 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((2721022719 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (9 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 56717604554309906868048595822001000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (9 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((1514484659 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (9 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 6121342494319594697207925498509460000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (9 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((8172664707 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (9 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 11710843612206033138306353981429349000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (9 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((312705254991 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (9 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 428536946616746156813932265906343000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (9 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((11442878037 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (9 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 428536205741383550771920472503706000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (9 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((5721429127 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 1 (9 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 11710845306036684470696494577082580000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 1) (m3 1) (9 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((15635265011 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 1 (9 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 6121342651797272489171058470821955000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 1) (m3 1) (9 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((32690659669 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 1 (9 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 56717350305569233945882187015930000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 1) (m3 1) (9 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((151447787 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 1 (9 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 407609251950101768965155368875312000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 1) (m3 1) (9 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((680253913 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_10 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (10 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -6 else 5) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 3 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (10 : Fin 88)), (alphaG (n3 1) (m3 1) (10 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -6 else 5) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 3 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (913231017986758597997747 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (10 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (10 : Fin 88)))) =
        {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (10 : Fin 88) = 33031327604148577472310000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (10 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 54484314152708369636943571546020000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (10 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((824736971 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (10 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 370093163071989616326890358216570000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (10 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((11204307847 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (10 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 396784847788808248438013702269980000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (10 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((6006189829 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (10 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 10360444664454066163019949758134920000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (10 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((78413777283 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (10 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 5333858992839494850560058669654060000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (10 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((80739397713 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (10 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 5333855618491192121157978408353700000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (10 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((16147869327 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 1 (10 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 10360449181818429306379404871250520000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 1) (m3 1) (10 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((78413811473 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 1 (10 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 396782615597751415285445278504800000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 1) (m3 1) (10 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((150153901 : ℚ)/12500000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 1 (10 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 370090600072186827626318549266740000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 1) (m3 1) (10 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((5602115127 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 1 (10 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 54483605861950553878996832802690000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 1) (m3 1) (10 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((1649452499 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_11 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (11 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 1) else if j.val = 1 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else if j.val = 2 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else -2) else if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -6) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else 4) else if j.val = 3 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -6) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (11 : Fin 88)), (alphaG (n3 1) (m3 1) (11 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 1) else if j.val = 1 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else if j.val = 2 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else -2) else if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -6) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else 4) else if j.val = 3 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -6) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2763161070583761051773 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (11 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (11 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (11 : Fin 88) = 4583319222669465617794000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (11 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 1505603433865710914439336868964000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (11 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((164248153 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (11 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 57453121902003092011965507173066000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (11 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((12535265189 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (11 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 298786711369168404764138825531190000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (11 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((13038005727 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (11 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1933914177260520835018729595040536000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (11 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((105486552611 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (11 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 1933914180258011606644560109077812000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (11 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((210973105549 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (11 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 298786757417776634924259887507508000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (11 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((32595019341 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 1 (11 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 57453094874169635930126759041848000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 1) (m3 1) (11 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((3133814823 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 1 (11 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 1505576153949697585779979759076000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 1) (m3 1) (11 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((164245177 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_12 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (12 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else 0) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else 5) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 0 else if k.val = 2 then -3 else -3) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else 7) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (12 : Fin 88)), (alphaG (n3 1) (m3 1) (12 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else 0) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else 5) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 0 else if k.val = 2 then -3 else -3) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else 7) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5431290433785413972094 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (12 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (12 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (12 : Fin 88) = 27598267603987961734550000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (12 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 9277648545466425470944354940850000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (12 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((336167787 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (12 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1140502408800110773091464593942450000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (12 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((41325144939 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (12 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 1063517841171778052612044359670550000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (12 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((38535673921 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (12 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 3946782607506987847891107628253550000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (12 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((143008346181 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (12 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 15278105429417449253633965981935550000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (12 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((553589292221 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (12 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 3946784807806470843435344876986850000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (12 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((143008425907 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 1 (12 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 1063517782718647267365541405893650000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 1) (m3 1) (12 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((38535671803 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 1 (12 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 1140502989246875020166275794998050000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 1) (m3 1) (12 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((41325165971 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 1 (12 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 9276088774176250883311003378500000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 1) (m3 1) (12 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((33611127 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_13 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (13 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else -6) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else 5) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (13 : Fin 88)), (alphaG (n3 1) (m3 1) (13 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else -6) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else 5) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2824626289452063986870 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (13 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (13 : Fin 88)))) =
        {(⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (13 : Fin 88) = 915717287192554183392000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (13 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 6698378830112578230329691583776000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (13 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((7314898303 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (13 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 162045838302456727017257249825280000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (13 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((2212006923 : ℚ)/12500000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (13 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 289114413852449307232556844916320000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (13 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((63144906817 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (13 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 289114431365542424790155602288320000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (13 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((31572455321 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (13 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 162045845704199559394672714182816000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (13 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((176960561923 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (13 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 6698379137793586727027897203488000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (13 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((7314898639 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_14 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (14 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (14 : Fin 88)), (alphaG (n3 1) (m3 1) (14 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1440025194336011251818 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (14 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (14 : Fin 88)))) =
        {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (14 : Fin 88) = 110814596949017072568000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (14 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 13134592727388271708392098632584000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (14 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((118527640663 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (14 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 42272705873892163485283432385208000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (14 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((381472360481 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (14 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 42272706050641445618965663131168000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (14 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((95368090519 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (14 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 13134592297095191755358805851040000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (14 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((5926381839 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_15 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (15 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else 1) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 2) else if j.val = 4 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (15 : Fin 88)), (alphaG (n3 1) (m3 1) (15 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else 1) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 2) else if j.val = 4 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (6654731988543825606994 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (15 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (15 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (15 : Fin 88) = 110169238029726659400000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (15 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 42147119390469089656292082844200000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (15 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((382567040893 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (15 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12906313276966531854230594712600000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (15 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((117149882379 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (15 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 12921320822960098950668616760200000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (15 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((117286105033 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (15 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 42194484539330938938808705683000000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (15 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((76599394339 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    (((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (0 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -4) else if j.val = 3 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -1) else if j.val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (0 : Fin 88)), (alphaG (n3 1) (m3 1) (0 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -4) else if j.val = 3 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -1) else if j.val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1863898318358101398335 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (1 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -2) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 3 else if k.val = 2 then 1 else 1) else if j.val = 1 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else 5) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -1 else if k.val = 2 then 5 else 1) else if j.val = 3 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else 5) else if j.val = 4 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -4 else if k.val = 2 then 5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (1 : Fin 88)), (alphaG (n3 1) (m3 1) (1 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -2) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 3 else if k.val = 2 then 1 else 1) else if j.val = 1 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else 5) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -1 else if k.val = 2 then 5 else 1) else if j.val = 3 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else 5) else if j.val = 4 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -4 else if k.val = 2 then 5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (640054964879520455779 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (2 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 6) else if j.val = 1 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 1) else if j.val = 2 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then -3 else 2) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 4 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then -3 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (2 : Fin 88)), (alphaG (n3 1) (m3 1) (2 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 6) else if j.val = 1 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 1) else if j.val = 2 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then -3 else 2) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 4 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then -3 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (53263491096941162159174 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (3 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else -3) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -2) else if j.val = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -7 else if k.val = 2 then -5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (3 : Fin 88)), (alphaG (n3 1) (m3 1) (3 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else -3) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -2) else if j.val = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -7 else if k.val = 2 then -5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (7846367121391741857183 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (4 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 0) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 4 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (4 : Fin 88)), (alphaG (n3 1) (m3 1) (4 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 0) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 4 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (4851373145645192154331 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (5 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 2) else if j.val = 1 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else -6) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 2) else if j.val = 1 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -2) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then -6 else 3) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -2) else if j.val = 4 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 5) else if j.val = 1 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else -4) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (5 : Fin 88)), (alphaG (n3 1) (m3 1) (5 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 2) else if j.val = 1 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else -6) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 2) else if j.val = 1 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -2) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then -6 else 3) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -2) else if j.val = 4 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 5) else if j.val = 1 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else -4) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (44666469750426604072739 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (6 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -5 else if k.val = 2 then -7 else -4) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else 2) else if j.val = 2 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -5 else if k.val = 2 then -7 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else 2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 1) else if j.val = 2 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 2) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 4) else if j.val = 3 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (6 : Fin 88)), (alphaG (n3 1) (m3 1) (6 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -5 else if k.val = 2 then -7 else -4) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else 2) else if j.val = 2 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -5 else if k.val = 2 then -7 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else 2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 1) else if j.val = 2 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 2) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 4) else if j.val = 3 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (4014108893067820188395 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (7 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -2) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else -1) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else 0) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else if j.val = 4 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (7 : Fin 88)), (alphaG (n3 1) (m3 1) (7 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -2) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else -1) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else 0) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else if j.val = 4 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (6040600755913978554710 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (8 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else -6) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else 8) else if j.val = 1 then (if k.val = 0 then (24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 8 else -4) else if j.val = 3 then (if k.val = 0 then (24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (8 : Fin 88)), (alphaG (n3 1) (m3 1) (8 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else -6) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else 8) else if j.val = 1 then (if k.val = 0 then (24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 8 else -4) else if j.val = 3 then (if k.val = 0 then (24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (325130379640329819702 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (9 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else 5) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -6) else if j.val = 1 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 3 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (9 : Fin 88)), (alphaG (n3 1) (m3 1) (9 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else 5) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -6) else if j.val = 1 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 3 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3388116574435662540975338 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (10 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -6 else 5) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 3 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (10 : Fin 88)), (alphaG (n3 1) (m3 1) (10 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -6 else 5) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 3 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (913231017986758597997747 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (11 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 1) else if j.val = 1 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else if j.val = 2 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else -2) else if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -6) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else 4) else if j.val = 3 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -6) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (11 : Fin 88)), (alphaG (n3 1) (m3 1) (11 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 1) else if j.val = 1 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else if j.val = 2 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else -2) else if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -6) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else 4) else if j.val = 3 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -6) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2763161070583761051773 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (12 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else 0) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else 5) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 0 else if k.val = 2 then -3 else -3) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else 7) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (12 : Fin 88)), (alphaG (n3 1) (m3 1) (12 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else 0) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else 5) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 0 else if k.val = 2 then -3 else -3) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else 7) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5431290433785413972094 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (13 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else -6) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else 5) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (13 : Fin 88)), (alphaG (n3 1) (m3 1) (13 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else -6) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else 5) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2824626289452063986870 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (14 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (14 : Fin 88)), (alphaG (n3 1) (m3 1) (14 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1440025194336011251818 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (15 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else 1) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 2) else if j.val = 4 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (15 : Fin 88)), (alphaG (n3 1) (m3 1) (15 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else 1) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 2) else if j.val = 4 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (6654731988543825606994 : ℚ)/10^30) :=
  ⟨L3C.pn_1_0, L3C.pn_1_1, L3C.pn_1_2, L3C.pn_1_3, L3C.pn_1_4, L3C.pn_1_5, L3C.pn_1_6, L3C.pn_1_7, L3C.pn_1_8, L3C.pn_1_9, L3C.pn_1_10, L3C.pn_1_11, L3C.pn_1_12, L3C.pn_1_13, L3C.pn_1_14, L3C.pn_1_15⟩

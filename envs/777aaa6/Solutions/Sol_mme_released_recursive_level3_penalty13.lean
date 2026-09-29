-- Prove2me | solution 1 for mme_released_recursive_level3_penalty13
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T08:18:42.481974+00:00
-- url     : https://prove2.me/submissions/52e3e4df-5036-460b-8f94-8c39c0efe052

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

theorem pn_2_0 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (0 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 5) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 2) else if j.val = 4 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (0 : Fin 88)), (alphaG (n3 2) (m3 2) (0 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 5) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 2) else if j.val = 4 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (875003602837153662383 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (0 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (0 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (0 : Fin 88) = 109577400394025852235000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (0 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 12563136245627991843676898923350000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (0 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((11465079661 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (0 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 42225504355962491576558949436140000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (0 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((96337164881 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (0 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 42225577988030769947746720675680000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (0 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((12042166609 : ℚ)/31250000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (0 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 12563181804404598867017430964830000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (0 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((57325606189 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_1 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (1 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else if j.val = 1 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else -8) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 5 else if k.val = 2 then -6 else -3) else if j.val = 2 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 4 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 5 else if k.val = 2 then -6 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (1 : Fin 88)), (alphaG (n3 2) (m3 2) (1 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else if j.val = 1 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else -8) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 5 else if k.val = 2 then -6 else -3) else if j.val = 2 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 4 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 5 else if k.val = 2 then -6 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (741499120881681123631 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (1 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (1 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (1 : Fin 88) = 3459169045607624158192000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (1 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 22863666830894859527391313416176000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (1 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((6609583553 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (1 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 596600530214099800843871987247984000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (1 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((172469319177 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (1 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 1110120266959861981486341258388224000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (1 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((20057567517 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (1 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1110120413047489115587524707152768000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (1 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((40115140313 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (1 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 596600643138673294704762631425824000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (1 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((86234675911 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (1 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 22863525416605106042108102369024000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (1 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((413096417 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_2 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (2 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else 2) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 1) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 1) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 8 else if k.val = 2 then 8 else -3) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -7) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 6) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -7) else if j.val = 4 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 8 else if k.val = 2 then 8 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (2 : Fin 88)), (alphaG (n3 2) (m3 2) (2 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else 2) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 1) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 1) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 8 else if k.val = 2 then 8 else -3) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -7) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 6) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -7) else if j.val = 4 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 8 else if k.val = 2 then 8 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (4740464368945404499185 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (2 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (2 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (2 : Fin 88) = 879841510671645059631000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (2 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 284515629475287890176438233105000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (2 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((64674291 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (2 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 10601307964661113150423673986092000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (2 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((3012277733 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (2 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 54159993996487025528511147779388000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (2 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((15389133537 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (2 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 374874976997568418840489785319218000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (2 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((213035514039 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (2 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 374874859750768548247740783951789000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (2 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((426070894819 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (2 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 54159872286251171298506758903896000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (2 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((7694549477 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 2 (2 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 10601464704906873261304467010218000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 2) (m3 2) (2 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((6024644539 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 2 (2 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 284519341526621413846944816294000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 2) (m3 2) (2 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((161687837 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_3 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (3 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -5) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (19 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -2) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -2) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (3 : Fin 88)), (alphaG (n3 2) (m3 2) (3 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -5) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (19 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -2) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -2) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (25226217124847524830304 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (3 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (3 : Fin 88)))) =
        {(⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (3 : Fin 88) = 470537640329091824576000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (3 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 3366145533714167160201423109248000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (3 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((3576914199 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (3 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 82757749072814852219228839773376000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (3 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((175879126301 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (3 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 149144986462056368904570051111936000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (3 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((19810448421 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (3 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 149144912661991784409150100962944000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (3 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((158483508947 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (3 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 82757704999906770794843090862336000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (3 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((43969758159 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (3 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 3366141598607881088006494180160000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (3 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((1430764007 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_4 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (4 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else 1) else if j.val = 3 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 6) else if j.val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (4 : Fin 88)), (alphaG (n3 2) (m3 2) (4 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else 1) else if j.val = 3 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 6) else if j.val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (9983125471716396156060 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (4 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (4 : Fin 88)))) =
        {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (4 : Fin 88) = 110255381897058443786000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (4 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 12877329259062069838409951649786000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (4 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((116795471001 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (4 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 42226979583766442802902495693360000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (4 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((9574811419 : ℚ)/25000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (4 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 42231057675983648958224310019058000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (4 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((383029444453 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (4 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 12920015378246282186463242637796000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (4 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((58591313893 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_5 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (5 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 5) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else -5) else if j.val = 2 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (35 : Int) else if k.val = 1 then -4 else if k.val = 2 then -7 else -6) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 4 then (if k.val = 0 then (35 : Int) else if k.val = 1 then -4 else if k.val = 2 then -7 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (5 : Fin 88)), (alphaG (n3 2) (m3 2) (5 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 5) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else -5) else if j.val = 2 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (35 : Int) else if k.val = 1 then -4 else if k.val = 2 then -7 else -6) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 4 then (if k.val = 0 then (35 : Int) else if k.val = 1 then -4 else if k.val = 2 then -7 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (8243612907270601472670 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (5 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (5 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (5 : Fin 88) = 3870557607912549433866000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (5 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 25478264326102326915895504616544000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (5 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((411411399 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (5 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1240682496021656621025481399962924000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (5 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((160271803407 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (5 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 669118131257292800171305025316102000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (5 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((172873833447 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (5 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 669117890551185721697768282623428000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (5 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((86436885629 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (5 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1240683084253519641143094161182140000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (5 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((32054375879 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (5 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 25477741502792322912455626298862000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (5 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((6582447307 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_6 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (6 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -1) else if j.val = 2 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 8) else if j.val = 1 then (if k.val = 0 then (38 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else -3) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -6 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -6 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (6 : Fin 88)), (alphaG (n3 2) (m3 2) (6 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -1) else if j.val = 2 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 8) else if j.val = 1 then (if k.val = 0 then (38 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else -3) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -6 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -6 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (14359429174948390476589 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (6 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (6 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (6 : Fin 88) = 34718695463555573971387000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (6 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 11126593812338408225877172024311000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (6 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((320478453 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (6 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1260264398901153842782264850403584000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (6 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((141794147 : ℚ)/3906250000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (6 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 5094091789763486802097755331168051000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (6 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((146724746473 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (6 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 1273423444692554340290215163298776000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (6 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((4584790081 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (6 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 19440882943632891453938295734260513000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (6 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((559954303699 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (6 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 1273423450004514746214217980920987000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (6 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((36678320801 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 2 (6 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 5094091789798205497561310905139438000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 2) (m3 2) (6 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((73362373237 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 2 (6 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 1260264403900645989534267502283312000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 2) (m3 2) (6 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((2268706361 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 2 (6 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 11126649049782890742795360501028000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 2) (m3 2) (6 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((80120011 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_7 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (7 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else 0) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -2) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 2) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 2) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (7 : Fin 88)), (alphaG (n3 2) (m3 2) (7 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else 0) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -2) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 2) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 2) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (808624639531353613600309 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (7 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (7 : Fin 88)))) =
        {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (7 : Fin 88) = 32661113361821047875230000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (7 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 53112884241456335420441700020870000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (7 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((1626181069 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (7 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 362937392594533704227216409504760000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (7 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((2778054353 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (7 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 390235233676321859140748296269160000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (7 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((2987001923 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (7 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 10248946758011750015898745708423190000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (7 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((313796613253 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (7 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 5275320481262196680784704575223990000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (7 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((161516860213 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (7 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 5275321161625849120878952864140120000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (7 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((40379220261 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 2 (7 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 10248917278515424109924607148203180000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 2) (m3 2) (7 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((156897855333 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 2 (7 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 390250901800301565210192905854300000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 2) (m3 2) (7 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((1194848741 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 2 (7 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 362953694932012670137768660306040000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 2) (m3 2) (7 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((2778179137 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 2 (7 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 53117575161201813606621732054390000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 2) (m3 2) (7 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((1626324693 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_8 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (8 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -8 else if k.val = 2 then -8 else 7) else if j.val = 1 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -1) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 2 else if k.val = 2 then 5 else 1) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -2) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 2 else if k.val = 2 then 5 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else 6) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -2) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (8 : Fin 88)), (alphaG (n3 2) (m3 2) (8 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -8 else if k.val = 2 then -8 else 7) else if j.val = 1 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -1) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 2 else if k.val = 2 then 5 else 1) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -2) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 2 else if k.val = 2 then 5 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else 6) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -2) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (15515768878648247238102 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (8 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (8 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (8 : Fin 88) = 16565899923327863589440000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (8 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 5444680516798425413771658752960000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (8 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((328667959 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (8 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 659285033708958243441683022679040000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (8 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((2487357451 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (8 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 612936691397319584792806548401920000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (8 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((9249975767 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (8 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 2390708924947455246847592911535360000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (8 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((36078766261 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (8 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 9229151087881499338565482182264960000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (8 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((278558699817 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (8 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 2390707586141121143259641203762880000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (8 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((144314984227 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 2 (8 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 612936978832249154454567688775360000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 2) (m3 2) (8 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((36999920419 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 2 (8 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 659284972994935024445062967381440000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 2) (m3 2) (8 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((39797715551 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 2 (8 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 5443966907527428219391816446080000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 2) (m3 2) (8 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((164312441 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_9 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (9 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else 6) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 3 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else -4) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -8) else if j.val = 3 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else -4) else if j.val = 4 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (9 : Fin 88)), (alphaG (n3 2) (m3 2) (9 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else 6) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 3 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else -4) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -8) else if j.val = 3 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else -4) else if j.val = 4 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (10531213102653250546405 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (9 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (9 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (9 : Fin 88) = 7163905301134324310272000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (9 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 2350495382343530664697505085440000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (9 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((8202563 : ℚ)/25000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (9 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 439629700005313438531387807104768000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (9 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((61367324319 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (9 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 3052213287296139663073922589930240000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (9 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((85210877559 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (9 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 87759351236357800097888494981120000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (9 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((153127637 : ℚ)/12500000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (9 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 87758958797625403959602778280960000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (9 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((612507809 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (9 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 3052213617287109549224303293989376000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (9 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((213027216929 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 2 (9 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 439629413083742222800564856400896000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 2) (m3 2) (9 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((15341821067 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 2 (9 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2350478045692701919632674227200000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 2) (m3 2) (9 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((3281001 : ℚ)/10000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_10 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (10 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -8 else if k.val = 2 then 1 else 1) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 3 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -8 else if k.val = 2 then 1 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then -8 else if k.val = 2 then 8 else 6) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 3 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -8 else if k.val = 2 then -3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (10 : Fin 88)), (alphaG (n3 2) (m3 2) (10 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -8 else if k.val = 2 then 1 else 1) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 3 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -8 else if k.val = 2 then 1 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then -8 else if k.val = 2 then 8 else 6) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 3 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -8 else if k.val = 2 then -3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3207047485086156624993961 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (10 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (10 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (10 : Fin 88) = 30531019478083341047290000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (10 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 329430738559022718992771459380190000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (10 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((10790034011 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (10 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 46595654685113552727425093627350000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (10 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((305234843 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (10 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 4988455127061757477427905070359030000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (10 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((163389733207 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (10 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 9545754410535415139291876011132430000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (10 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((312657571667 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (10 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 355275306693328639013484307541490000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (10 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((11636535981 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (10 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 355275421825803090865763396872080000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (10 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((1454567469 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 2 (10 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 9545754380737140128682535148977390000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 2) (m3 2) (10 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((312657570691 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 2 (10 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 4988451994792876162423697005736060000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 2) (m3 2) (10 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((81694815307 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 2 (10 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 46595674347090096613096728082110000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 2) (m3 2) (10 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((1526174859 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 2 (10 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 329430768845794041251445778291870000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 2) (m3 2) (10 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((10790035003 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_11 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (11 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else 5) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 4 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else 1) else if j.val = 1 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -8) else if j.val = 2 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (11 : Fin 88)), (alphaG (n3 2) (m3 2) (11 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else 5) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 4 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else 1) else if j.val = 1 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -8) else if j.val = 2 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5649824715047531850439 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (11 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (11 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (11 : Fin 88) = 8449144978653725514200000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (11 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 1208881355285186197097568308768400000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (11 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((71538679851 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (11 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 314045895684830408594178737394400000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (11 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((9292238933 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (11 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 2836587406739786523664985989600000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (11 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((83931197 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (11 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 355013606795234563824614581926400000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (11 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((656526503 : ℚ)/15625000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (11 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 4687590927250695967584314253303000000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (11 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((110960125293 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (11 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 355013365006052709690951542065000000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (11 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((1680706703 : ℚ)/40000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 2 (11 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 2836638143855383339286698760600000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 2) (m3 2) (11 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((335730793 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 2 (11 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 314045900897952860423527379655800000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 2) (m3 2) (11 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((37168956349 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 2 (11 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 1208880702183177637121893512136800000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 2) (m3 2) (11 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((35769320601 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_12 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (12 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 3) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 3 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -6) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 0) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -6) else if j.val = 4 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (12 : Fin 88)), (alphaG (n3 2) (m3 2) (12 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 3) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 3 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -6) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 0) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -6) else if j.val = 4 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3384297378254418570808 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (12 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (12 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (12 : Fin 88) = 29840561367432433314565000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (12 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 371616549465351923537444639845340000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (12 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((3113350859 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (12 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 9740504387545567856998239787985000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (12 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((326418269 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (12 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 12590562676344796509767207405220875000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (12 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((16877112359 : ℚ)/40000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (12 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 1948361115075321899400043680200710000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (12 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((32646187367 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (12 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 1948360677911097866514895621823460000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (12 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((16323090021 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (12 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 12590562229064622173322464453206090000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (12 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((210963896993 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 2 (12 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 9740460999369339610240200410475000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 2) (m3 2) (12 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((65283363 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 2 (12 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 371617154184328034555705759505065000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 2) (m3 2) (12 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((12453423701 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_13 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (13 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -8) else if j.val = 2 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else 4) else if j.val = 2 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (13 : Fin 88)), (alphaG (n3 2) (m3 2) (13 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -8) else if j.val = 2 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else 4) else if j.val = 2 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (358967088790053066033 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (13 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (13 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (13 : Fin 88) = 1051372073961870357460000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (13 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 186153227056573940587787054683120000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (13 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((44264355043 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (13 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 331828515471410819224287840040600000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (13 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((31561473211 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (13 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 7704327195830918312453647653060000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (13 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((7327878861 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (13 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 7704349836077159007369925196700000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (13 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((1465580079 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (13 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 331828531342923647752682756256760000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (13 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((157807373603 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (13 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 186153123059053872575418776169760000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (13 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((22132165157 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_14 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (14 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 3 else 0) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else -5) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else -5) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 4 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (14 : Fin 88)), (alphaG (n3 2) (m3 2) (14 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 3 else 0) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else -5) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else -5) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 4 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3422711031360231628410 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (14 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (14 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (14 : Fin 88) = 1773840045009992719104000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (14 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 312307749679089110052682541995776000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (14 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((176063084469 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (14 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12870101846139099183876908952576000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (14 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((1813875761 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (14 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 561742167960692393708432941136640000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (14 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((63336282157 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (14 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 561742159660894823106677008449024000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (14 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((158340703053 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (14 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 12870118997398494385496509969152000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (14 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((7255512713 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (14 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 312307746865778798666834089496832000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (14 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((176063082883 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_15 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (15 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 3 then (if k.val = 0 then (37 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -8) else if j.val = 4 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (15 : Fin 88)), (alphaG (n3 2) (m3 2) (15 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 3 then (if k.val = 0 then (37 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -8) else if j.val = 4 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5474642236182278905474 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (15 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (15 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (15 : Fin 88) = 110882005440259842999000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (15 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 42293315168436905829003104811090000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (15 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((38142631891 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (15 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 13147687402113190331586366983259000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (15 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((118573679741 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (15 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 13147687784656109100482825329809000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (15 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((118573683191 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (15 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 42293315085053637737927702875842000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (15 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((190713159079 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    (((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (0 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 5) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 2) else if j.val = 4 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (0 : Fin 88)), (alphaG (n3 2) (m3 2) (0 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 5) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 2) else if j.val = 4 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (875003602837153662383 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (1 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else if j.val = 1 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else -8) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 5 else if k.val = 2 then -6 else -3) else if j.val = 2 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 4 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 5 else if k.val = 2 then -6 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (1 : Fin 88)), (alphaG (n3 2) (m3 2) (1 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else if j.val = 1 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else -8) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 5 else if k.val = 2 then -6 else -3) else if j.val = 2 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 4 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 5 else if k.val = 2 then -6 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (741499120881681123631 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (2 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else 2) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 1) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 1) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 8 else if k.val = 2 then 8 else -3) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -7) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 6) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -7) else if j.val = 4 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 8 else if k.val = 2 then 8 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (2 : Fin 88)), (alphaG (n3 2) (m3 2) (2 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else 2) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 1) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 1) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 8 else if k.val = 2 then 8 else -3) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -7) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 6) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -7) else if j.val = 4 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 8 else if k.val = 2 then 8 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (4740464368945404499185 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (3 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -5) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (19 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -2) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -2) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (3 : Fin 88)), (alphaG (n3 2) (m3 2) (3 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -5) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (19 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -2) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -2) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (25226217124847524830304 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (4 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else 1) else if j.val = 3 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 6) else if j.val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (4 : Fin 88)), (alphaG (n3 2) (m3 2) (4 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else 1) else if j.val = 3 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 6) else if j.val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (9983125471716396156060 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (5 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 5) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else -5) else if j.val = 2 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (35 : Int) else if k.val = 1 then -4 else if k.val = 2 then -7 else -6) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 4 then (if k.val = 0 then (35 : Int) else if k.val = 1 then -4 else if k.val = 2 then -7 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (5 : Fin 88)), (alphaG (n3 2) (m3 2) (5 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 5) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else -5) else if j.val = 2 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (35 : Int) else if k.val = 1 then -4 else if k.val = 2 then -7 else -6) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 4 then (if k.val = 0 then (35 : Int) else if k.val = 1 then -4 else if k.val = 2 then -7 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (8243612907270601472670 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (6 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -1) else if j.val = 2 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 8) else if j.val = 1 then (if k.val = 0 then (38 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else -3) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -6 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -6 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (6 : Fin 88)), (alphaG (n3 2) (m3 2) (6 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -1) else if j.val = 2 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 8) else if j.val = 1 then (if k.val = 0 then (38 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else -3) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -6 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -6 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (14359429174948390476589 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (7 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else 0) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -2) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 2) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 2) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (7 : Fin 88)), (alphaG (n3 2) (m3 2) (7 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else 0) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -2) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 2) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 2) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (808624639531353613600309 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (8 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -8 else if k.val = 2 then -8 else 7) else if j.val = 1 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -1) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 2 else if k.val = 2 then 5 else 1) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -2) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 2 else if k.val = 2 then 5 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else 6) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -2) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (8 : Fin 88)), (alphaG (n3 2) (m3 2) (8 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -8 else if k.val = 2 then -8 else 7) else if j.val = 1 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -1) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 2 else if k.val = 2 then 5 else 1) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -2) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 2 else if k.val = 2 then 5 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else 6) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -2) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (15515768878648247238102 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (9 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else 6) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 3 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else -4) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -8) else if j.val = 3 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else -4) else if j.val = 4 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (9 : Fin 88)), (alphaG (n3 2) (m3 2) (9 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else 6) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 3 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else -4) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -8) else if j.val = 3 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else -4) else if j.val = 4 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (10531213102653250546405 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (10 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -8 else if k.val = 2 then 1 else 1) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 3 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -8 else if k.val = 2 then 1 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then -8 else if k.val = 2 then 8 else 6) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 3 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -8 else if k.val = 2 then -3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (10 : Fin 88)), (alphaG (n3 2) (m3 2) (10 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -8 else if k.val = 2 then 1 else 1) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 3 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -8 else if k.val = 2 then 1 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then -8 else if k.val = 2 then 8 else 6) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 3 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -8 else if k.val = 2 then -3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3207047485086156624993961 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (11 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else 5) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 4 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else 1) else if j.val = 1 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -8) else if j.val = 2 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (11 : Fin 88)), (alphaG (n3 2) (m3 2) (11 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else 5) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 4 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else 1) else if j.val = 1 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -8) else if j.val = 2 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5649824715047531850439 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (12 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 3) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 3 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -6) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 0) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -6) else if j.val = 4 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (12 : Fin 88)), (alphaG (n3 2) (m3 2) (12 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 3) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 3 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -6) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 0) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -6) else if j.val = 4 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3384297378254418570808 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (13 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -8) else if j.val = 2 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else 4) else if j.val = 2 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (13 : Fin 88)), (alphaG (n3 2) (m3 2) (13 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -8) else if j.val = 2 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else 4) else if j.val = 2 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (358967088790053066033 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (14 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 3 else 0) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else -5) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else -5) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 4 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (14 : Fin 88)), (alphaG (n3 2) (m3 2) (14 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 3 else 0) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else -5) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else -5) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 4 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3422711031360231628410 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (15 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 3 then (if k.val = 0 then (37 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -8) else if j.val = 4 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (15 : Fin 88)), (alphaG (n3 2) (m3 2) (15 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 3 then (if k.val = 0 then (37 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -8) else if j.val = 4 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5474642236182278905474 : ℚ)/10^30) :=
  ⟨L3C.pn_2_0, L3C.pn_2_1, L3C.pn_2_2, L3C.pn_2_3, L3C.pn_2_4, L3C.pn_2_5, L3C.pn_2_6, L3C.pn_2_7, L3C.pn_2_8, L3C.pn_2_9, L3C.pn_2_10, L3C.pn_2_11, L3C.pn_2_12, L3C.pn_2_13, L3C.pn_2_14, L3C.pn_2_15⟩

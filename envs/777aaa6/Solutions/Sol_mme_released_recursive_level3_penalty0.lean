-- Prove2me | solution 1 for mme_released_recursive_level3_penalty0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T06:46:24.732242+00:00
-- url     : https://prove2.me/submissions/179025b1-53c1-41ad-876a-5f9341bfbb2a

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

theorem pn_0 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (0 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 5) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 2) else if j.val = 4 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (0 : Fin 88)), (alphaG (n3 0) (m3 0) (0 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 5) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 2) else if j.val = 4 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1584509256982770566717 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (0 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (0 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (0 : Fin 88) = 109575045509078956545000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (0 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 12563091103528839712236179913180000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (0 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((28663212151 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (0 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 42224348125350273400156693486215000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (0 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((385346389127 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (0 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 42224434011585843962351780935755000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (0 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((385347172939 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (0 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 12563172268613999470255345664850000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (0 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((11465358933 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (1 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -5) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else -5) else if j.val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else 2) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (1 : Fin 88)), (alphaG (n3 0) (m3 0) (1 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -5) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else -5) else if j.val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else 2) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (4061210160018434017608 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (1 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (1 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (1 : Fin 88) = 3891500549815061546820000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (1 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 25619951413105345004077700094420000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (1 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((6583566181 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (1 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1247311492358590535137238770099920000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (1 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((80130496989 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (1 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 672818882355765129934523609050500000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (1 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((6915778361 : ℚ)/40000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (1 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 672818769560621693544964674472800000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (1 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((4322360751 : ℚ)/25000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (1 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1247311610232142189035453023277720000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (1 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((160261009123 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (1 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 25619843894836654163742223004640000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (1 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((822942319 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (2 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else -1) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else 7) else if j.val = 1 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else 7) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -8) else if j.val = 3 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else 7) else if j.val = 4 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (2 : Fin 88)), (alphaG (n3 0) (m3 0) (2 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else -1) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else 7) else if j.val = 1 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else 7) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -8) else if j.val = 3 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else 7) else if j.val = 4 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (13904946759932504043269 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (2 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (2 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (2 : Fin 88) = 6938286480913396351838000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (2 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 2263415538116421414506731955694000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (2 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((326221113 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (2 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 426094450086589201912281556403690000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (2 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((12282411551 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (2 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 2956307512932753804337452044425406000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (2 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((426086112337 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (2 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 84478276593683425967546220220632000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (2 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((3043917141 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (2 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 84477438733146277346716168615590000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (2 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((2435109561 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (2 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 2956308150838812859515112632411126000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (2 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((426086204277 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 0 (2 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 426093835964976203305743662518634000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 0) (m3 0) (2 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((61411969243 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 0 (2 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2263400225318158038640983449228000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 0) (m3 0) (2 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((163109453 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (3 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 0 else if k.val = 2 then -7 else -1) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 0 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 1) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -2) else if j.val = 2 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (3 : Fin 88)), (alphaG (n3 0) (m3 0) (3 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 0 else if k.val = 2 then -7 else -1) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 0 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 1) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -2) else if j.val = 2 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (8909785987668425425519 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (3 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (3 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (3 : Fin 88) = 589047454390058129621000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (3 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 103625997828059122030438715317084000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (3 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((43980326651 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (3 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 186681002219699742731855574673302000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (3 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((158460070431 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (3 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 4216787238357212195595745166308000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (3 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((1789663637 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (3 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 4216726737293171792725251793398000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (3 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((3579275919 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (3 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 186681039959970145502879939490772000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (3 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((79230051233 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (3 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 103625900406678735367504773559136000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (3 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((5497535663 : ℚ)/31250000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    (((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (0 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 5) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 2) else if j.val = 4 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (0 : Fin 88)), (alphaG (n3 0) (m3 0) (0 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 5) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 2) else if j.val = 4 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1584509256982770566717 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (1 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -5) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else -5) else if j.val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else 2) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (1 : Fin 88)), (alphaG (n3 0) (m3 0) (1 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -5) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else -5) else if j.val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else 2) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (4061210160018434017608 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (2 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else -1) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else 7) else if j.val = 1 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else 7) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -8) else if j.val = 3 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else 7) else if j.val = 4 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (2 : Fin 88)), (alphaG (n3 0) (m3 0) (2 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else -1) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else 7) else if j.val = 1 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else 7) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -8) else if j.val = 3 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else 7) else if j.val = 4 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (13904946759932504043269 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (3 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 0 else if k.val = 2 then -7 else -1) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 0 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 1) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -2) else if j.val = 2 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (3 : Fin 88)), (alphaG (n3 0) (m3 0) (3 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 0 else if k.val = 2 then -7 else -1) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 0 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 1) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -2) else if j.val = 2 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (8909785987668425425519 : ℚ)/10^30) :=
  ⟨L3C.pn_0, L3C.pn_1, L3C.pn_2, L3C.pn_3⟩

-- Prove2me | solution 1 for mme_released_recursive_level3_penalty15
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T08:19:03.154155+00:00
-- url     : https://prove2.me/submissions/18c4caac-516c-4456-9f45-df3c3a162365

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

theorem pn_2_32 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (32 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else -3) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else 5) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else 4) else if j.val = 2 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else -1) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else 4) else if j.val = 4 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (32 : Fin 88)), (alphaG (n3 2) (m3 2) (32 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else -3) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else 5) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else 4) else if j.val = 2 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else -1) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else 4) else if j.val = 4 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (15233006572800959698805 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (32 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (32 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (32 : Fin 88) = 950877917145265514130000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (32 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 308945503144157750311785280200000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (32 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((16245277 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (32 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 11515253796771367725671893185420000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (32 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((6055064267 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (32 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 58511111211179231758930546849530000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (32 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((61533778581 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (32 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 405103621408429982248293413620950000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (32 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((85206231863 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (32 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 405103701738596422680324047323350000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (32 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((85206248759 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (32 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 58511200992121290697755125490000000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (32 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((61533873 : ℚ)/1000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 2 (32 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 11515143425518890923267871573930000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 2) (m3 2) (32 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((12110012461 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 2 (32 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 308939069504170345445316676620000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 2) (m3 2) (32 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((162449387 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_33 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (33 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else -2) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (33 : Fin 88)), (alphaG (n3 2) (m3 2) (33 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else -2) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (701788092790881936660 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (33 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (33 : Fin 88)))) =
        {(⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (33 : Fin 88) = 895244853840646821600000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (33 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 6552478210303278273114699290400000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (33 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((7319202319 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (33 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 158451448815109763116092278088000000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (33 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((17699230343 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (33 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 282618524715573942142726151481600000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (33 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((39461065247 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (33 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 282618450010076623702270829426400000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (33 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((315688438529 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (33 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 158451441034536738387030751562400000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (33 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((176992294739 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (33 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 6552511055046475978765290151200000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (33 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((7319239007 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_34 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (34 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 3 then (if k.val = 0 then (35 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -8) else if j.val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (34 : Fin 88)), (alphaG (n3 2) (m3 2) (34 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 3 then (if k.val = 0 then (35 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -8) else if j.val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5489243206320888310469 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (34 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (34 : Fin 88)))) =
        {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (34 : Fin 88) = 110787158727778557220000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (34 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 13134658508587531338074511191220000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (34 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((118557589701 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (34 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 42257033615108210865381157950620000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (34 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((381425375471 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (34 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 42257342441292755547959457805480000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (34 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((190714081517 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (34 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 13138124162790059468584873052680000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (34 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((59294435897 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_35 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (35 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -5) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else -5) else if j.val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (35 : Int) else if k.val = 1 then -4 else if k.val = 2 then -7 else -6) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 4 then (if k.val = 0 then (35 : Int) else if k.val = 1 then -4 else if k.val = 2 then -7 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (35 : Fin 88)), (alphaG (n3 2) (m3 2) (35 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -5) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else -5) else if j.val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (35 : Int) else if k.val = 1 then -4 else if k.val = 2 then -7 else -6) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 4 then (if k.val = 0 then (35 : Int) else if k.val = 1 then -4 else if k.val = 2 then -7 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (6247811224788688620645 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (35 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (35 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (35 : Fin 88) = 3882148474330116064984000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (35 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 25556957250699136175145369520656000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (35 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((3291599667 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (35 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1244287611508725652812612898505640000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (35 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((64103040867 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (35 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 671229691756756316599889862852464000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (35 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((86450801173 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (35 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 671229446272979690809330609654208000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (35 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((21612692389 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (35 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1244288264680206458854640832063640000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (35 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((64103074517 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (35 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 25556502860748809732380427403392000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (35 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((411442643 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_36 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (36 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else -1) else if j.val = 1 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else 0) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 4) else if j.val = 2 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -6 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else -6) else if j.val = 4 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (36 : Fin 88)), (alphaG (n3 2) (m3 2) (36 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else -1) else if j.val = 1 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else 0) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 4) else if j.val = 2 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -6 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else -6) else if j.val = 4 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (8644252691414433503333 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (36 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (36 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (36 : Fin 88) = 35086177508994641449945000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (36 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 11244036816419257429120454147795000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (36 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((320469131 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (36 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1272642227466340525976695979348170000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (36 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((18135948653 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (36 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 5148146994207174295388542873629465000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (36 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((146728636737 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (36 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 1287793812819263309366952127294480000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (36 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((2293983529 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (36 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 19646523368200727904090098486557320000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (36 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((69993815097 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (36 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 1287793790679885301191333372379185000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (36 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((36703735833 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 2 (36 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 5148146989610885041710244843686670000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 2) (m3 2) (36 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((73364318303 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 2 (36 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 1272642199818432648888918516791510000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 2) (m3 2) (36 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((18135948259 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 2 (36 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 11244089375513165903093346165405000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 2) (m3 2) (36 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((320470629 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_37 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (37 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 6) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 3 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -8 else if k.val = 2 then -5 else 6) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (37 : Fin 88)), (alphaG (n3 2) (m3 2) (37 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 6) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 3 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -8 else if k.val = 2 then -5 else 6) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (868598180784515496955184 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (37 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (37 : Fin 88)))) =
        {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (37 : Fin 88) = 36585578988250089342318000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (37 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 59987051194966023449426838199452000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (37 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((819818257 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (37 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 410050114940506138969375387737558000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (37 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((11207971181 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (37 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 436726245980319155938231001545770000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (37 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((2387422903 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (37 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 11478385037068392771341584642664892000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (37 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((156870348297 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (37 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 5907637462444380473023383640731450000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (37 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((6458979331 : ℚ)/40000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (37 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 5907638154716706088691574176072646000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (37 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((161474502197 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 2 (37 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 11478358845342638346137874209181738000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 2) (m3 2) (37 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((313739980691 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 2 (37 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 436740332891652791752631367668490000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 2) (m3 2) (37 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((2387499911 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 2 (37 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 410064498780398843421500856113166000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 2) (m3 2) (37 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((11208364337 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 2 (37 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 59991244890128709592417880084838000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 2) (m3 2) (37 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((1639751141 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_38 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (38 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 3 else if k.val = 2 then -4 else -5) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else 5) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 1) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else 3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (38 : Fin 88)), (alphaG (n3 2) (m3 2) (38 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 3 else if k.val = 2 then -4 else -5) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else 5) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 1) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else 3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (8667858960464947783353 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (38 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (38 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (38 : Fin 88) = 28229447473206479825325000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (38 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 9482373907373831786054913255075000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (38 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((335903631 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (38 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1167981676382719757306245150277625000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (38 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((8274917017 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (38 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 1086412340517309028572027832328175000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (38 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((38485072779 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (38 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 4037077701222219104146233146058450000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (38 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((71504724013 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (38 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 15627539346114261382634554203667200000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (38 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((2162460871 : ℚ)/3906250000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (38 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 4037077687587395974587503390426475000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (38 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((143009447543 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 2 (38 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 1086413149178061346044848908588125000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 2) (m3 2) (38 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((1539404057 : ℚ)/40000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 2 (38 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 1167982536110542553809588230550500000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 2) (m3 2) (38 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((2068730777 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 2 (38 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 9480662186596846437944224848375000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 2) (m3 2) (38 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((67168599 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_39 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (39 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 2) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else 7) else if j.val = 1 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else 7) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -8) else if j.val = 3 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else 7) else if j.val = 4 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (39 : Fin 88)), (alphaG (n3 2) (m3 2) (39 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 2) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else 7) else if j.val = 1 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else 7) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -8) else if j.val = 3 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else 7) else if j.val = 4 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (10711932302373422718787 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (39 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (39 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (39 : Fin 88) = 6876744670358923049368000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (39 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 2243534950443922368365860475552000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (39 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((81562391 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (39 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 422288674481290442937244597573424000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (39 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((30704111809 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (39 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 2930102139786985285294467177145984000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (39 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((26630534143 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (39 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 83738040837164343548128298761680000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (39 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((1217698851 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (39 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 83737958976395787595508319085008000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (39 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((6088488303 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (39 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 2930102170587924663832083515265256000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (39 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((426088550767 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 2 (39 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 422288624563000880801822182211112000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 2) (m3 2) (39 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((61408216359 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 2 (39 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2243526175717722990380049481984000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 2) (m3 2) (39 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((10195259 : ℚ)/31250000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_40 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (40 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 1) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 4 else -1) else if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (40 : Fin 88)), (alphaG (n3 2) (m3 2) (40 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 1) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 4 else -1) else if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3350173356963256779413284 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (40 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (40 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (40 : Fin 88) = 35638678338595255721736000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (40 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 387701563828464866667948471003096000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (40 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((10878674011 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (40 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 54280580691953693738268027295416000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (40 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((1523080631 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (40 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 5824864754742935062228282245637416000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (40 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((163442221381 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (40 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 11141989558681696962659237225227608000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (40 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((312637563403 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (40 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 410502814847299170854886646757808000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (40 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((5759231739 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (40 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 410502152359907534707678035407304000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (40 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((11518444889 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 2 (40 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 11141990859422178964708880557148136000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 2) (m3 2) (40 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((312637599901 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 2 (40 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 5824864759019576462859712932245736000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 2) (m3 2) (40 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((163442221501 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 2 (40 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 54280393553253737774580232459680000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 2) (m3 2) (40 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((76153769 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 2 (40 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 387700901447989265536525626817800000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 2) (m3 2) (40 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((435146217 : ℚ)/40000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_41 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (41 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else 7) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else 4) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 8) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 6) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 6) else if j.val = 4 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 1 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 4) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (41 : Fin 88)), (alphaG (n3 2) (m3 2) (41 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else 7) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else 4) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 8) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 6) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 6) else if j.val = 4 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 1 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 4) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1850595070273425045435 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (41 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (41 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (41 : Fin 88) = 7370924582478806573736000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (41 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 1064041805512085854059579212594160000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (41 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((14435662631 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (41 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 264132271101074217188669006415888000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (41 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((17917173629 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (41 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 2423237156222319029716467163200000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (41 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((1643781 : ℚ)/5000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (41 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 297425943407280338952796362705288000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (41 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((40351239533 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (41 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 4114878075297390734026356698488056000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (41 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((558258062371 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (41 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 297425938785710625738584640972816000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (41 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((20175619453 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 2 (41 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 2423267192739992630853255137400000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 2) (m3 2) (41 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((13150411 : ℚ)/40000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 2 (41 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 264132232263672592107837169400904000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 2) (m3 2) (41 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((35834341989 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 2 (41 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 1064041811762629900001607187122288000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 2) (m3 2) (41 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((72178313579 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_42 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (42 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 3) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 6 else if k.val = 2 then -4 else 2) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else 8) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 0 else if k.val = 2 then -3 else 1) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else 8) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 6 else if k.val = 2 then -4 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (42 : Fin 88)), (alphaG (n3 2) (m3 2) (42 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 3) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 6 else if k.val = 2 then -4 else 2) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else 8) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 0 else if k.val = 2 then -3 else 1) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else 8) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 6 else if k.val = 2 then -4 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1814988654327369347502 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (42 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (42 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (42 : Fin 88) = 32474987370003040055260000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (42 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 402754989446751442843690373659880000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (42 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((6201003019 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (42 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 10658986696389374801275596056020000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (42 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((328221427 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (42 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 13795035589868800932915705635321640000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (42 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((212394779907 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (42 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2029043943787021415902927296834760000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (42 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((31240103663 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (42 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 2029044178938404962094940336972420000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (42 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((62480214567 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (42 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 13795036053254395715489084183826580000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (42 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((424789574083 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 2 (42 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 10659162613395958107743575399440000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 2) (m3 2) (42 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((82056711 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 2 (42 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 402754465397880253104633001929260000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 2) (m3 2) (42 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((12401989901 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_43 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (43 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else -4) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 1) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -2) else if j.val = 2 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (43 : Fin 88)), (alphaG (n3 2) (m3 2) (43 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else -4) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 1) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -2) else if j.val = 2 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (9567213504813701530379 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (43 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (43 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (43 : Fin 88) = 551135578998253609078000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (43 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 96956878677852701173269445711068000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (43 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((87961004853 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (43 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 174665977994730932441869324948598000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (43 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((316920163841 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (43 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 3944906100876674140547217929958000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (43 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((7157777961 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (43 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 3944922291035442793245238205286000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (43 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((7157807337 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (43 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 174666023495382063379690783210122000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (43 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((316920246399 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (43 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 96956870438375795149377989994968000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (43 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((43980498689 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_44 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (44 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 4) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -2) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 8) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 4 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (44 : Fin 88)), (alphaG (n3 2) (m3 2) (44 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 4) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -2) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 8) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 4 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2634149706420207900938 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (44 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (44 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (44 : Fin 88) = 2047683600843706309806000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (44 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 358536570873675149881757366395434000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (44 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((175093735539 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (44 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 14415964885715553831442325268582000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (44 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((7040132997 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (44 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 650889378978494835491392465875546000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (44 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((317866187291 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (44 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 650889206463199148009979571029852000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (44 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((158933051521 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (44 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 14415867147729601960496451918396000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (44 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((3520042633 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (44 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 358536612494892020630931819512190000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (44 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((35018751173 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_45 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (45 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 6) else if j.val = 4 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (45 : Fin 88)), (alphaG (n3 2) (m3 2) (45 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 6) else if j.val = 4 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2293317858417120460115 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (45 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (45 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (45 : Fin 88) = 110216540174478019604000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (45 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 42211158503811832549624136234764000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (45 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((382983882791 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (45 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12897109096611381295628307440184000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (45 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((58508047323 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (45 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 12897113973142201315408284819164000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (45 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((117016138891 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (45 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 42211158600912604443339271505888000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (45 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((47872985459 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_46 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (46 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 4) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else -6) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -6) else if j.val = 4 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (46 : Fin 88)), (alphaG (n3 2) (m3 2) (46 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 4) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else -6) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -6) else if j.val = 4 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2618440071482095618218 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (46 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (46 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (46 : Fin 88) = 110541610394793142487000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (46 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 12995411713987074368520988373585000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (46 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((23512253291 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (46 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 42262936404303514797783548653471000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (46 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((382326042233 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (46 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 42299634514292412222984182361444000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (46 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((95664506703 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (46 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 12983627762210141097711280611500000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (46 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((234909329 : ℚ)/2000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_47 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (47 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -2) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else -1) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -1) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else if j.val = 4 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (47 : Fin 88)), (alphaG (n3 2) (m3 2) (47 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -2) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else -1) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -1) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else if j.val = 4 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (9401517278057570158278 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (47 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (47 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (47 : Fin 88) = 3158873760010093011788000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (47 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 22336076732707708585111736254796000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (47 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((7070898817 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (47 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 553642961866332668504063660194468000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (47 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((175265934611 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (47 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 1003457789442532776638794559638136000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (47 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((158831575061 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (47 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1003457949670086505630742396560860000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (47 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((63532640169 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (47 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 553642954307147760799911082985784000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (47 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((87632966109 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (47 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 22336027991285591629376564365956000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (47 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((7070883387 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    (((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (32 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else -3) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else 5) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else 4) else if j.val = 2 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else -1) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else 4) else if j.val = 4 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (32 : Fin 88)), (alphaG (n3 2) (m3 2) (32 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else -3) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else 5) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else 4) else if j.val = 2 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else -1) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else 4) else if j.val = 4 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (15233006572800959698805 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (33 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else -2) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (33 : Fin 88)), (alphaG (n3 2) (m3 2) (33 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else -2) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (701788092790881936660 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (34 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 3 then (if k.val = 0 then (35 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -8) else if j.val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (34 : Fin 88)), (alphaG (n3 2) (m3 2) (34 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 3 then (if k.val = 0 then (35 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -8) else if j.val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5489243206320888310469 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (35 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -5) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else -5) else if j.val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (35 : Int) else if k.val = 1 then -4 else if k.val = 2 then -7 else -6) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 4 then (if k.val = 0 then (35 : Int) else if k.val = 1 then -4 else if k.val = 2 then -7 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (35 : Fin 88)), (alphaG (n3 2) (m3 2) (35 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -5) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else -5) else if j.val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (35 : Int) else if k.val = 1 then -4 else if k.val = 2 then -7 else -6) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 4 then (if k.val = 0 then (35 : Int) else if k.val = 1 then -4 else if k.val = 2 then -7 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (6247811224788688620645 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (36 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else -1) else if j.val = 1 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else 0) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 4) else if j.val = 2 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -6 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else -6) else if j.val = 4 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (36 : Fin 88)), (alphaG (n3 2) (m3 2) (36 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else -1) else if j.val = 1 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else 0) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 4) else if j.val = 2 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -6 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else -6) else if j.val = 4 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (8644252691414433503333 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (37 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 6) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 3 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -8 else if k.val = 2 then -5 else 6) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (37 : Fin 88)), (alphaG (n3 2) (m3 2) (37 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 6) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 3 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -8 else if k.val = 2 then -5 else 6) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (868598180784515496955184 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (38 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 3 else if k.val = 2 then -4 else -5) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else 5) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 1) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else 3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (38 : Fin 88)), (alphaG (n3 2) (m3 2) (38 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 3 else if k.val = 2 then -4 else -5) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else 5) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 1) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else 3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (8667858960464947783353 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (39 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 2) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else 7) else if j.val = 1 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else 7) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -8) else if j.val = 3 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else 7) else if j.val = 4 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (39 : Fin 88)), (alphaG (n3 2) (m3 2) (39 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 2) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else 7) else if j.val = 1 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else 7) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -8) else if j.val = 3 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else 7) else if j.val = 4 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (10711932302373422718787 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (40 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 1) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 4 else -1) else if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (40 : Fin 88)), (alphaG (n3 2) (m3 2) (40 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 1) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 4 else -1) else if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3350173356963256779413284 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (41 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else 7) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else 4) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 8) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 6) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 6) else if j.val = 4 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 1 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 4) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (41 : Fin 88)), (alphaG (n3 2) (m3 2) (41 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else 7) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else 4) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 8) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 6) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 6) else if j.val = 4 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 1 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 4) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1850595070273425045435 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (42 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 3) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 6 else if k.val = 2 then -4 else 2) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else 8) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 0 else if k.val = 2 then -3 else 1) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else 8) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 6 else if k.val = 2 then -4 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (42 : Fin 88)), (alphaG (n3 2) (m3 2) (42 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 3) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 6 else if k.val = 2 then -4 else 2) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else 8) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 0 else if k.val = 2 then -3 else 1) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else 8) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 6 else if k.val = 2 then -4 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1814988654327369347502 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (43 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else -4) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 1) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -2) else if j.val = 2 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (43 : Fin 88)), (alphaG (n3 2) (m3 2) (43 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else -4) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 1) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -2) else if j.val = 2 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (9567213504813701530379 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (44 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 4) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -2) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 8) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 4 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (44 : Fin 88)), (alphaG (n3 2) (m3 2) (44 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 4) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -2) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 8) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 4 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2634149706420207900938 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (45 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 6) else if j.val = 4 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (45 : Fin 88)), (alphaG (n3 2) (m3 2) (45 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 6) else if j.val = 4 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2293317858417120460115 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (46 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 4) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else -6) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -6) else if j.val = 4 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (46 : Fin 88)), (alphaG (n3 2) (m3 2) (46 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 4) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else -6) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -6) else if j.val = 4 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2618440071482095618218 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (47 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -2) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else -1) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -1) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else if j.val = 4 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (47 : Fin 88)), (alphaG (n3 2) (m3 2) (47 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -2) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else -1) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -1) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else if j.val = 4 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (9401517278057570158278 : ℚ)/10^30) :=
  ⟨L3C.pn_2_32, L3C.pn_2_33, L3C.pn_2_34, L3C.pn_2_35, L3C.pn_2_36, L3C.pn_2_37, L3C.pn_2_38, L3C.pn_2_39, L3C.pn_2_40, L3C.pn_2_41, L3C.pn_2_42, L3C.pn_2_43, L3C.pn_2_44, L3C.pn_2_45, L3C.pn_2_46, L3C.pn_2_47⟩

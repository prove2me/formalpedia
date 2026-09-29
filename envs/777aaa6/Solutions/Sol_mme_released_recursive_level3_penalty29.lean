-- Prove2me | solution 1 for mme_released_recursive_level3_penalty29
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T09:28:16.772425+00:00
-- url     : https://prove2.me/submissions/e5a0b703-d433-4230-8eb1-7eaebbc27c26

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

theorem pn_4_64 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (64 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else -1) else if j.val = 1 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else 0) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 4) else if j.val = 2 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -8) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 4 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (64 : Fin 88)), (alphaG (n3 4) (m3 4) (64 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else -1) else if j.val = 1 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else 0) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 4) else if j.val = 2 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -8) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 4 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (7061667401283322549845 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (64 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (64 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (64 : Fin 88) = 34713345380975204700145000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (64 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 11099991423752048298700620117645000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (64 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((319761501 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (64 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1259179009823837582919454922397170000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (64 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((18136814473 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (64 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 5093296846513904620916882187061140000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (64 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((36681114933 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (64 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 1274185850597090609559495021489745000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (64 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((36705936481 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 4 (64 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 19437821806074433136210208772024315000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 4) (m3 4) (64 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((559952421547 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 4 (64 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 1274187104824972569574616042428740000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 4) (m3 4) (64 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((9176493153 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 4 (64 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 5093296833947673593003858085608650000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 4) (m3 4) (64 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((14672445937 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 4 (64 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 1259180245271799691826990200557720000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 4) (m3 4) (64 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((4534208067 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 4 (64 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 11097692497740847834794148314875000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 4) (m3 4) (64 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((12787811 : ℚ)/40000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_65 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (65 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -5) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else -5) else if j.val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 4 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (65 : Fin 88)), (alphaG (n3 4) (m3 4) (65 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -5) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else -5) else if j.val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 4 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3827121547613330199116 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (65 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (65 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (65 : Fin 88) = 3877674156037861098468000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (65 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 25545180482268307701352210835796000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (65 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((6587758397 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (65 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1242856868305656374256617478467688000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (65 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((160258033333 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (65 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 670434826292928911034569722373736000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (65 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((86448061301 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (65 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 670435351136125930759069400017536000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (65 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((5403008061 : ℚ)/31250000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 4 (65 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1242855508967592604404220105017948000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 4) (m3 4) (65 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((320515716111 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 4 (65 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 25546420853288970312171083287296000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 4) (m3 4) (65 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((102938723 : ℚ)/15625000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_66 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (66 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 1) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 4 else -1) else if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (66 : Fin 88)), (alphaG (n3 4) (m3 4) (66 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 1) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 4 else -1) else if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3351156373651427359556300 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (66 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (66 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (66 : Fin 88) = 35536457924913754292998000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (66 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 386590009072686371808338534900650000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (66 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((435147487 : ℚ)/40000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (66 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 54127481189883028097277540810948000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (66 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((761576763 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (66 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 5808164564347916972417248025438592000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (66 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((2553787761 : ℚ)/15625000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (66 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 11110000581461835910482562576925916000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (66 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((156318345021 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 4 (66 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 409346161495390092093753402413174000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 4) (m3 4) (66 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((11519047913 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 4 (66 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 409346816467846106179158776659312000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 4) (m3 4) (66 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((1439883293 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 4 (66 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 11109999719134147904525400903036448000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 4) (m3 4) (66 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((19539791611 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 4 (66 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 5808164758448050158296173973793668000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 4) (m3 4) (66 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((81721211083 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 4 (66 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 54127603399761831875678554431070000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 4) (m3 4) (66 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((304631393 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 4 (66 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 386590229896235917222407711590222000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 4) (m3 4) (66 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((10878693389 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_67 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (67 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 2) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else 7) else if j.val = 1 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else 7) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -8) else if j.val = 3 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else 7) else if j.val = 4 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (67 : Fin 88)), (alphaG (n3 4) (m3 4) (67 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 2) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else 7) else if j.val = 1 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else 7) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -8) else if j.val = 3 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else 7) else if j.val = 4 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (8404943956088741555847 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (67 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (67 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (67 : Fin 88) = 7086635326284777546190000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (67 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 2311789406023762165948963565620000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (67 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((163109099 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (67 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 435158038205095931069337728681910000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (67 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((61405450989 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (67 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 3019561654610723870023703847899860000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (67 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((213046214147 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (67 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 86286338938339715333979184797230000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (67 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((12175924817 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 4 (67 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 86286069546984421944445543930570000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 4) (m3 4) (67 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((12175886803 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 4 (67 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 3019561771738632542858507131328180000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 4) (m3 4) (67 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((213046222411 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 4 (67 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 435157832614718480221656336163820000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 4) (m3 4) (67 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((30702710989 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 4 (67 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2311831224258822572421263632810000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 4) (m3 4) (67 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((326224099 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_68 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (68 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 2) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (38 : Int) else if k.val = 1 then -7 else if k.val = 2 then -5 else -8) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else 8) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 0 else if k.val = 2 then -3 else 1) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else 8) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 6 else if k.val = 2 then -4 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (68 : Fin 88)), (alphaG (n3 4) (m3 4) (68 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 2) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (38 : Int) else if k.val = 1 then -7 else if k.val = 2 then -5 else -8) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else 8) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 0 else if k.val = 2 then -3 else 1) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else 8) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 6 else if k.val = 2 then -4 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2182862611770108868425 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (68 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (68 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (68 : Fin 88) = 32297437831669942155216000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (68 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 400524455113984483503587550008592000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (68 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((12401121637 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (68 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 10600651900053510924518538347088000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (68 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((328219593 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (68 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 13719613537422705002388271328443488000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (68 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((212394766559 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (68 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2017980117985398380359397345924832000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (68 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((31240560451 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 4 (68 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 2017980347943155741849385491062752000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 4) (m3 4) (68 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((31240564011 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 4 (68 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 13719613969497828314468757480923136000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 4) (m3 4) (68 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((829667083 : ℚ)/1953125000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 4 (68 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 10600807153837167761930478470400000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 4) (m3 4) (68 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((820561 : ℚ)/2500000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 4 (68 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 400523944652979553960151786819712000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 4) (m3 4) (68 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((1550138229 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_69 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (69 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (26 : Int) else if k.val = 1 then -1 else if k.val = 2 then -6 else -5) else if j.val = 1 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else 8) else if j.val = 2 then (if k.val = 0 then (26 : Int) else if k.val = 1 then -1 else if k.val = 2 then -6 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 7) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else -6) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else -6) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else 4) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else 0) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (69 : Fin 88)), (alphaG (n3 4) (m3 4) (69 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (26 : Int) else if k.val = 1 then -1 else if k.val = 2 then -6 else -5) else if j.val = 1 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else 8) else if j.val = 2 then (if k.val = 0 then (26 : Int) else if k.val = 1 then -1 else if k.val = 2 then -6 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 7) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else -6) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else -6) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else 4) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else 0) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (13018803010484841294606 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (69 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (69 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (69 : Fin 88) = 7869749807762197479852000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (69 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 1136050924262606050694908351732020000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (69 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((28871335227 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (69 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 281715090065180176548483876333252000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (69 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((35797210451 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (69 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 2586959195899472189136333437172000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (69 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((328721911 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (69 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 317859390873289615068470070351396000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (69 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((40390024923 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 4 (69 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 4393325284612679077483985082304932000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 4) (m3 4) (69 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((558254759291 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 4 (69 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 317859246148590650321658415873116000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 4) (m3 4) (69 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((40390006533 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 4 (69 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 2586739834493330625643780042524000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 4) (m3 4) (69 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((328694037 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 4 (69 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 281715207969771796441726519475916000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 4) (m3 4) (69 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((35797225433 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 4 (69 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 1136050964799687310477987570449672000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 4) (m3 4) (69 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((72178340643 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_70 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (70 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 4) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -2) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 6 else if k.val = 2 then -4 else 3) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 6 else if k.val = 2 then -4 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (70 : Fin 88)), (alphaG (n3 4) (m3 4) (70 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 4) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -2) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 6 else if k.val = 2 then -4 else 3) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 6 else if k.val = 2 then -4 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2395588807000913189464 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (70 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (70 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (70 : Fin 88) = 2051930839037285587360000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (70 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 359276990736920490556939270971520000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (70 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((43773038533 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (70 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 14435510318805974925908802495200000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (70 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((1407017239 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (70 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 652252927271855420184218953069760000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (70 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((158936381983 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (70 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 652252934151979523476237527487840000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (70 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((317872767319 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 4 (70 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 14435472062607411914756311755360000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 4) (m3 4) (70 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((7035067551 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 4 (70 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 359277004495116766301939134220320000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 4) (m3 4) (70 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((175092160837 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_71 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (71 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -7 else if k.val = 2 then -3 else 0) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -7 else if k.val = 2 then -3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 1) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -2) else if j.val = 2 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (71 : Fin 88)), (alphaG (n3 4) (m3 4) (71 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -7 else if k.val = 2 then -3 else 0) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -7 else if k.val = 2 then -3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 1) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -2) else if j.val = 2 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5936792413960182261074 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (71 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (71 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (71 : Fin 88) = 517324085058055137746000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (71 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 91003933304247358985748848599884000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (71 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((87956404827 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (71 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 163953937340268892571037054549388000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (71 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((158463468139 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (71 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 3704174864298047250611690267688000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (71 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((1790064957 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (71 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 3704119223506078831491349996658000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (71 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((7160152273 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 4 (71 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 163954006511154981598531467429302000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 4) (m3 4) (71 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((316927069987 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 4 (71 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 91003913814579778508579589157080000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 4) (m3 4) (71 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((8795638599 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_72 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (72 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 6) else if j.val = 4 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (72 : Fin 88)), (alphaG (n3 4) (m3 4) (72 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 6) else if j.val = 4 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1986108336616459095069 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (72 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (72 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (72 : Fin 88) = 110206010965453588824000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (72 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 42207338874163470253154994569184000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (72 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((95746453629 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (72 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12895666117044515252921999275776000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (72 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((3656693157 : ℚ)/31250000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (72 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 12895667095784098637115321621720000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (72 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((23402837981 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (72 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 42207338878461504680807684533320000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (72 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((76597162911 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_73 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (73 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 3 then (if k.val = 0 then (35 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -8) else if j.val = 4 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (73 : Fin 88)), (alphaG (n3 4) (m3 4) (73 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 3 then (if k.val = 0 then (35 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -8) else if j.val = 4 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2161436680094926993893 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (73 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (73 : Fin 88)))) =
        {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (73 : Fin 88) = 110864782856322348018000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (73 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 13141967363244375788144143640718000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (73 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((118540505151 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (73 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 42291916661767780334161816909224000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (73 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((95368239517 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (73 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 42287498943408289475364531160716000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (73 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((190716555131 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (73 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 13143399887901902420329508289342000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (73 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((118553426519 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_74 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (74 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else 5) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else 5) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (74 : Fin 88)), (alphaG (n3 4) (m3 4) (74 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else 5) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else 5) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (4846864407240136327037 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (74 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (74 : Fin 88)))) =
        {(⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (74 : Fin 88) = 911604919615666516775000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (74 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 6669376214975331055571296684725000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (74 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((7316081859 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (74 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 161314325746458451728952453962775000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (74 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((176956401041 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (74 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 287818767900490134044162262863975000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (74 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((315727528129 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (74 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 287818741038227967729317013055050000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (74 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((157863749331 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 4 (74 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 161314319984203754838324401428000000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 4) (m3 4) (74 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((1105977467 : ℚ)/6250000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 4 (74 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 6669388731310877378672572005475000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 4) (m3 4) (74 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((7316095589 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_75 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (75 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 1) else if j.val = 1 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else if j.val = 2 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -6) else if j.val = 1 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else 1) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else 4) else if j.val = 3 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else 1) else if j.val = 4 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 3 else if k.val = 2 then 1 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (75 : Fin 88)), (alphaG (n3 4) (m3 4) (75 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 1) else if j.val = 1 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else if j.val = 2 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -6) else if j.val = 1 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else 1) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else 4) else if j.val = 3 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else 1) else if j.val = 4 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 3 else if k.val = 2 then 1 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2002834186251526559478 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (75 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (75 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (75 : Fin 88) = 4639269892467041474888000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (75 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 1524188838781949759077491694960000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (75 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((32854067 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (75 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 58147979055933265337833017428888000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (75 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((12533864251 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (75 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 302410830385251838296120935508144000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (75 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((32592502419 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (75 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1957552041787426529089349426452696000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (75 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((421952610467 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 4 (75 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 1957551637173502857576327194095776000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 4) (m3 4) (75 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((105488130813 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 4 (75 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 302410236897372304664906177510968000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 4) (m3 4) (75 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((65184876911 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 4 (75 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 58148612478648033325340791261968000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 4) (m3 4) (75 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((6267000393 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 4 (75 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 1524365850124696839044966046600000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 4) (m3 4) (75 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((13143153 : ℚ)/40000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_76 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (76 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -2) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else -1) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else 3) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else if j.val = 4 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (76 : Fin 88)), (alphaG (n3 4) (m3 4) (76 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -2) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else -1) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else 3) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else if j.val = 4 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (8571917814722612623114 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (76 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (76 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (76 : Fin 88) = 3137014326140716983246000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (76 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 22190829338484019673913210731046000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (76 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((7073869301 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (76 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 549805353880864519130191781613876000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (76 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((87631948203 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (76 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 996510867865872538247580139739370000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (76 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((63532439719 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (76 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 996510966650453668418757942155910000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (76 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((63532446017 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 4 (76 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 549805260124917353762583303340674000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 4) (m3 4) (76 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((175263866519 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 4 (76 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 22191048280124884012973622419124000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 4) (m3 4) (76 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((3536969547 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_77 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (77 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else -3) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -2) else if j.val = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -7 else if k.val = 2 then -5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (77 : Fin 88)), (alphaG (n3 4) (m3 4) (77 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else -3) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -2) else if j.val = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -7 else if k.val = 2 then -5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (7798388528960814413022 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (77 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (77 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (77 : Fin 88) = 110602898391032769120000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (77 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 12998720829753490301579054322720000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (77 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((117526041531 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (77 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 42320293151888397447763066476000000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (77 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((15305310717 : ℚ)/40000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (77 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 42317287881455142346804877035200000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (77 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((38260559621 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (77 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 12966596527935739023853002166080000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (77 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((58617797167 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_78 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (78 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else 5) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 0 else if k.val = 2 then -3 else -3) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else 7) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (78 : Fin 88)), (alphaG (n3 4) (m3 4) (78 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else 5) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 0 else if k.val = 2 then -3 else -3) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else 7) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (7643680078408989044855 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (78 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (78 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (78 : Fin 88) = 28413854865319997008170000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (78 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 9552305177469419574632328546390000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (78 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((336184767 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (78 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1174182905691471525177293935894350000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (78 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((8264861711 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (78 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 1095025893693909522251552436488490000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (78 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((38538448897 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (78 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 4063383965240711843646564699110100000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (78 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((14300713453 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 4 (78 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 15729563352499680600819777792073410000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 4) (m3 4) (78 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((553587798173 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 4 (78 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 4063386257357969974145403351175830000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 4) (m3 4) (78 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((143007215199 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 4 (78 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 1095025153569817990396270367676330000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 4) (m3 4) (78 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((38538422849 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 4 (78 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 1174182778539471002870307324333600000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 4) (m3 4) (78 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((516553801 : ℚ)/12500000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 4 (78 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 9552253549495129288197764701500000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 4) (m3 4) (78 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((6723659 : ℚ)/20000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_4_79 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (79 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 3 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (79 : Fin 88)), (alphaG (n3 4) (m3 4) (79 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 3 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (911427032825204091269530 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 4 (79 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 4 (79 : Fin 88)))) =
        {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 4 (79 : Fin 88) = 33357649585939236593184000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 4 (79 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 55006795556762061510982050186144000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 4) (m3 4) (79 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((1649000941 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 4 (79 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 373678877323514510888916605374272000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 4) (m3 4) (79 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((5601097229 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 4 (79 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 400686297672931769374693934103168000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 4) (m3 4) (79 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((3002956613 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 4 (79 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 10462758943361886001081904728716288000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 4) (m3 4) (79 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((9801686301 : ℚ)/31250000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 4 (79 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 5386696249215599983476080337122880000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 4) (m3 4) (79 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((16148308757 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 4 (79 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 5386692805405214380695233693399904000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 4) (m3 4) (79 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((161482984331 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 4 (79 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 10462764785754065080823558605334784000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 4) (m3 4) (79 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((39206767097 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 4 (79 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 400683364134511882706349456315840000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 4) (m3 4) (79 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((1201173851 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 4 (79 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 373675590694373757053752788734304000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 4) (m3 4) (79 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((11202095931 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 4 (79 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 55005876820377165572527800712416000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 4) (m3 4) (79 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((1648973399 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    (((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (64 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else -1) else if j.val = 1 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else 0) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 4) else if j.val = 2 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -8) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 4 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (64 : Fin 88)), (alphaG (n3 4) (m3 4) (64 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else -1) else if j.val = 1 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else 0) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 4) else if j.val = 2 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -8) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -4 else -3) else if j.val = 4 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (7061667401283322549845 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (65 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -5) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else -5) else if j.val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 4 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (65 : Fin 88)), (alphaG (n3 4) (m3 4) (65 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -5) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else -5) else if j.val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 4 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3827121547613330199116 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (66 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 1) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 4 else -1) else if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (66 : Fin 88)), (alphaG (n3 4) (m3 4) (66 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 1) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 4 else -1) else if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3351156373651427359556300 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (67 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 2) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else 7) else if j.val = 1 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else 7) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -8) else if j.val = 3 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else 7) else if j.val = 4 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (67 : Fin 88)), (alphaG (n3 4) (m3 4) (67 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 2) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else 7) else if j.val = 1 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else 7) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -8) else if j.val = 3 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else 7) else if j.val = 4 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (8404943956088741555847 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (68 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 2) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (38 : Int) else if k.val = 1 then -7 else if k.val = 2 then -5 else -8) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else 8) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 0 else if k.val = 2 then -3 else 1) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else 8) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 6 else if k.val = 2 then -4 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (68 : Fin 88)), (alphaG (n3 4) (m3 4) (68 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 2) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (38 : Int) else if k.val = 1 then -7 else if k.val = 2 then -5 else -8) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else 8) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 0 else if k.val = 2 then -3 else 1) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else 8) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 6 else if k.val = 2 then -4 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2182862611770108868425 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (69 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (26 : Int) else if k.val = 1 then -1 else if k.val = 2 then -6 else -5) else if j.val = 1 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else 8) else if j.val = 2 then (if k.val = 0 then (26 : Int) else if k.val = 1 then -1 else if k.val = 2 then -6 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 7) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else -6) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else -6) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else 4) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else 0) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (69 : Fin 88)), (alphaG (n3 4) (m3 4) (69 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (26 : Int) else if k.val = 1 then -1 else if k.val = 2 then -6 else -5) else if j.val = 1 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else 8) else if j.val = 2 then (if k.val = 0 then (26 : Int) else if k.val = 1 then -1 else if k.val = 2 then -6 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 7) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else -6) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else -6) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else 4) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else 0) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (13018803010484841294606 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (70 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 4) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -2) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 6 else if k.val = 2 then -4 else 3) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 6 else if k.val = 2 then -4 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (70 : Fin 88)), (alphaG (n3 4) (m3 4) (70 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 4) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -2) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 6 else if k.val = 2 then -4 else 3) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 6 else if k.val = 2 then -4 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2395588807000913189464 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (71 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -7 else if k.val = 2 then -3 else 0) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -7 else if k.val = 2 then -3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 1) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -2) else if j.val = 2 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (71 : Fin 88)), (alphaG (n3 4) (m3 4) (71 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -7 else if k.val = 2 then -3 else 0) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -7 else if k.val = 2 then -3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 1) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -2) else if j.val = 2 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5936792413960182261074 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (72 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 6) else if j.val = 4 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (72 : Fin 88)), (alphaG (n3 4) (m3 4) (72 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 6) else if j.val = 4 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1986108336616459095069 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (73 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 3 then (if k.val = 0 then (35 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -8) else if j.val = 4 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (73 : Fin 88)), (alphaG (n3 4) (m3 4) (73 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 3 then (if k.val = 0 then (35 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -8) else if j.val = 4 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2161436680094926993893 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (74 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else 5) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else 5) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (74 : Fin 88)), (alphaG (n3 4) (m3 4) (74 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else 5) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else 5) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (4846864407240136327037 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (75 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 1) else if j.val = 1 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else if j.val = 2 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -6) else if j.val = 1 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else 1) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else 4) else if j.val = 3 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else 1) else if j.val = 4 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 3 else if k.val = 2 then 1 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (75 : Fin 88)), (alphaG (n3 4) (m3 4) (75 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 1) else if j.val = 1 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else if j.val = 2 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -6) else if j.val = 1 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else 1) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else 4) else if j.val = 3 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else 1) else if j.val = 4 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 3 else if k.val = 2 then 1 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2002834186251526559478 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (76 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -2) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else -1) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else 3) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else if j.val = 4 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (76 : Fin 88)), (alphaG (n3 4) (m3 4) (76 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -2) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else -1) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else 3) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else if j.val = 4 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (8571917814722612623114 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (77 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else -3) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -2) else if j.val = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -7 else if k.val = 2 then -5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (77 : Fin 88)), (alphaG (n3 4) (m3 4) (77 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else -3) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -2) else if j.val = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -7 else if k.val = 2 then -5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (7798388528960814413022 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (78 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else 5) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 0 else if k.val = 2 then -3 else -3) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else 7) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (78 : Fin 88)), (alphaG (n3 4) (m3 4) (78 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else 5) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 0 else if k.val = 2 then -3 else -3) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else 7) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (7643680078408989044855 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (79 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 3 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 (79 : Fin 88)), (alphaG (n3 4) (m3 4) (79 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 3 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (911427032825204091269530 : ℚ)/10^30) :=
  ⟨L3C.pn_4_64, L3C.pn_4_65, L3C.pn_4_66, L3C.pn_4_67, L3C.pn_4_68, L3C.pn_4_69, L3C.pn_4_70, L3C.pn_4_71, L3C.pn_4_72, L3C.pn_4_73, L3C.pn_4_74, L3C.pn_4_75, L3C.pn_4_76, L3C.pn_4_77, L3C.pn_4_78, L3C.pn_4_79⟩

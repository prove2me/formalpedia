-- Prove2me | solution 1 for mme_released_recursive_level3_penalty18
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T08:26:08.390567+00:00
-- url     : https://prove2.me/submissions/80676cb7-44b6-4e59-bd9e-b76523d6e363

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

theorem pn_2_80 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (80 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 3 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 3 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (80 : Fin 88)), (alphaG (n3 2) (m3 2) (80 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 3 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 3 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (888565128145945464454483 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (80 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (80 : Fin 88)))) =
        {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (80 : Fin 88) = 26031955097479542659200000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (80 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 42936946120619806213306272736000000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (80 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((164939383 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (80 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 288907520485645598669618186144000000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (80 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((1109818757 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (80 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 315699544919713510247066853763200000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (80 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((12127385121 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (80 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 8164466745883457988177208612617600000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (80 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((313632484203 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (80 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 4203964121128572257426191349958400000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (80 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((80746223351 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (80 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 4203962138925351359846415565174400000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (80 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((161492370557 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 2 (80 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 8164436870049870814805280355145600000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 2) (m3 2) (80 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((313631336543 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 2 (80 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 315715407960127351161018005148800000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 2) (m3 2) (80 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((12127994489 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 2 (80 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 288924060461019794441596647366400000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 2) (m3 2) (80 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((5549411471 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 2 (80 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 42941741545164178212298151945600000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 2) (m3 2) (80 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((1649578043 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_81 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (81 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -6 else if k.val = 2 then -4 else -1) else if j.val = 1 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -1) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 2) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else 5) else if j.val = 2 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then 2 else -2) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -5 else if k.val = 2 then -1 else 2) else if j.val = 2 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then 2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (81 : Fin 88)), (alphaG (n3 2) (m3 2) (81 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -6 else if k.val = 2 then -4 else -1) else if j.val = 1 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -1) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 2) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else 5) else if j.val = 2 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then 2 else -2) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -5 else if k.val = 2 then -1 else 2) else if j.val = 2 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then 2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (58589100838177256386 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (81 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (81 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (81 : Fin 88) = 18490136774775589144871000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (81 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 6071621910859181991976474265479000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (81 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((328370849 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (81 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 734880286750619319825394103562819000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (81 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((39744448389 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (81 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 685113826127666096117119375589273000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (81 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((37052934463 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (81 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 2668459176963387023471943299240785000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (81 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((28863595867 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (81 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 10301085995940629159727769146633331000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (81 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((557112482261 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (81 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 2668460658060322956546184981697627000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (81 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((144318059437 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 2 (81 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 685113855508493431235530526789292000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 2) (m3 2) (81 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((9263234013 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 2 (81 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 734880724042354043268077379761969000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 2) (m3 2) (81 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((39744472039 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 2 (81 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 6070629471257932687004712459425000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 2) (m3 2) (81 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((13132687 : ℚ)/40000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_82 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (82 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 8) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 8) else if j.val = 4 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (82 : Fin 88)), (alphaG (n3 2) (m3 2) (82 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 8) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 8) else if j.val = 4 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5336682594847732430093 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (82 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (82 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (82 : Fin 88) = 10625118709154371058818000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (82 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 3491248914733623489310082885916000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (82 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((164292231 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (82 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 720692929834066233418394663676004000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (82 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((33914582489 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (82 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 4453300248802940249740578954524766000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (82 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((419129458287 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (82 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 135074725913198495886780897606210000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (82 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((2542554669 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (82 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 135075101213641540637475437175606000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (82 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((12712808667 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (82 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 4453300006922112835841321800532996000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (82 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((209564717761 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 2 (82 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 720693181989383439069928631544780000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 2) (m3 2) (82 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((6782918871 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 2 (82 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 3491265564294640734209532053722000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 2) (m3 2) (82 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((328586029 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_83 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (83 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -7) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 3 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 7) else if j.val = 1 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 3 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then -2 else if k.val = 2 then 6 else 7) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (83 : Fin 88)), (alphaG (n3 2) (m3 2) (83 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -7) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 3 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 7) else if j.val = 1 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 3 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then -2 else if k.val = 2 then 6 else 7) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3312147533032252430563291 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (83 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (83 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (83 : Fin 88) = 35377377812585378471616000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (83 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 381590569710026389870088175294336000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (83 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((5393143773 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (83 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 53130237496850671637336014961088000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (83 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((1501813893 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (83 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 5783794405802944399754831669929920000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (83 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((32697699849 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (83 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 11064927692209587029271510307078272000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (83 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((156384225971 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (83 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 405246034575657533792587245356736000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (83 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((11454948321 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (83 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 405245541238123937289484458671616000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (83 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((1431866797 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 2 (83 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 11064928703896460335775578459881024000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 2) (m3 2) (83 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((312768480539 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 2 (83 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 5783794376687362459997065187789952000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 2) (m3 2) (83 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((81744249211 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 2 (83 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 53130108157157388825192322732992000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 2) (m3 2) (83 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((1501810237 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 2 (83 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 381590142811208325402326158304064000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 2) (m3 2) (83 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((10786275479 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_84 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (84 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 0) else if j.val = 1 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 4 else if k.val = 2 then -2 else 1) else if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 6 else if k.val = 2 then -2 else 2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -7 else if k.val = 2 then 8 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else -3) else if j.val = 1 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else -4) else if j.val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (84 : Fin 88)), (alphaG (n3 2) (m3 2) (84 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 0) else if j.val = 1 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 4 else if k.val = 2 then -2 else 1) else if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 6 else if k.val = 2 then -2 else 2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -7 else if k.val = 2 then 8 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else -3) else if j.val = 1 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else -4) else if j.val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (10213956923657842280237 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (84 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (84 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (84 : Fin 88) = 565802419399427803472000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (84 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 82691455016980304476036524166368000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (84 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((73074497547 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (84 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 19267379789417687370187283615824000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (84 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((34053194417 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (84 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 180486544384485668785005831600000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (84 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((12759687 : ℚ)/40000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (84 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 21341203668158255948114839241264000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (84 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((37718473687 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (84 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 318841379860010228502135587712848000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (84 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((563520707809 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (84 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 21341196339885319886725928671920000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (84 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((7543692147 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 2 (84 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 180475969537267093479358939920000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 2) (m3 2) (84 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((63794697 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 2 (84 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 19267386835921018570661148056112000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 2) (m3 2) (84 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((34053206871 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 2 (84 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 82691455375133235955874323764144000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 2) (m3 2) (84 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((146148995727 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_85 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (85 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 5 else if k.val = 2 then -6 else -4) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 3) else if j.val = 2 then (if k.val = 0 then (37 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -4) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 3) else if j.val = 4 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 5 else if k.val = 2 then -6 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (85 : Fin 88)), (alphaG (n3 2) (m3 2) (85 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 5 else if k.val = 2 then -6 else -4) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 3) else if j.val = 2 then (if k.val = 0 then (37 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -4) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 3) else if j.val = 4 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 5 else if k.val = 2 then -6 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2738720878107839439491 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (85 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (85 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (85 : Fin 88) = 38904769580362828608244000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (85 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 471210296168702029692859627344992000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (85 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((1513986271 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (85 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12671938336310519525199033371252000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (85 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((325716833 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (85 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 16692671340843282073963717749493656000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (85 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((214532453487 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (85 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2275831096056858152092507848821168000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (85 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((14624370743 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (85 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 2275831064971947257382607790834212000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (85 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((58497482173 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (85 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 16692671329833232282721037253360604000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (85 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((429064906691 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 2 (85 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 12671955493313904465206449606856000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 2) (m3 2) (85 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((162858637 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 2 (85 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 471210558659182388400864247167260000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 2) (m3 2) (85 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((2422379383 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_86 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (86 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else 7) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-43 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else 4) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (86 : Fin 88)), (alphaG (n3 2) (m3 2) (86 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else 7) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-43 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else 4) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2811571359264073128532 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (86 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (86 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (86 : Fin 88) = 2344679235493339615898000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (86 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 403957904344318628160388418324478000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (86 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((172287065211 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (86 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 15554772799528139814324859771850000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (86 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((265362913 : ℚ)/40000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (86 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 752827179270067100076819563776990000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (86 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((64215792751 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (86 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 752826740205433461594043090717510000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (86 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((64215755299 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (86 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 15554262374581969091757176856740000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (86 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((663385513 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (86 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 403958376499410317160666890552432000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (86 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((21535908323 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_87 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (87 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else 0) else if j.val = 3 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -1) else if j.val = 4 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (87 : Fin 88)), (alphaG (n3 2) (m3 2) (87 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else 0) else if j.val = 3 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -1) else if j.val = 4 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (10251997136968664125862 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (87 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (87 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (87 : Fin 88) = 109671448171802031851000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (87 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 42275672274203396921680734024225000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (87 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((15419025819 : ℚ)/40000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (87 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12530325243935344592385797071165000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (87 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((22850660683 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (87 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 12544546739385167714528104051401000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (87 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((114382977051 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (87 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 42320903914278122622405364853209000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (87 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((385888074059 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    (((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (80 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 3 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 3 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (80 : Fin 88)), (alphaG (n3 2) (m3 2) (80 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 3 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 3 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (888565128145945464454483 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (81 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -6 else if k.val = 2 then -4 else -1) else if j.val = 1 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -1) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 2) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else 5) else if j.val = 2 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then 2 else -2) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -5 else if k.val = 2 then -1 else 2) else if j.val = 2 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then 2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (81 : Fin 88)), (alphaG (n3 2) (m3 2) (81 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -6 else if k.val = 2 then -4 else -1) else if j.val = 1 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -1) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 2) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else 5) else if j.val = 2 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then 2 else -2) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -5 else if k.val = 2 then -1 else 2) else if j.val = 2 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then 2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (58589100838177256386 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (82 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 8) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 8) else if j.val = 4 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (82 : Fin 88)), (alphaG (n3 2) (m3 2) (82 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 8) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 8) else if j.val = 4 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5336682594847732430093 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (83 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -7) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 3 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 7) else if j.val = 1 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 3 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then -2 else if k.val = 2 then 6 else 7) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (83 : Fin 88)), (alphaG (n3 2) (m3 2) (83 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -7) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 3 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 7) else if j.val = 1 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 3 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then -2 else if k.val = 2 then 6 else 7) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3312147533032252430563291 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (84 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 0) else if j.val = 1 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 4 else if k.val = 2 then -2 else 1) else if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 6 else if k.val = 2 then -2 else 2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -7 else if k.val = 2 then 8 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else -3) else if j.val = 1 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else -4) else if j.val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (84 : Fin 88)), (alphaG (n3 2) (m3 2) (84 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 0) else if j.val = 1 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 4 else if k.val = 2 then -2 else 1) else if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 6 else if k.val = 2 then -2 else 2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -7 else if k.val = 2 then 8 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else -3) else if j.val = 1 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else -4) else if j.val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (10213956923657842280237 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (85 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 5 else if k.val = 2 then -6 else -4) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 3) else if j.val = 2 then (if k.val = 0 then (37 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -4) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 3) else if j.val = 4 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 5 else if k.val = 2 then -6 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (85 : Fin 88)), (alphaG (n3 2) (m3 2) (85 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 5 else if k.val = 2 then -6 else -4) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 3) else if j.val = 2 then (if k.val = 0 then (37 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -4) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 3) else if j.val = 4 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 5 else if k.val = 2 then -6 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2738720878107839439491 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (86 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else 7) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-43 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else 4) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (86 : Fin 88)), (alphaG (n3 2) (m3 2) (86 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else 7) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-43 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else 4) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2811571359264073128532 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (87 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else 0) else if j.val = 3 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -1) else if j.val = 4 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (87 : Fin 88)), (alphaG (n3 2) (m3 2) (87 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else 0) else if j.val = 3 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -1) else if j.val = 4 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (10251997136968664125862 : ℚ)/10^30) :=
  ⟨L3C.pn_2_80, L3C.pn_2_81, L3C.pn_2_82, L3C.pn_2_83, L3C.pn_2_84, L3C.pn_2_85, L3C.pn_2_86, L3C.pn_2_87⟩

-- Prove2me | solution 1 for mme_released_recursive_level3_penalty5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T07:39:41.974039+00:00
-- url     : https://prove2.me/submissions/662b76d5-672c-4260-a57d-2ed87fb493f4

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

theorem pn_0_68 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (68 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 4 else if k.val = 2 then -7 else 3) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 4 else if k.val = 2 then -7 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else 2) else if j.val = 1 then (if k.val = 0 then (33 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else -8) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else 0) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else -8) else if j.val = 4 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (68 : Fin 88)), (alphaG (n3 0) (m3 0) (68 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 4 else if k.val = 2 then -7 else 3) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 4 else if k.val = 2 then -7 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else 2) else if j.val = 1 then (if k.val = 0 then (33 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else -8) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else 0) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else -8) else if j.val = 4 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (910220336103666916949 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (68 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (68 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (68 : Fin 88) = 6044901480888335032132000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (68 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 1986431088578738648108396637668000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (68 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((328612649 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (68 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 76867424600311915241795713171384000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (68 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((6358037831 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (68 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 409667134307287819804121657740880000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (68 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((3388534417 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (68 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 2533929747346954582676258360966352000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (68 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((104796155709 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (68 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 2533929769676820653077767969661960000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (68 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((41918462653 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (68 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 409667158710555098150330182457764000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (68 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((67770692377 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 0 (68 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 76867381971666672017257066576520000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 0) (m3 0) (68 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((1271606861 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 0 (68 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 1986433186159552516360652787472000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 0) (m3 0) (68 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((82153249 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_69 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (69 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 3 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 3 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (69 : Fin 88)), (alphaG (n3 0) (m3 0) (69 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 3 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 3 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (889378077960408835219120 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (69 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (69 : Fin 88)))) =
        {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (69 : Fin 88) = 25742696099525811314930000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (69 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 42463185335877784862217727591390000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (69 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((1649523623 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (69 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 285728790694482779105866726663110000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (69 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((11099412027 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (69 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 312170599469297643542002314273410000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (69 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((12126569737 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (69 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 8073792594337595519423528184365400000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (69 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((15681715239 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (69 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 4157192927523897018554610168412260000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (69 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((80745095841 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (69 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 4157193009874781840937680564873330000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (69 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((161490194881 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 0 (69 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 8073793050086287265428491703886120000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 0) (m3 0) (69 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((78408580621 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 0 (69 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 312170446377483939662002424384700000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 0) (m3 0) (69 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((1212656379 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 0 (69 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 285728393227255002427340024143910000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 0) (m3 0) (69 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((11099396587 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 0 (69 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 42463102598852520986260161406370000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 0) (m3 0) (69 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((1649520409 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_70 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (70 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -7) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 3 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 7) else if j.val = 1 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 3 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then -2 else if k.val = 2 then 6 else 7) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (70 : Fin 88)), (alphaG (n3 0) (m3 0) (70 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -7) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 3 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 7) else if j.val = 1 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 3 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then -2 else if k.val = 2 then 6 else 7) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3310209208295391693995655 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (70 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (70 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (70 : Fin 88) = 35305197000849047245590000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (70 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 380821877875890082120437651158190000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (70 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((10786567141 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (70 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 53022412061370040818427201694520000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (70 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((375457557 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (70 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 5772014117009955839618059028679360000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (70 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((5109033697 : ℚ)/31250000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (70 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 11042319822059388843322377007757400000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (70 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((15638377293 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (70 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 404420771692560318946698580720830000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (70 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((11454992637 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (70 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 404418614827465143076704253136550000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (70 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((2290986309 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 0 (70 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 11042323355968387840308610102334040000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 0) (m3 0) (70 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((78191911489 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 0 (70 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 5772013838593172290922472449956620000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 0) (m3 0) (70 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((81744535209 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 0 (70 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 53021891027272702288187951277300000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 0) (m3 0) (70 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((150181547 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 0 (70 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 380820299733584144168025773285190000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 0) (m3 0) (70 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((10786522441 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_71 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (71 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else 4) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -3) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 3) else if j.val = 2 then (if k.val = 0 then (37 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -4) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 3) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (71 : Fin 88)), (alphaG (n3 0) (m3 0) (71 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else 4) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -3) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 3) else if j.val = 2 then (if k.val = 0 then (37 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -4) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 3) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (30241233241425648426187 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (71 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (71 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (71 : Fin 88) = 38455102061686906176449000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (71 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 465567723186736883280478409366670000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (71 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((1210678683 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (71 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12522861954961787572572165991243000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (71 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((325648907 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (71 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 16499636379936796231741210123430284000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (71 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((107265586979 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (71 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2249823848032170312358976530157565000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (71 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((11701042137 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (71 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 2249824427550558381980652609243995000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (71 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((11701045151 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (71 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 16499636793406053598998825332609932000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (71 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((107265589667 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 0 (71 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 12522753396208667430436029875716000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 0) (m3 0) (71 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((81411521 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 0 (71 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 465567274223420313085848799324595000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 0) (m3 0) (71 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((2421355031 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_72 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (72 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -8 else if k.val = 2 then -8 else 7) else if j.val = 1 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -1) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 2) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 2) else if j.val = 2 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then 2 else -2) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -5 else if k.val = 2 then -1 else 2) else if j.val = 2 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then 2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (72 : Fin 88)), (alphaG (n3 0) (m3 0) (72 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -8 else if k.val = 2 then -8 else 7) else if j.val = 1 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -1) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 2) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 2) else if j.val = 2 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then 2 else -2) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -5 else if k.val = 2 then -1 else 2) else if j.val = 2 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then 2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (22111111780314515972832 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (72 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (72 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (72 : Fin 88) = 18193280658643192595892000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (72 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 5979744654315617945211074715540000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (72 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((65735749 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (72 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 723017220956545797698468611734168000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (72 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((19870446527 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (72 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 674227612017034873618018710527484000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (72 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((37059155227 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (72 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 2625572461261509503802818515814016000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (72 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((4509859489 : ℚ)/31250000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (72 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 10135686437192043648457674244658460000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (72 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((111422306151 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (72 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 2625572428459024476269142265420740000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (72 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((28863100369 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 0 (72 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 674228391253438763964600785177736000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 0) (m3 0) (72 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((18529599029 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 0 (72 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 723018038307872667902539174778160000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 0) (m3 0) (72 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((1987046899 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 0 (72 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 5978324541407246233526617173696000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 0) (m3 0) (72 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((20537543 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_73 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (73 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -3 else 0) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else -6) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else 2) else if j.val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (73 : Fin 88)), (alphaG (n3 0) (m3 0) (73 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -3 else 0) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else -6) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else 2) else if j.val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5713383872870351750154 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (73 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (73 : Fin 88)))) =
        {(⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (73 : Fin 88) = 405929511182391566920000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (73 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 2904651497482500652596729445800000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (73 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((1431111273 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (73 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 71366577962966455201705872424720000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (73 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((87905136233 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (73 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 128693496821012402192296700237800000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (73 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((63406819793 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (73 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 128693526992129250334732303133720000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (73 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((317034173291 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (73 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 71366603657898583535909666893800000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (73 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((35162067153 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (73 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 2904654250902375002758727864160000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (73 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((1788890787 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_74 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (74 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else 1) else if j.val = 3 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 2 else if k.val = 2 then 7 else -1) else if j.val = 4 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (74 : Fin 88)), (alphaG (n3 0) (m3 0) (74 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else 1) else if j.val = 3 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 2 else if k.val = 2 then 7 else -1) else if j.val = 4 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3596602208606126542638 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (74 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (74 : Fin 88)))) =
        {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (74 : Fin 88) = 110242411831095174528000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (74 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 12877257196670847215723749326720000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (74 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((23361711673 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (74 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 42243948915549202754950042031232000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (74 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((383191443419 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (74 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 42243948913454596930159233715200000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (74 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((1915957217 : ℚ)/5000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (74 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 12877256805420527627166974926848000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (74 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((1825133669 : ℚ)/15625000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_75 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (75 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then -2 else if k.val = 2 then 7 else 6) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 3) else if j.val = 4 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (75 : Fin 88)), (alphaG (n3 0) (m3 0) (75 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then -2 else if k.val = 2 then 7 else 6) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 3) else if j.val = 4 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (9925877097143598011823 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (75 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (75 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (75 : Fin 88) = 111445382014040884224000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (75 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 13247994849818344668882998055936000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (75 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((118874327589 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (75 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 42468942019490923629474509724672000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (75 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((381074040503 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (75 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 42477628152471436880058242273280000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (75 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((19057599061 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (75 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 13250816992260179045584249946112000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (75 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((928903521 : ℚ)/7812500000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_76 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (76 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else 7) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else -4) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 5) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (76 : Fin 88)), (alphaG (n3 0) (m3 0) (76 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else 7) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else -4) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 5) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (10777099443266738441623 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (76 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (76 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (76 : Fin 88) = 3199352595399596276383000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (76 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 23574220614291041065499765886057000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (76 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((7368434679 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (76 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1009003130636570784839967981741352000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (76 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((39422160443 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (76 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 567098933587538878779655221312931000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (76 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((177254277757 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (76 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 567098956821237426571523380406277000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (76 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((177254285019 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (76 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1009003073912049268405126001470762000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (76 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((157688632907 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (76 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 23574279827908876721227649182621000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (76 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((7368453187 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_77 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (77 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then -6 else 2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -8) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -8) else if j.val = 3 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -1) else if j.val = 1 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else 4) else if j.val = 2 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 8) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else 4) else if j.val = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (77 : Fin 88)), (alphaG (n3 0) (m3 0) (77 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then -6 else 2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -8) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -8) else if j.val = 3 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -1) else if j.val = 1 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else 4) else if j.val = 2 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 8) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else 4) else if j.val = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1814991905636108977750 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (77 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (77 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (77 : Fin 88) = 10757103157606973235969000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (77 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 3549084569013167800345364116662000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (77 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((164964699 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (77 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 729257282511145594362607873112340000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (77 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((3389654593 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (77 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 4508413832548142428723076975071026000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (77 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((209555201177 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (77 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 137331594769046911857427382990670000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (77 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((1276659643 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (77 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 137331164657034258100209516006174000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (77 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((6383278223 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (77 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 4508414156197105131644080725670329000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (77 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((419110432441 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 0 (77 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 729256947491924853851033412093804000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 0) (m3 0) (77 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((16948265179 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 0 (77 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 3549094863560889630218750938995000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 0) (m3 0) (77 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((65986071 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_78 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (78 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -8) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 0) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -1) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (78 : Fin 88)), (alphaG (n3 0) (m3 0) (78 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -8) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 0) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -1) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1020111482700393550132 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (78 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (78 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (78 : Fin 88) = 547314933383461180152000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (78 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 96245328674912340846861130004424000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (78 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((175849995687 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (78 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 173493541828241202482634307513608000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (78 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((316990330879 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (78 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 3918565600240049811626126146992000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (78 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((3579808773 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (78 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 3918507049035791382332534666184000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (78 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((7159510567 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (78 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 173493730573079869369523050011720000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (78 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((63398135147 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (78 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 96245259657951926259022851657072000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (78 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((87924934793 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_79 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (79 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then -8 else if k.val = 2 then 6 else 7) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 6) else if j.val = 4 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (79 : Fin 88)), (alphaG (n3 0) (m3 0) (79 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then -8 else if k.val = 2 then 6 else 7) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 6) else if j.val = 4 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (7327823244303144477635 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (79 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (79 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (79 : Fin 88) = 110281620997937638620000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (79 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 42230357244875889090198562648500000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (79 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((15317278387 : ℚ)/40000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (79 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12929032066834773569987456505300000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (79 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((23447301463 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (79 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 12888104106273412233131556175800000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (79 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((11686538509 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (79 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 42234127579953563726682424670400000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (79 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((4787076849 : ℚ)/12500000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_80 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (80 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -4 else if k.val = 2 then -4 else 6) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -3) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -4 else if k.val = 2 then -4 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 4 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (80 : Fin 88)), (alphaG (n3 0) (m3 0) (80 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -4 else if k.val = 2 then -4 else 6) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -3) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -4 else if k.val = 2 then -4 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 4 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (4073411303118769723911 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (80 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (80 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (80 : Fin 88) = 2844274767837393260500000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (80 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 20902495512528238143070082319500000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (80 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((7348971959 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (80 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 503235791124504480954684133718500000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (80 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((176929386997 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (80 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 897998885937827286994739562509500000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (80 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((315721566739 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (80 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 897999297123253374175333659952500000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (80 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((63144342261 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (80 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 503236250821881008369857682249500000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (80 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((176929548619 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (80 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 20902047317398871862314879250500000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (80 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((7348814381 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_81 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (81 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -3 else 0) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 5 else if k.val = 2 then -5 else -1) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -8) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else -5) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else -5) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else -4) else if j.val = 1 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else 0) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (81 : Fin 88)), (alphaG (n3 0) (m3 0) (81 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -3 else 0) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 5 else if k.val = 2 then -5 else -1) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -8) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else -5) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else -5) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else -4) else if j.val = 1 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else 0) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5181237194651955600965 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (81 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (81 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (81 : Fin 88) = 7042066099602865294704000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (81 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 1016563509632860745388219844400736000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (81 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((72177930117 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (81 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 252850385673105061799723539459920000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (81 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((7181142071 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (81 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 2315608413343562722549375826784000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (81 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((164412573 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (81 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 283666435777908841785875044984128000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (81 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((10070426483 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (81 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 3931273679510153910026300876190912000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (81 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((139563929957 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (81 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 283666269261213850576522286413344000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (81 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((20140841143 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 0 (81 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 2315467515685041868420559389152000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 0) (m3 0) (81 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((164402569 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 0 (81 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 252850634870698128446317723150368000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 0) (m3 0) (81 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((17952872871 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 0 (81 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 1016564108947896152090070750184656000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 0) (m3 0) (81 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((144355945339 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_82 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (82 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 5) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else 6) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 0) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 6 else if k.val = 2 then -4 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (82 : Fin 88)), (alphaG (n3 0) (m3 0) (82 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 5) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else 6) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 0) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 6 else if k.val = 2 then -4 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (4586301037440826690315 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (82 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (82 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (82 : Fin 88) = 2072668777206426302096000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (82 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 363048682960769274132575665069808000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (82 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((175160009623 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (82 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 14585460887259981218270958023056000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (82 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((7037043761 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (82 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 658700570802563900485662107024704000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (82 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((79450775981 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (82 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 658699961230676524075686660591104000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (82 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((9931337807 : ℚ)/31250000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (82 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 14585116695737500764706379357104000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (82 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((7036877699 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (82 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 363048984629419121419098229934224000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (82 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((175160155169 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_83 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (83 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else -6) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else -4) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else -4) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 3 else if k.val = 2 then 1 else 6) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (83 : Fin 88)), (alphaG (n3 0) (m3 0) (83 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else -6) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else -4) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else -4) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 3 else if k.val = 2 then 1 else 6) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (7271512809905978373412 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (83 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (83 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (83 : Fin 88) = 5943998956570462546744000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (83 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 1946070542596241828945189655416000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (83 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((327400889 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (83 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 75295231424766225842740255663144000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (83 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((12667436851 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (83 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 402987699014602036968981455567616000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (83 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((2118668877 : ℚ)/31250000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (83 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 2491770439202233457114668174484784000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (83 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((209603875893 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (83 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 2491770559378004361056279944554976000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (83 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((104801943001 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (83 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 402987823291732220944212382891168000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (83 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((16949356243 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 0 (83 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 75295056231340979884927152930488000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 0) (m3 0) (83 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((12667407377 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 0 (83 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 1946077485187023103245444252408000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 0) (m3 0) (83 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((327402057 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    (((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (68 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 4 else if k.val = 2 then -7 else 3) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 4 else if k.val = 2 then -7 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else 2) else if j.val = 1 then (if k.val = 0 then (33 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else -8) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else 0) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else -8) else if j.val = 4 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (68 : Fin 88)), (alphaG (n3 0) (m3 0) (68 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 4 else if k.val = 2 then -7 else 3) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 4 else if k.val = 2 then -7 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else 2) else if j.val = 1 then (if k.val = 0 then (33 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else -8) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else 0) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else -8) else if j.val = 4 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (910220336103666916949 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (69 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 3 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 3 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (69 : Fin 88)), (alphaG (n3 0) (m3 0) (69 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 3 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 3 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (889378077960408835219120 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (70 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -7) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 3 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 7) else if j.val = 1 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 3 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then -2 else if k.val = 2 then 6 else 7) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (70 : Fin 88)), (alphaG (n3 0) (m3 0) (70 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -7) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 3 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 7) else if j.val = 1 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 3 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then -2 else if k.val = 2 then 6 else 7) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3310209208295391693995655 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (71 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else 4) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -3) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 3) else if j.val = 2 then (if k.val = 0 then (37 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -4) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 3) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (71 : Fin 88)), (alphaG (n3 0) (m3 0) (71 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else 4) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -3) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 3) else if j.val = 2 then (if k.val = 0 then (37 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -4) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 3) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (30241233241425648426187 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (72 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -8 else if k.val = 2 then -8 else 7) else if j.val = 1 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -1) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 2) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 2) else if j.val = 2 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then 2 else -2) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -5 else if k.val = 2 then -1 else 2) else if j.val = 2 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then 2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (72 : Fin 88)), (alphaG (n3 0) (m3 0) (72 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -8 else if k.val = 2 then -8 else 7) else if j.val = 1 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -1) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 2) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 2) else if j.val = 2 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then 2 else -2) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -5 else if k.val = 2 then -1 else 2) else if j.val = 2 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then 2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (22111111780314515972832 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (73 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -3 else 0) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else -6) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else 2) else if j.val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (73 : Fin 88)), (alphaG (n3 0) (m3 0) (73 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -3 else 0) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else -6) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else 2) else if j.val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5713383872870351750154 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (74 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else 1) else if j.val = 3 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 2 else if k.val = 2 then 7 else -1) else if j.val = 4 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (74 : Fin 88)), (alphaG (n3 0) (m3 0) (74 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else 1) else if j.val = 3 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 2 else if k.val = 2 then 7 else -1) else if j.val = 4 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3596602208606126542638 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (75 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then -2 else if k.val = 2 then 7 else 6) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 3) else if j.val = 4 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (75 : Fin 88)), (alphaG (n3 0) (m3 0) (75 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then -2 else if k.val = 2 then 7 else 6) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 3) else if j.val = 4 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (9925877097143598011823 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (76 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else 7) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else -4) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 5) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (76 : Fin 88)), (alphaG (n3 0) (m3 0) (76 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else 7) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else -4) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 5) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (10777099443266738441623 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (77 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then -6 else 2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -8) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -8) else if j.val = 3 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -1) else if j.val = 1 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else 4) else if j.val = 2 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 8) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else 4) else if j.val = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (77 : Fin 88)), (alphaG (n3 0) (m3 0) (77 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then -6 else 2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -8) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -8) else if j.val = 3 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -1) else if j.val = 1 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else 4) else if j.val = 2 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 8) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else 4) else if j.val = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1814991905636108977750 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (78 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -8) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 0) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -1) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (78 : Fin 88)), (alphaG (n3 0) (m3 0) (78 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -8) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 0) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -1) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1020111482700393550132 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (79 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then -8 else if k.val = 2 then 6 else 7) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 6) else if j.val = 4 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (79 : Fin 88)), (alphaG (n3 0) (m3 0) (79 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then -8 else if k.val = 2 then 6 else 7) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 6) else if j.val = 4 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (7327823244303144477635 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (80 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -4 else if k.val = 2 then -4 else 6) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -3) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -4 else if k.val = 2 then -4 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 4 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (80 : Fin 88)), (alphaG (n3 0) (m3 0) (80 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -4 else if k.val = 2 then -4 else 6) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -3) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -4 else if k.val = 2 then -4 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 4 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (4073411303118769723911 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (81 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -3 else 0) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 5 else if k.val = 2 then -5 else -1) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -8) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else -5) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else -5) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else -4) else if j.val = 1 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else 0) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (81 : Fin 88)), (alphaG (n3 0) (m3 0) (81 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -3 else 0) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 5 else if k.val = 2 then -5 else -1) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -8) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else -5) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else -5) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else -4) else if j.val = 1 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else 0) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5181237194651955600965 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (82 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 5) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else 6) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 0) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 6 else if k.val = 2 then -4 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (82 : Fin 88)), (alphaG (n3 0) (m3 0) (82 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 5) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else 6) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 0) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 6 else if k.val = 2 then -4 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (4586301037440826690315 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (83 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else -6) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else -4) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else -4) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 3 else if k.val = 2 then 1 else 6) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (83 : Fin 88)), (alphaG (n3 0) (m3 0) (83 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else -6) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else -4) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else -4) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 3 else if k.val = 2 then 1 else 6) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then -3 else if k.val = 2 then 7 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (7271512809905978373412 : ℚ)/10^30) :=
  ⟨L3C.pn_0_68, L3C.pn_0_69, L3C.pn_0_70, L3C.pn_0_71, L3C.pn_0_72, L3C.pn_0_73, L3C.pn_0_74, L3C.pn_0_75, L3C.pn_0_76, L3C.pn_0_77, L3C.pn_0_78, L3C.pn_0_79, L3C.pn_0_80, L3C.pn_0_81, L3C.pn_0_82, L3C.pn_0_83⟩

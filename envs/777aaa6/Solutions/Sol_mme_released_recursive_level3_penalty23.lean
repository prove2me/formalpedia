-- Prove2me | solution 1 for mme_released_recursive_level3_penalty23
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T10:00:50.269229+00:00
-- url     : https://prove2.me/submissions/ace0cdad-e3c1-4412-9450-b6cc7ae1054a

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

theorem pn_3_64 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (64 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -7) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 3 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else 1) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 3 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else 4) else if j.val = 1 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else -8) else if j.val = 2 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (64 : Fin 88)), (alphaG (n3 3) (m3 3) (64 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -7) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 3 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else 1) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 3 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else 4) else if j.val = 1 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else -8) else if j.val = 2 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3154291984401883407651176 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (64 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (64 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (64 : Fin 88) = 28465976738591180503536000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (64 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 305358020524861279793142492280224000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (64 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((5363561267 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (64 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 43220637835337912629989013386624000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (64 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((189790773 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (64 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 4650626328577127978766475595412192000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (64 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((81687453961 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (64 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 8902369859296566712349609158051488000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (64 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((156368599979 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (64 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 331409879701333595943591093296832000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (64 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((2910578853 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (64 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 331428369577262310674748901580880000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (64 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((2328592991 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 3 (64 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 8902333905800102662576533054963264000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 3) (m3 3) (64 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((78183984231 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 3 (64 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 4650626228234559975232564320447792000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 3) (m3 3) (64 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((163374904397 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 3 (64 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 43225996356197115249580540513872000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 3) (m3 3) (64 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((1518514427 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 3 (64 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 305377512687830960319765830066832000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 3) (m3 3) (64 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((10727807287 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_65 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (65 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 3 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -5) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 3 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (65 : Fin 88)), (alphaG (n3 3) (m3 3) (65 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 3 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -5) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 3 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (815912007597478184198526 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (65 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (65 : Fin 88)))) =
        {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (65 : Fin 88) = 26245634207757154372116000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (65 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 42700654744802202735240311643084000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (65 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((1626962199 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (65 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 289843019457644680983981412786872000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (65 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((5521737771 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (65 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 315669067755815989828980301460328000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (65 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((6013744329 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (65 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 8235414342699432793137478360932300000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (65 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((12551290287 : ℚ)/40000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (65 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 4239190104151753815674471161344792000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (65 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((80759909831 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (65 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 4239189922873158342695805913139580000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (65 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((32303962551 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 3 (65 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 8235414382776516228382653087153432000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 3) (m3 3) (65 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((156891129351 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 3 (65 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 315668836400550448449664511257788000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 3) (m3 3) (65 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((12027479843 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 3 (65 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 289843223464959377880342347244540000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 3) (m3 3) (65 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((2208696663 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 3 (65 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 42700653432520492347382593037284000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 3) (m3 3) (65 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((1626962149 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_66 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (66 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else if j.val = 1 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 5 else if k.val = 2 then 5 else -7) else if j.val = 1 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 1) else if j.val = 2 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else 5) else if j.val = 3 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 1) else if j.val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 5 else if k.val = 2 then 5 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (66 : Fin 88)), (alphaG (n3 3) (m3 3) (66 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else if j.val = 1 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 5 else if k.val = 2 then 5 else -7) else if j.val = 1 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 1) else if j.val = 2 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else 5) else if j.val = 3 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 1) else if j.val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 5 else if k.val = 2 then 5 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2861964018196537977670 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (66 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (66 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (66 : Fin 88) = 9440709720546157638416000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (66 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 3121334358693572032270403209104000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (66 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((330624969 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (66 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 614941665070416080381161349977168000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (66 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((65137228373 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (66 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 3983151544804098593300321633818496000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (66 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((52739037407 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (66 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 119140473982944198231463903694912000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (66 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((3154966033 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (66 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 119140150459262784835187792817008000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (66 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((12619829863 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (66 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 3983151804706837199936041419410976000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (66 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((210956163393 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 3 (66 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 614941427570481640601473640345856000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 3) (m3 3) (66 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((4071075201 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 3 (66 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 3121319593423569098079856726480000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 3) (m3 3) (66 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((66124681 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_67 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (67 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -4) else if j.val = 1 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else -6) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else 2) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else -3) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -6) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 4) else if j.val = 3 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (67 : Fin 88)), (alphaG (n3 3) (m3 3) (67 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -4) else if j.val = 1 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else -6) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else 2) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else -3) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -6) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 4) else if j.val = 3 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (7345903525161811424629 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (67 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (67 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (67 : Fin 88) = 10265725703067822871576000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (67 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 3425508990383122778877046792256000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (67 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((41710507 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (67 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 396326226751091482728048449736376000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (67 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((38606742301 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (67 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 1483367406057141621644094440365392000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (67 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((72248540871 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (67 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 399720446558929631106764002505680000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (67 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((3893737843 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (67 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 5700046516559228834333729101717088000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (67 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((138812556497 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (67 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 399720499345291196281509208149472000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (67 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((9734345893 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 3 (67 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 1483367403542038824392477836829272000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 3) (m3 3) (67 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((144497081497 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 3 (67 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 396326289392549722847903612093128000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 3) (m3 3) (67 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((38606748403 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 3 (67 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 3425405871168435462596301811336000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 3) (m3 3) (67 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((333674011 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_68 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (68 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 3 else if k.val = 2 then -5 else -2) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 3 else if k.val = 2 then -5 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 5 else if k.val = 2 then 8 else -2) else if j.val = 1 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else 5) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 0) else if j.val = 3 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else 5) else if j.val = 4 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 5 else if k.val = 2 then 8 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (68 : Fin 88)), (alphaG (n3 3) (m3 3) (68 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 3 else if k.val = 2 then -5 else -2) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 3 else if k.val = 2 then -5 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 5 else if k.val = 2 then 8 else -2) else if j.val = 1 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else 5) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 0) else if j.val = 3 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else 5) else if j.val = 4 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 5 else if k.val = 2 then 8 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1099240409488892035253 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (68 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (68 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (68 : Fin 88) = 4405099677236671631054000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (68 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 1434842048698277500138205596138000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (68 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((325722947 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (68 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 54711593240375159459391669792976000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (68 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((1552507243 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (68 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 287400982744149011504611849955182000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (68 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((65242787633 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (68 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1859002522955224766365870308719610000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (68 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((84402290943 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (68 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 1859002231742895303603982123001778000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (68 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((422011388607 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (68 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 287400704337444310469728095711328000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (68 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((4077670277 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 3 (68 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 54711967211312258466629788122306000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 3) (m3 3) (68 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((12420142839 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 3 (68 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 1434832956572543683647959100682000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 3) (m3 3) (68 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((325720883 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_69 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (69 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else -5) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -3) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else -6) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 4 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (69 : Fin 88)), (alphaG (n3 3) (m3 3) (69 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else -5) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -3) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else -6) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 4 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (7466932539415614870675 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (69 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (69 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (69 : Fin 88) = 3541674470741661408560000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (69 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 25039046503089063806848113561760000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (69 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((3534916423 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (69 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1123681854503766389318024050380560000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (69 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((317274177451 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (69 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 622116342775452119166573681387680000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (69 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((87827996039 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (69 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 622116325364580421000566196906720000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (69 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((87827993581 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (69 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1123681877903609617508180976736480000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (69 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((158637092029 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (69 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 25039023691163797759806981026800000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (69 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((1413965281 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_70 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (70 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else -6) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -2) else if j.val = 2 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 7) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 5) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 5) else if j.val = 4 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (70 : Fin 88)), (alphaG (n3 3) (m3 3) (70 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else -6) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -2) else if j.val = 2 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 7) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 5) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 5) else if j.val = 4 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (731471838170391279621 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (70 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (70 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (70 : Fin 88) = 3192498072093166091606000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (70 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 22576851480754225077695941695910000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (70 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((1414368997 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (70 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 559763548430056587354823475741546000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (70 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((175337160991 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (70 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 1013908668204415367546333972744814000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (70 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((317591004069 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (70 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1013908463131109208569716912341798000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (70 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((317590939833 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (70 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 559763486671181382712525433623476000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (70 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((87668570823 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (70 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 22577054175649320344904263852456000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (70 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((1767977119 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_71 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (71 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else 0) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 2) else if j.val = 4 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (71 : Fin 88)), (alphaG (n3 3) (m3 3) (71 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else 0) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 2) else if j.val = 4 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (22152224704204103402 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (71 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (71 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (71 : Fin 88) = 110583226808213055048000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (71 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 12958861205186508563319671640216000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (71 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((117186499067 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (71 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 42332751750836783933801029305288000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (71 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((382813496881 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (71 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 42332751748956869078061407369472000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (71 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((11962921777 : ℚ)/31250000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (71 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 12958862103232893472817891685024000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (71 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((29296626797 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_72 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (72 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 7 else if k.val = 2 then 1 else -1) else if j.val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (72 : Fin 88)), (alphaG (n3 3) (m3 3) (72 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 7 else if k.val = 2 then 1 else -1) else if j.val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5005721307087226075541 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (72 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (72 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (72 : Fin 88) = 110932762861723711524000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (72 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 42309589138112386440675773432292000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (72 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((381398498033 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (72 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 13156070903648545303731608687148000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (72 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((118594999027 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (72 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 13155378622860865150993999858092000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (72 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((118588758483 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (72 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 42311724197101914628598618022468000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (72 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((381417744457 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_73 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (73 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 3 else 0) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else -5) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else -5) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 4 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (73 : Fin 88)), (alphaG (n3 3) (m3 3) (73 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 3 else 0) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else -5) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else -5) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 4 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3986350149452664854787 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (73 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (73 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (73 : Fin 88) = 1774967245722334950955000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (73 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 312509301153492460673563321891345000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (73 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((176064827059 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (73 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12878049006281022772477177936755000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (73 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((7255372761 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (73 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 562096382323371087842866071152700000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (73 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((15833993097 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (73 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 562096257715345536397785509258835000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (73 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((316679791737 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (73 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 12877897647724111046086570200085000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (73 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((7255287487 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (73 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 312509357876120732222221349560280000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (73 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((22008107377 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_74 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (74 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 3) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 3 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -6) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 0) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -6) else if j.val = 4 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (74 : Fin 88)), (alphaG (n3 3) (m3 3) (74 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 3) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 3 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -6) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 0) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -6) else if j.val = 4 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2904261856934095003327 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (74 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (74 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (74 : Fin 88) = 29768213275869573517905000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (74 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 370723259873049077433094497135090000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (74 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((6226830889 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (74 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 9717936043316277128427018093870000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (74 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((163226727 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (74 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 12560096964348469127565580390324380000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (74 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((105482455799 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (74 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 1943568506902337713729319289029370000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (74 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((32645031277 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (74 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 1943568048739767184820713274953515000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (74 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((65290047163 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (74 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 12560096766389850843032916496256130000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (74 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((210964908273 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 3 (74 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 9718139538822230972831586492450000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 3) (m3 3) (74 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((32646029 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 3 (74 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 370723654033961063222117447715195000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 3) (m3 3) (74 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((12453675019 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_75 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (75 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else if j.val = 3 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 7) else if j.val = 4 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -2 else if k.val = 2 then -8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (75 : Fin 88)), (alphaG (n3 3) (m3 3) (75 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else if j.val = 3 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 7) else if j.val = 4 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -2 else if k.val = 2 then -8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1916303543796241469153 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (75 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (75 : Fin 88)))) =
        {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (75 : Fin 88) = 110272572456467996736000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (75 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 12874603783224020889483108085248000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (75 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((14594068471 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (75 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 42243130894046545603792950359040000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (75 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((4788490233 : ℚ)/12500000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (75 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 42238986603432251516617894800192000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (75 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((383041636397 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (75 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 12915851175765178726106046755520000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (75 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((23425319439 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_76 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (76 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else 4) else if j.val = 2 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (76 : Fin 88)), (alphaG (n3 3) (m3 3) (76 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else 4) else if j.val = 2 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (57690091683700445453 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (76 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (76 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (76 : Fin 88) = 1027861981115300421850000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (76 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 181987348236394306528596256437350000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (76 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((177054265631 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (76 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 324412762442015806052775594605100000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (76 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((157809496023 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (76 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 7530975027395828205872899190200000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (76 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((1831708723 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (76 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 7530817743955477942602347703200000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (76 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((457917617 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (76 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 324412896101076382361981250291700000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (76 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((157809561041 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (76 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 181987181564462620758171651772450000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (76 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((177054103477 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_77 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (77 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else -6) else if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else 5) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 4 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else 5) else if j.val = 1 then (if k.val = 0 then (20 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -7) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (77 : Fin 88)), (alphaG (n3 3) (m3 3) (77 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else -6) else if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else 5) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 4 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else 5) else if j.val = 1 then (if k.val = 0 then (20 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -7) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (31509558247647258047203 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (77 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (77 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (77 : Fin 88) = 7714585614082885038960000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (77 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 1103779662692696011904360983754160000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (77 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((143076986621 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (77 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 286891714601072500092946159458720000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (77 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((18594110491 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (77 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 2590202199097637960999586905040000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (77 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((335753899 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (77 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 324011348389274888118306510401760000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (77 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((20999919153 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (77 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 4280040475805923414971413682396480000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (77 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((138699623347 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (77 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 324011176199723981788312440814560000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (77 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((20999907993 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 3 (77 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 2590217311970855949371378227680000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 3) (m3 3) (77 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((167877929 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 3 (77 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 286891781586819387174636952748400000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 3) (m3 3) (77 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((7437645933 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 3 (77 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 1103779035296306360999652305293200000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 3) (m3 3) (77 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((28615381059 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_78 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (78 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then -3 else 0) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 3 then (if k.val = 0 then (-46 : Int) else if k.val = 1 then -1 else if k.val = 2 then 8 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 5 else if k.val = 2 then -2 else 8) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (78 : Fin 88)), (alphaG (n3 3) (m3 3) (78 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then -3 else 0) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 3 then (if k.val = 0 then (-46 : Int) else if k.val = 1 then -1 else if k.val = 2 then 8 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 5 else if k.val = 2 then -2 else 8) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3207800003276561017080487 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (78 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (78 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (78 : Fin 88) = 30439146382988008212512000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (78 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 328343775808568977199945619288032000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (78 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((10786891711 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (78 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 46433950390297862403310045943616000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (78 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((762734109 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (78 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 4973668440692414777185729190251968000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (78 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((81698553207 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (78 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 9516945408061452653115998370834848000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (78 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((312654806029 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (78 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 354179508447747936133520007950464000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (78 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((2908914593 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (78 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 354198011765612080500964221532512000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (78 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((11636266251 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 3 (78 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 9516909950078174891662003771643776000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 3) (m3 3) (78 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((78163410287 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 3 (78 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 4973665431904551404353069416290816000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 3) (m3 3) (78 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((10212312973 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 3 (78 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 46439235234892876781295902277056000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 3) (m3 3) (78 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((762820919 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 3 (78 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 328362670604294753176163453986912000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 3) (m3 3) (78 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((10787512451 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_79 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (79 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then 1 else if k.val = 2 then 3 else 6) else if j.val = 1 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -1) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 3 else if k.val = 2 then 7 else -3) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else 1) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 3 else if k.val = 2 then 7 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else if j.val = 1 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (79 : Fin 88)), (alphaG (n3 3) (m3 3) (79 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then 1 else if k.val = 2 then 3 else 6) else if j.val = 1 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -1) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 3 else if k.val = 2 then 7 else -3) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else 1) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 3 else if k.val = 2 then 7 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else if j.val = 1 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (33586634404144084118240 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (79 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (79 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (79 : Fin 88) = 18476076594180186568587000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (79 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 6066399237724912719268845364155000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (79 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((65667613 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (79 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 735691780835885008732899085828044000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (79 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((9954653753 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (79 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 683265056856607440180183220791789000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (79 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((36981068647 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (79 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 2666403558849044976053239507754394000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (79 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((72158273031 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (79 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 10293225072367190203062858653344737000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (79 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((557110976451 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (79 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 2666402093640742827781904059099533000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (79 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((144316466759 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 3 (79 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 683265286939189267506046559405700000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 3) (m3 3) (79 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((369810811 : ℚ)/10000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 3 (79 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 735691654829042636424026688064704000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 3) (m3 3) (79 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((622165753 : ℚ)/15625000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 3 (79 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 6065690624759296126573380346944000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 3) (m3 3) (79 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((5129683 : ℚ)/15625000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    (((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (64 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -7) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 3 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else 1) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 3 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else 4) else if j.val = 1 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else -8) else if j.val = 2 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (64 : Fin 88)), (alphaG (n3 3) (m3 3) (64 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -7) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 3 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else 1) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 3 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else 4) else if j.val = 1 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else -8) else if j.val = 2 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3154291984401883407651176 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (65 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 3 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -5) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 3 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (65 : Fin 88)), (alphaG (n3 3) (m3 3) (65 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 3 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -5) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 3 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (815912007597478184198526 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (66 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else if j.val = 1 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 5 else if k.val = 2 then 5 else -7) else if j.val = 1 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 1) else if j.val = 2 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else 5) else if j.val = 3 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 1) else if j.val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 5 else if k.val = 2 then 5 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (66 : Fin 88)), (alphaG (n3 3) (m3 3) (66 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else if j.val = 1 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 5 else if k.val = 2 then 5 else -7) else if j.val = 1 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 1) else if j.val = 2 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else 5) else if j.val = 3 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 1) else if j.val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 5 else if k.val = 2 then 5 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2861964018196537977670 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (67 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -4) else if j.val = 1 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else -6) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else 2) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else -3) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -6) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 4) else if j.val = 3 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (67 : Fin 88)), (alphaG (n3 3) (m3 3) (67 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -4) else if j.val = 1 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else -6) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else 2) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else -3) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -6) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 4) else if j.val = 3 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (7345903525161811424629 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (68 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 3 else if k.val = 2 then -5 else -2) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 3 else if k.val = 2 then -5 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 5 else if k.val = 2 then 8 else -2) else if j.val = 1 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else 5) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 0) else if j.val = 3 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else 5) else if j.val = 4 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 5 else if k.val = 2 then 8 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (68 : Fin 88)), (alphaG (n3 3) (m3 3) (68 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 3 else if k.val = 2 then -5 else -2) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 3 else if k.val = 2 then -5 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 5 else if k.val = 2 then 8 else -2) else if j.val = 1 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else 5) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 0) else if j.val = 3 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else 5) else if j.val = 4 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 5 else if k.val = 2 then 8 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1099240409488892035253 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (69 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else -5) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -3) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else -6) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 4 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (69 : Fin 88)), (alphaG (n3 3) (m3 3) (69 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else -5) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -3) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else -6) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 4 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (7466932539415614870675 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (70 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else -6) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -2) else if j.val = 2 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 7) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 5) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 5) else if j.val = 4 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (70 : Fin 88)), (alphaG (n3 3) (m3 3) (70 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else -6) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -2) else if j.val = 2 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 7) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 5) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 5) else if j.val = 4 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (731471838170391279621 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (71 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else 0) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 2) else if j.val = 4 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (71 : Fin 88)), (alphaG (n3 3) (m3 3) (71 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else 0) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 2) else if j.val = 4 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (22152224704204103402 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (72 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 7 else if k.val = 2 then 1 else -1) else if j.val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (72 : Fin 88)), (alphaG (n3 3) (m3 3) (72 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 7 else if k.val = 2 then 1 else -1) else if j.val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5005721307087226075541 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (73 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 3 else 0) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else -5) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else -5) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 4 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (73 : Fin 88)), (alphaG (n3 3) (m3 3) (73 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 3 else 0) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else -5) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else -5) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 4 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3986350149452664854787 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (74 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 3) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 3 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -6) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 0) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -6) else if j.val = 4 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (74 : Fin 88)), (alphaG (n3 3) (m3 3) (74 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 3) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 3 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -6) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 0) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -6) else if j.val = 4 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2904261856934095003327 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (75 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else if j.val = 3 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 7) else if j.val = 4 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -2 else if k.val = 2 then -8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (75 : Fin 88)), (alphaG (n3 3) (m3 3) (75 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else if j.val = 3 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 7) else if j.val = 4 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -2 else if k.val = 2 then -8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1916303543796241469153 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (76 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else 4) else if j.val = 2 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (76 : Fin 88)), (alphaG (n3 3) (m3 3) (76 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else 4) else if j.val = 2 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (57690091683700445453 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (77 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else -6) else if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else 5) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 4 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else 5) else if j.val = 1 then (if k.val = 0 then (20 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -7) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (77 : Fin 88)), (alphaG (n3 3) (m3 3) (77 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else -6) else if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else 5) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 4 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else 5) else if j.val = 1 then (if k.val = 0 then (20 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -7) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (31509558247647258047203 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (78 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then -3 else 0) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 3 then (if k.val = 0 then (-46 : Int) else if k.val = 1 then -1 else if k.val = 2 then 8 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 5 else if k.val = 2 then -2 else 8) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (78 : Fin 88)), (alphaG (n3 3) (m3 3) (78 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then -3 else 0) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 3 then (if k.val = 0 then (-46 : Int) else if k.val = 1 then -1 else if k.val = 2 then 8 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 5 else if k.val = 2 then -2 else 8) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3207800003276561017080487 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (79 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then 1 else if k.val = 2 then 3 else 6) else if j.val = 1 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -1) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 3 else if k.val = 2 then 7 else -3) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else 1) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 3 else if k.val = 2 then 7 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else if j.val = 1 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (79 : Fin 88)), (alphaG (n3 3) (m3 3) (79 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then 1 else if k.val = 2 then 3 else 6) else if j.val = 1 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -1) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 3 else if k.val = 2 then 7 else -3) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else 1) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 3 else if k.val = 2 then 7 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else if j.val = 1 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (33586634404144084118240 : ℚ)/10^30) :=
  ⟨L3C.pn_3_64, L3C.pn_3_65, L3C.pn_3_66, L3C.pn_3_67, L3C.pn_3_68, L3C.pn_3_69, L3C.pn_3_70, L3C.pn_3_71, L3C.pn_3_72, L3C.pn_3_73, L3C.pn_3_74, L3C.pn_3_75, L3C.pn_3_76, L3C.pn_3_77, L3C.pn_3_78, L3C.pn_3_79⟩

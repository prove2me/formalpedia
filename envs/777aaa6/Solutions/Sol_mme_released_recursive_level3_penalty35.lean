-- Prove2me | solution 1 for mme_released_recursive_level3_penalty35
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T09:53:57.670975+00:00
-- url     : https://prove2.me/submissions/ee8023bf-0d1f-4f69-bc38-8de1255bbb3d

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

theorem pn_5_64 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (64 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 6) else if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 6 else if k.val = 2 then 5 else -2) else if j.val = 2 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -6) else if j.val = 1 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -2) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then -6 else 3) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -2) else if j.val = 4 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 1) else if j.val = 1 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 4 else if k.val = 2 then -2 else 7) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (64 : Fin 88)), (alphaG (n3 5) (m3 5) (64 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 6) else if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 6 else if k.val = 2 then 5 else -2) else if j.val = 2 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -6) else if j.val = 1 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -2) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then -6 else 3) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -2) else if j.val = 4 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 1) else if j.val = 1 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 4 else if k.val = 2 then -2 else 7) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (9442469067760044572946 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (64 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (64 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (64 : Fin 88) = 1401801330449296552040000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (64 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 204881116293277678185653893362240000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (64 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((18269450157 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (64 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 47601741750429939996379668189080000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (64 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((33957552127 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (64 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 446827570645336954608295592920000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (64 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((318752423 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (64 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 52987806301453675274572818768440000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (64 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((37799797411 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (64 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 789966373630394928975515205985440000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (64 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((140884153209 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (64 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 52987767890695419633397996320400000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (64 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((3779977001 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 5 (64 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 446797968806641856813006164240000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 5) (m3 5) (64 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((159365653 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 5 (64 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 47601778996291290034189055891880000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 5) (m3 5) (64 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((33957578697 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 5 (64 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 204881120047301641128870059725360000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 5) (m3 5) (64 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((73077801967 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_65 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (65 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 3 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (65 : Fin 88)), (alphaG (n3 5) (m3 5) (65 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 3 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (911828502458973159419724 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (65 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (65 : Fin 88)))) =
        {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (65 : Fin 88) = 33095525098264157833082000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (65 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 54577570705866451505424852172464000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (65 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((206136519 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (65 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 370772095934818529518438559262278000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (65 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((11203088479 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (65 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 397525300575122708786222106310842000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (65 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((12011451681 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (65 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 10380543136216841653522564918929084000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (65 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((156826989531 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (65 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 5344344312291367902105529338171790000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (65 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((32296476919 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (65 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 5344344306598937585204094190881686000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (65 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((161482384423 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 5 (65 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 10380542285529464527740651977389356000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 5) (m3 5) (65 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((156826976679 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 5 (65 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 397525760801494725247600933149134000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 5) (m3 5) (65 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((12011465587 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 5 (65 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 370772614243837093433414383159480000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 5) (m3 5) (65 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((560155207 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 5 (65 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 54577715366406656018058740573886000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 5) (m3 5) (65 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((1649096523 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_66 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (66 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 1) else if j.val = 1 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else if j.val = 2 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 3 else if k.val = 2 then 1 else 1) else if j.val = 1 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else 1) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else 4) else if j.val = 3 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else 1) else if j.val = 4 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 3 else if k.val = 2 then 1 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (66 : Fin 88)), (alphaG (n3 5) (m3 5) (66 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 1) else if j.val = 1 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else if j.val = 2 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 3 else if k.val = 2 then 1 else 1) else if j.val = 1 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else 1) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else 4) else if j.val = 3 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else 1) else if j.val = 4 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 3 else if k.val = 2 then 1 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2116684997534798799953 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (66 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (66 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (66 : Fin 88) = 4646943431783900206368000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (66 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 1526944969516935225821319905472000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (66 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((164295627 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (66 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 58248259432154790629672032987968000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (66 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((6267373413 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (66 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 302909719798047228111617789442528000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (66 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((65184722871 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (66 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1960786727373887109895926101324544000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (66 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((52743990651 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (66 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 1960786900426060509528369786468864000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (66 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((26371997653 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (66 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 302909880888988234332302343395616000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (66 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((65184757537 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 5 (66 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 58248041959849126574926275171936000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 5) (m3 5) (66 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((12534700027 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 5 (66 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 1526956935396272069364351303072000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 5) (m3 5) (66 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((328593829 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_67 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (67 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -5 else if k.val = 2 then -7 else -4) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else 2) else if j.val = 2 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -5 else if k.val = 2 then -7 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else 2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 1) else if j.val = 2 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -6) else if j.val = 1 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 7 else if k.val = 2 then 6 else 5) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 4) else if j.val = 3 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 7 else if k.val = 2 then 6 else 5) else if j.val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (67 : Fin 88)), (alphaG (n3 5) (m3 5) (67 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -5 else if k.val = 2 then -7 else -4) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else 2) else if j.val = 2 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -5 else if k.val = 2 then -7 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else 2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 1) else if j.val = 2 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -6) else if j.val = 1 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 7 else if k.val = 2 then 6 else 5) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 4) else if j.val = 3 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 7 else if k.val = 2 then 6 else 5) else if j.val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3710134197284793983161 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (67 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (67 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (67 : Fin 88) = 10472490034229900776708000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (67 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 3494745284460804207553448790768000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (67 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((83426799 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (67 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 403591764986495318910939053706376000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (67 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((19269140561 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (67 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 1513265328572643271851338799645120000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (67 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((1806238683 : ℚ)/12500000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (67 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 408457293271167071584478388766868000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (67 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((39002882021 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (67 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 5814871773466762044929477775272084000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (67 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((555252070373 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (67 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 408457687288132119450265211628660000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (67 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((7800583929 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 5 (67 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 1513265324938689229973563230127444000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 5) (m3 5) (67 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((144499094293 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 5 (67 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 403592149222154674805998551122896000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 5) (m3 5) (67 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((9634579453 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 5 (67 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 3493967199396240994385540939784000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 5) (m3 5) (67 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((166816449 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_68 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (68 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -2) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -6) else if j.val = 1 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -3) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -1 else if k.val = 2 then 5 else 1) else if j.val = 3 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -3) else if j.val = 4 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (68 : Fin 88)), (alphaG (n3 5) (m3 5) (68 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -2) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -6) else if j.val = 1 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -3) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -1 else if k.val = 2 then 5 else 1) else if j.val = 3 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -3) else if j.val = 4 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (473822647205923510582 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (68 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (68 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (68 : Fin 88) = 9506196102826594750947000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (68 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 3111895701401100501161684424567000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (68 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((327354461 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (68 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 619962027659815159369762806249057000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (68 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((65216625131 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (68 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 4011285276662827344317627249080398000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (68 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((210982670317 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (68 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 118738870610782291200322846660812000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (68 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((3122670449 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (68 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 118738810807302608318215268453235000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (68 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((2498135101 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (68 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 4011285339555820760618378121345750000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (68 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((1687861389 : ℚ)/4000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 5 (68 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 619961974206474473175820521674076000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 5) (m3 5) (68 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((16304154877 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 5 (68 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 3111907622171013445711502112105000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 5) (m3 5) (68 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((65471143 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_69 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (69 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -2) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else -1) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -1) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else if j.val = 4 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (69 : Fin 88)), (alphaG (n3 5) (m3 5) (69 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -2) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else -1) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -1) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else if j.val = 4 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (9111055026819043582107 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (69 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (69 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (69 : Fin 88) = 3148655891324359004880000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (69 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 22261899890199196206174453125280000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (69 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((3535143353 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (69 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 551863786628115102507504068411040000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (69 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((87634820329 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (69 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 1000202240166916146714409756051920000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (69 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((317660066609 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (69 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1000202325473450210365268275265760000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (69 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((158830046851 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (69 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 551863828281683888837449343968560000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (69 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((175269653887 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (69 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 22261810883994460249194103177440000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (69 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((3535129219 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_70 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (70 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -1) else if j.val = 1 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 1) else if j.val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -8 else if k.val = 2 then -4 else 2) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -8 else if k.val = 2 then -4 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (70 : Fin 88)), (alphaG (n3 5) (m3 5) (70 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -1) else if j.val = 1 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 1) else if j.val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -8 else if k.val = 2 then -4 else 2) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -8 else if k.val = 2 then -4 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (33260461387215027710978 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (70 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (70 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (70 : Fin 88) = 3596175750527312310072000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (70 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 25431211066230196510022219433096000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (70 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((7071737543 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (70 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1140716985472074561303628348191576000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (70 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((317202791133 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (70 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 631939699601151629033397392343288000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (70 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((175725477129 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (70 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 631939659719562555685503873644808000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (70 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((175725466039 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (70 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1140717067044129110514653477554752000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (70 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((39650351727 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (70 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 25431127624164257024794688832480000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (70 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((353585717 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_71 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (71 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else 0) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 2) else if j.val = 4 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (71 : Fin 88)), (alphaG (n3 5) (m3 5) (71 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else 0) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 2) else if j.val = 4 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (143745971072684059864 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (71 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (71 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (71 : Fin 88) = 110583728050019398872000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (71 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 12958749365462118474922225624008000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (71 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((117184956539 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (71 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 42333114210135310165798937360184000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (71 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((382815039397 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (71 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 42333114210798812534099053753416000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (71 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((382815039403 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (71 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 12958750263623157697179783262392000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (71 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((117184964661 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_72 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (72 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 3 then (if k.val = 0 then (35 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -8) else if j.val = 4 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (72 : Fin 88)), (alphaG (n3 5) (m3 5) (72 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 3 then (if k.val = 0 then (35 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -8) else if j.val = 4 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2156183255827502102965 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (72 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (72 : Fin 88)))) =
        {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (72 : Fin 88) = 110865048325768066050000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (72 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 13142019094931455860260765182050000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (72 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((118540687921 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (72 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 42287589219731231986251989760000000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (72 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((14899727 : ℚ)/39062500) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (72 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 42291995456509053416156986669350000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (72 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((381472755347 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (72 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 13143444554596324787330258388600000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (72 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((29638386383 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_73 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (73 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 3) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -7 else if k.val = 2 then 6 else 0) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else 8) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 0 else if k.val = 2 then -3 else 1) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else 8) else if j.val = 4 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (73 : Fin 88)), (alphaG (n3 5) (m3 5) (73 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 3) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -7 else if k.val = 2 then 6 else 0) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else 8) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 0 else if k.val = 2 then -3 else 1) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else 8) else if j.val = 4 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2137508650212776875494 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (73 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (73 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (73 : Fin 88) = 32229338364051993069668000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (73 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 399695204441805168121560689799788000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (73 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((12401595091 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (73 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 10577559368019441440844579937804000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (73 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((328196603 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (73 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 13690720403891978535073896643356484000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (73 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((424790613113 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (73 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2013675161116918878649285553584960000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (73 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((780994609 : ℚ)/12500000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (73 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 2013673461373842896911223052364308000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (73 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((62479515981 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (73 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 13690721103848749125555082130406108000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (73 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((424790634831 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 5 (73 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 10579636355500974407485961622396000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 5) (m3 5) (73 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((328261047 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 5 (73 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 399695833655178049508621388928152000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 5) (m3 5) (73 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((6200807307 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_74 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (74 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 4) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -2) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 5 else if k.val = 2 then -6 else 7) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 4 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (74 : Fin 88)), (alphaG (n3 5) (m3 5) (74 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 4) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -2) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 5 else if k.val = 2 then -6 else 7) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 4 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2831660529263712664573 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (74 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (74 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (74 : Fin 88) = 2057858096960535038172000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (74 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 360313492174920696266922311573004000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (74 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((175091515157 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (74 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 14482416221299547051099499328320000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (74 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((87970207 : ℚ)/12500000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (74 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 654133168857019187470179092819580000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (74 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((63574176453 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (74 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 654133012937226896964360320603484000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (74 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((317870806497 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (74 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 14482546372592747417098523554632000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (74 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((3518839903 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (74 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 360313460397475963002340252120980000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (74 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((35018299943 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_75 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (75 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else 4) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -2) else if j.val = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -7 else if k.val = 2 then -5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (75 : Fin 88)), (alphaG (n3 5) (m3 5) (75 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else 4) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -2) else if j.val = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -7 else if k.val = 2 then -5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1685591792850176033033 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (75 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (75 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (75 : Fin 88) = 110138059707412158324000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (75 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 42146049737168866085994247234356000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (75 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((382665627569 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (75 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12942933564593199698647544026368000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (75 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((1836180313 : ℚ)/15625000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (75 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 12906530082292911020979852009852000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (75 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((117185014123 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (75 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 42142546323357181518378356729424000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (75 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((95658454569 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_76 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (76 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else 5) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 8 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (76 : Fin 88)), (alphaG (n3 5) (m3 5) (76 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else 5) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 8 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3117062480058143178939 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (76 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (76 : Fin 88)))) =
        {(⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (76 : Fin 88) = 904233765570637817350000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (76 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 6609780250924680876390849256850000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (76 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((7309813571 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (76 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 160054255683584380414814584298750000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (76 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((7080215837 : ℚ)/40000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (76 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 285449279053618853472125436878100000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (76 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((157840422423 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (76 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 285457084459162687745426898023200000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (76 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((19730592307 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (76 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 160049796476471079188113630390150000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (76 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((177000464449 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (76 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 6613569646876135653128601152950000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (76 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((7314004297 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_77 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (77 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 5 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else 5) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 1) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else 3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (77 : Fin 88)), (alphaG (n3 5) (m3 5) (77 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 5 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else 5) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 1) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else 3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (9123642646997317604554 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (77 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (77 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (77 : Fin 88) = 28366363706824710413100000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (77 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 9537296766557590620871649785800000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (77 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((168109259 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (77 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1173696796574635294288841530231800000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (77 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((20688178589 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (77 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 1091792469350852301485319619540500000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (77 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((7697796451 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (77 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 4056551247040215914341511997579000000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (77 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((14300568409 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (77 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 15703211230977346929354967806294000000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (77 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((27679281337 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (77 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 4056549016763235828955480478004600000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (77 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((71502802733 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 5 (77 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 1091792353105493830917656346656700000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 5) (m3 5) (77 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((38488978157 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 5 (77 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 1173696030626082482608010955705600000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 5) (m3 5) (77 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((646505159 : ℚ)/15625000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 5 (77 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 9537265620290240527339616202000000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 5) (m3 5) (77 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((16810871 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_78 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (78 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -6 else if k.val = 2 then -2 else 2) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 3 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -6 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 4 else -1) else if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (78 : Fin 88)), (alphaG (n3 5) (m3 5) (78 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -6 else if k.val = 2 then -2 else 2) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 3 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -6 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 4 else -1) else if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3350359406253675879797792 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (78 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (78 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (78 : Fin 88) = 35191207509593212535104000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (78 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 382897137177441459460951890342208000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (78 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((10880477377 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (78 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 53609987345013071192687623663808000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (78 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((1523391527 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (78 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 5751658531190302491925819467048704000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (78 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((40860053819 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (78 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 11002084139656922626237332069218560000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (78 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((15631865057 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (78 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 405356524689998030532436696132800000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (78 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((460747503 : ℚ)/40000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (78 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 405352420374657394185651939488384000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (78 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((5759285473 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 5 (78 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 11002092422787390196739732519322560000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 5) (m3 5) (78 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((62527507303 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 5 (78 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 5751655055636266429480963075107456000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 5) (m3 5) (78 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((81720058257 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 5 (78 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 53608756638104045698858846006720000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 5) (m3 5) (78 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((304671311 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 5 (78 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 382892534097116789649565873668800000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 5) (m3 5) (78 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((435213863 : ℚ)/40000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_79 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (79 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -2 else if k.val = 2 then -8 else -1) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -7) else if j.val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -2 else if k.val = 2 then -8 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 0) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 6) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 6) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (35 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -8) else if j.val = 1 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else -4) else if j.val = 2 then (if k.val = 0 then (35 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (79 : Fin 88)), (alphaG (n3 5) (m3 5) (79 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -2 else if k.val = 2 then -8 else -1) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -7) else if j.val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -2 else if k.val = 2 then -8 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 0) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 6) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 6) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (35 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -8) else if j.val = 1 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else -4) else if j.val = 2 then (if k.val = 0 then (35 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (16554276624361082535511 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (79 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (79 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (79 : Fin 88) = 7577742413099649053744000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (79 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 1093905542437247126033517777291936000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (79 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((72178855047 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (79 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 271439221374928117352151982442576000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (79 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((35820592279 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (79 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 2491020692507581359426835147120000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (79 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((65745721 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (79 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 305879736489378817137730890435488000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (79 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((20182774751 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (79 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 4230312273423625867405956454878816000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (79 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((279127479057 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (79 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 305879415140056304820913468313680000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (79 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((8073101419 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 5 (79 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 2490887619773064916489802348736000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 5) (m3 5) (79 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((82177761 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 5 (79 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 271439350113193973502089756499392000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 5) (m3 5) (79 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((8955152317 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 5 (79 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 1093904965808938201215723032642256000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 5) (m3 5) (79 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((144357633999 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    (((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (64 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 6) else if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 6 else if k.val = 2 then 5 else -2) else if j.val = 2 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -6) else if j.val = 1 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -2) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then -6 else 3) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -2) else if j.val = 4 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 1) else if j.val = 1 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 4 else if k.val = 2 then -2 else 7) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (64 : Fin 88)), (alphaG (n3 5) (m3 5) (64 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 6) else if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 6 else if k.val = 2 then 5 else -2) else if j.val = 2 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -6) else if j.val = 1 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -2) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then -6 else 3) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -2) else if j.val = 4 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 1) else if j.val = 1 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 4 else if k.val = 2 then -2 else 7) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (9442469067760044572946 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (65 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 3 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (65 : Fin 88)), (alphaG (n3 5) (m3 5) (65 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 3 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (911828502458973159419724 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (66 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 1) else if j.val = 1 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else if j.val = 2 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 3 else if k.val = 2 then 1 else 1) else if j.val = 1 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else 1) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else 4) else if j.val = 3 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else 1) else if j.val = 4 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 3 else if k.val = 2 then 1 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (66 : Fin 88)), (alphaG (n3 5) (m3 5) (66 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 1) else if j.val = 1 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else if j.val = 2 then (if k.val = 0 then (-42 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 7) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 3 else if k.val = 2 then 1 else 1) else if j.val = 1 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else 1) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else 4) else if j.val = 3 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else 1) else if j.val = 4 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 3 else if k.val = 2 then 1 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2116684997534798799953 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (67 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -5 else if k.val = 2 then -7 else -4) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else 2) else if j.val = 2 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -5 else if k.val = 2 then -7 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else 2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 1) else if j.val = 2 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -6) else if j.val = 1 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 7 else if k.val = 2 then 6 else 5) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 4) else if j.val = 3 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 7 else if k.val = 2 then 6 else 5) else if j.val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (67 : Fin 88)), (alphaG (n3 5) (m3 5) (67 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -5 else if k.val = 2 then -7 else -4) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else 2) else if j.val = 2 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -5 else if k.val = 2 then -7 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else 2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 1) else if j.val = 2 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -6) else if j.val = 1 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 7 else if k.val = 2 then 6 else 5) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 4) else if j.val = 3 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 7 else if k.val = 2 then 6 else 5) else if j.val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3710134197284793983161 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (68 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -2) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -6) else if j.val = 1 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -3) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -1 else if k.val = 2 then 5 else 1) else if j.val = 3 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -3) else if j.val = 4 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (68 : Fin 88)), (alphaG (n3 5) (m3 5) (68 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -2) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -6) else if j.val = 1 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -3) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -1 else if k.val = 2 then 5 else 1) else if j.val = 3 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -3) else if j.val = 4 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (473822647205923510582 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (69 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -2) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else -1) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -1) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else if j.val = 4 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (69 : Fin 88)), (alphaG (n3 5) (m3 5) (69 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -2) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else -1) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -1) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else if j.val = 4 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (9111055026819043582107 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (70 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -1) else if j.val = 1 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 1) else if j.val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -8 else if k.val = 2 then -4 else 2) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -8 else if k.val = 2 then -4 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (70 : Fin 88)), (alphaG (n3 5) (m3 5) (70 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -1) else if j.val = 1 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 1) else if j.val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -8 else if k.val = 2 then -4 else 2) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -8 else if k.val = 2 then -4 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (33260461387215027710978 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (71 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else 0) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 2) else if j.val = 4 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (71 : Fin 88)), (alphaG (n3 5) (m3 5) (71 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else 0) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 2) else if j.val = 4 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (143745971072684059864 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (72 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 3 then (if k.val = 0 then (35 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -8) else if j.val = 4 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (72 : Fin 88)), (alphaG (n3 5) (m3 5) (72 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 3 then (if k.val = 0 then (35 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -8) else if j.val = 4 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2156183255827502102965 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (73 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 3) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -7 else if k.val = 2 then 6 else 0) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else 8) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 0 else if k.val = 2 then -3 else 1) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else 8) else if j.val = 4 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (73 : Fin 88)), (alphaG (n3 5) (m3 5) (73 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 3) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -7 else if k.val = 2 then 6 else 0) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else 8) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 0 else if k.val = 2 then -3 else 1) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else 8) else if j.val = 4 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2137508650212776875494 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (74 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 4) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -2) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 5 else if k.val = 2 then -6 else 7) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 4 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (74 : Fin 88)), (alphaG (n3 5) (m3 5) (74 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 4) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -2) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 5 else if k.val = 2 then -6 else 7) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 4 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2831660529263712664573 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (75 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else 4) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -2) else if j.val = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -7 else if k.val = 2 then -5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (75 : Fin 88)), (alphaG (n3 5) (m3 5) (75 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else 4) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -2) else if j.val = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -7 else if k.val = 2 then -5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1685591792850176033033 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (76 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else 5) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 8 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (76 : Fin 88)), (alphaG (n3 5) (m3 5) (76 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else 5) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 8 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3117062480058143178939 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (77 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 5 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else 5) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 1) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else 3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (77 : Fin 88)), (alphaG (n3 5) (m3 5) (77 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 5 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else 5) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 1) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else 3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (9123642646997317604554 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (78 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -6 else if k.val = 2 then -2 else 2) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 3 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -6 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 4 else -1) else if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (78 : Fin 88)), (alphaG (n3 5) (m3 5) (78 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -6 else if k.val = 2 then -2 else 2) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 3 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -6 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 4 else -1) else if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3350359406253675879797792 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (79 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -2 else if k.val = 2 then -8 else -1) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -7) else if j.val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -2 else if k.val = 2 then -8 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 0) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 6) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 6) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (35 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -8) else if j.val = 1 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else -4) else if j.val = 2 then (if k.val = 0 then (35 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (79 : Fin 88)), (alphaG (n3 5) (m3 5) (79 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -2 else if k.val = 2 then -8 else -1) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -7) else if j.val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -2 else if k.val = 2 then -8 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 0) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 6) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 6) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (35 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -8) else if j.val = 1 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else -4) else if j.val = 2 then (if k.val = 0 then (35 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (16554276624361082535511 : ℚ)/10^30) :=
  ⟨L3C.pn_5_64, L3C.pn_5_65, L3C.pn_5_66, L3C.pn_5_67, L3C.pn_5_68, L3C.pn_5_69, L3C.pn_5_70, L3C.pn_5_71, L3C.pn_5_72, L3C.pn_5_73, L3C.pn_5_74, L3C.pn_5_75, L3C.pn_5_76, L3C.pn_5_77, L3C.pn_5_78, L3C.pn_5_79⟩

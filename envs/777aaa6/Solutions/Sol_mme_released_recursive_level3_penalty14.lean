-- Prove2me | solution 1 for mme_released_recursive_level3_penalty14
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T08:18:53.029403+00:00
-- url     : https://prove2.me/submissions/4a812b33-eda1-47ab-8464-c2068d437760

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

theorem pn_2_16 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (16 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else 4) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -1) else if j.val = 4 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (16 : Fin 88)), (alphaG (n3 2) (m3 2) (16 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else 4) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -1) else if j.val = 4 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3870159008721074389464 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (16 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (16 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (16 : Fin 88) = 110627931194120315100000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (16 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 12969182804860179947030344785900000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (16 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((117232444509 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (16 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 42344826302275944181683704359200000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (16 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((47845993599 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (16 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 42344624933775490845674309256000000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (16 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((4784576607 : ℚ)/12500000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (16 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 12969297153208700125611641598900000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (16 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((117233478139 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_17 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (17 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else -6) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -2) else if j.val = 2 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else 2) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 5) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 5) else if j.val = 4 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (17 : Fin 88)), (alphaG (n3 2) (m3 2) (17 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else -6) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -2) else if j.val = 2 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else 2) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 5) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 5) else if j.val = 4 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1432151561761682503066 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (17 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (17 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (17 : Fin 88) = 3159937839803471119432000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (17 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 22353290458290070169026683260272000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (17 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((3536982623 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (17 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 554047277204681020691924337002880000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (17 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((2191685823 : ℚ)/12500000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (17 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 1003568337977964997821983817740232000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (17 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((317591164401 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (17 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1003568453514772234556298357532448000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (17 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((79397800241 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (17 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 554047324006520366021135086910232000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (17 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((175334880651 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (17 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 22353156641242430171631717553936000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (17 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((3536961449 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_18 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (18 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-40 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 6) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 3 then (if k.val = 0 then (-40 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 8 else if k.val = 2 then -7 else 8) else if j.val = 1 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else 5) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 0) else if j.val = 3 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else 5) else if j.val = 4 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 8 else if k.val = 2 then -7 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (18 : Fin 88)), (alphaG (n3 2) (m3 2) (18 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-40 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 6) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 3 then (if k.val = 0 then (-40 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 8 else if k.val = 2 then -7 else 8) else if j.val = 1 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else 5) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 0) else if j.val = 3 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else 5) else if j.val = 4 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 8 else if k.val = 2 then -7 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (959986475987715193510 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (18 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (18 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (18 : Fin 88) = 4222826625845868209883000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (18 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 1375165872380923959618069324012000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (18 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((81412641 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (18 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 52451633450325791041454968161750000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (18 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((49683909 : ℚ)/4000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (18 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 275503329288824159694789131209794000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (18 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((32620724659 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (18 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1782083296621700171242348741352712000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (18 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((52751493683 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (18 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 1782082935358882330128323385862062000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (18 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((211005931957 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (18 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 275502930793343958497743769180733000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (18 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((65241354951 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 2 (18 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 52452141249450375632953074802383000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 2) (m3 2) (18 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((12421097501 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 2 (18 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 1375193210960499685768860106554000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 2) (m3 2) (18 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((162828519 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_19 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (19 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else -1) else if j.val = 3 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -6 else if k.val = 2 then -4 else 3) else if j.val = 4 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (19 : Fin 88)), (alphaG (n3 2) (m3 2) (19 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else -1) else if j.val = 3 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -6 else if k.val = 2 then -4 else 3) else if j.val = 4 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (11287538636038196778693 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (19 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (19 : Fin 88)))) =
        {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (19 : Fin 88) = 109599759972492300994000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (19 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 12511903769275097173519273602372000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (19 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((57079977969 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (19 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 42237132741565735541882418766662000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (19 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((385376142723 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (19 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 42245192670321394955132658285720000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (19 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((19272484119 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (19 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 12605530791330073323465649345246000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (19 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((115014218959 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_20 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (20 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else -5) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -3) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 1) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 4 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (20 : Fin 88)), (alphaG (n3 2) (m3 2) (20 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else -5) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -3) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 1) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 4 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (11085311997805938436689 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (20 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (20 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (20 : Fin 88) = 3550665399159463382688000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (20 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 25094229983595726391236758278176000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (20 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((7067472477 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (20 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1126512383559805714997384398405152000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (20 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((317267964429 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (20 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 623726208321246597007297743091392000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (20 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((87832298767 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (20 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 623725964759802876264747544225344000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (20 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((87832264469 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (20 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1126512918368129467194078025637088000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (20 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((317268115051 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (20 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 25093694166883000833255530362848000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (20 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((7067321571 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_21 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (21 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -7) else if j.val = 1 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 5 else if k.val = 2 then -6 else -3) else if j.val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else 2) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else -3) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 6) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 4) else if j.val = 3 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 4 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (21 : Fin 88)), (alphaG (n3 2) (m3 2) (21 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -7) else if j.val = 1 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 5 else if k.val = 2 then -6 else -3) else if j.val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else 2) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else -3) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 6) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 4) else if j.val = 3 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 4 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (10221328523279419114689 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (21 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (21 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (21 : Fin 88) = 9995269453890851439006000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (21 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 3332960051674548141356892655482000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (21 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((333453747 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (21 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 385853095066914732980768840082624000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (21 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((1206361597 : ℚ)/31250000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (21 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 1444290072214682019540431677409190000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (21 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((28899472473 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (21 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 389224308873909439834281176355222000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (21 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((38940852037 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (21 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 5549868608513693830787075969506194000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (21 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((555249524199 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (21 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 389224315170929195785517582929002000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (21 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((38940852667 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 2 (21 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 1444290050524947304597284054766170000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 2) (m3 2) (21 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((28899472039 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 2 (21 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 385853077695136422118469039090196000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 2) (m3 2) (21 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((19301784683 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 2 (21 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 3332965778963945220814767205920000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 2) (m3 2) (21 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((4168179 : ℚ)/12500000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_22 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (22 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 3 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 3 else if k.val = 2 then 4 else 7) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -5) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 3 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (22 : Fin 88)), (alphaG (n3 2) (m3 2) (22 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 3 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 3 else if k.val = 2 then 4 else 7) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -5) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 3 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (816293504546845321965369 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (22 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (22 : Fin 88)))) =
        {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (22 : Fin 88) = 26453150351246742424478000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (22 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 43036125739053525570018253706628000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (22 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((813440463 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (22 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 292123145262766183453384729624906000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (22 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((11043038027 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (22 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 318166105710690696243234379752022000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (22 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((12027531749 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (22 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 8300514152064494052552394282945526000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (22 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((313781687317 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (22 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 4272731569146146410437117105536174000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (22 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((161520707833 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (22 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 4272732115350794862979854686157918000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (22 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((161520728481 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 2 (22 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 8300483138946538408247757415852364000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 2) (m3 2) (22 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((156890257469 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 2 (22 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 318182382598633321876315585310202000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 2) (m3 2) (22 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((12028147059 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 2 (22 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 292140543499752198435877308805506000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 2) (m3 2) (22 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((11043695727 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 2 (22 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 43041072927872764682046252308754000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 2) (m3 2) (22 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((1627067943 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_23 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (23 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -5 else 6) else if j.val = 1 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-49 : Int) else if k.val = 1 then 2 else if k.val = 2 then 7 else 8) else if j.val = 1 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 1) else if j.val = 2 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else 5) else if j.val = 3 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 1) else if j.val = 4 then (if k.val = 0 then (-49 : Int) else if k.val = 1 then 2 else if k.val = 2 then 7 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (23 : Fin 88)), (alphaG (n3 2) (m3 2) (23 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -5 else 6) else if j.val = 1 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-49 : Int) else if k.val = 1 then 2 else if k.val = 2 then 7 else 8) else if j.val = 1 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 1) else if j.val = 2 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else 5) else if j.val = 3 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 1) else if j.val = 4 then (if k.val = 0 then (-49 : Int) else if k.val = 1 then 2 else if k.val = 2 then 7 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2480581593300830232074 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (23 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (23 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (23 : Fin 88) = 9424289486287513634146000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (23 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 3114901920906335225924834725394000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (23 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((330518489 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (23 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 613848425910641498629224833682098000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (23 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((65134716713 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (23 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 3976237081082893533133386304215910000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (23 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((84382744967 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (23 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 118944338036728402544619535571582000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (23 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((12621040367 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (23 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 118944316238346820761600499791884000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (23 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((6310519027 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (23 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 3976237103861401221490306757946792000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (23 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((105478431813 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 2 (23 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 613848418993213015694189826218934000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 2) (m3 2) (23 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((65134715979 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 2 (23 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 3114900243382806666747407847406000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 2) (m3 2) (23 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((330518311 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_24 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (24 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -7) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 3 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else 1) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 3 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else 4) else if j.val = 1 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else -8) else if j.val = 2 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (24 : Fin 88)), (alphaG (n3 2) (m3 2) (24 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -7) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 3 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else 1) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 3 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else 4) else if j.val = 1 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else -8) else if j.val = 2 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3154671084367053930059529 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (24 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (24 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (24 : Fin 88) = 28450932656425798423724000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (24 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 305184438832965839586495030694944000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (24 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((1340836707 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (24 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 43199624467560996116633373459524000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (24 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((1518390451 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (24 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 4648142413817851063208344669670768000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (24 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((40843497733 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (24 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 8897684602322618082196601805486288000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (24 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((78184472103 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (24 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 331255342887588458210466306367468000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (24 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((11643039857 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (24 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 331255202795196057969834867950492000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (24 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((11643034933 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 2 (24 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 8897684264154832527919561741102824000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 2) (m3 2) (24 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((156368938263 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 2 (24 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 4648142166038678558396066197458452000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 2) (m3 2) (24 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((163373982223 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 2 (24 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 43199676390513094093715496755824000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 2) (m3 2) (24 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((379598069 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 2 (24 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 305184924717993746026280511053416000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 2) (m3 2) (24 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((5363355367 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_25 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (25 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else if j.val = 1 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 5 else if k.val = 2 then -2 else 4) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 4 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else 4) else if j.val = 1 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else -4) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (25 : Fin 88)), (alphaG (n3 2) (m3 2) (25 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else if j.val = 1 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 5 else if k.val = 2 then -2 else 4) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 4 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else 4) else if j.val = 1 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else -4) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (36169001282656064757343 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (25 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (25 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (25 : Fin 88) = 7958124616234841503676000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (25 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 1138620945794800303257508964535684000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (25 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((143076541359 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (25 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 296108253604073769429545901838808000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (25 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((18604147829 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (25 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 2671816726351184059066140400692000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (25 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((335734467 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (25 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 334069983284739071784528690288336000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (25 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((10494620259 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (25 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 4415182635408232603921677245684396000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (25 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((554801897221 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (25 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 334069984661494630393156270424284000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (25 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((41978481209 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 2 (25 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 2671860718864062605269972721620000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 2) (m3 2) (25 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((67147999 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 2 (25 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 296108216153139325428381785539552000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 2) (m3 2) (25 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((4651036369 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 2 (25 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 1138620919883146552796865028566628000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 2) (m3 2) (25 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((143076538103 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_26 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (26 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 7) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 3 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else 7) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else -1) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -4 else if k.val = 2 then -4 else 8) else if j.val = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else -1) else if j.val = 4 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (26 : Fin 88)), (alphaG (n3 2) (m3 2) (26 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 7) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 3 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else 7) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else -1) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -4 else if k.val = 2 then -4 else 8) else if j.val = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else -1) else if j.val = 4 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (7100598145725263230292 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (26 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (26 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (26 : Fin 88) = 30242340581612341046595000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (26 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 374571011843952462222774412703385000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (26 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((12385648883 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (26 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 9819270158672051581725496743480000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (26 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((40585773 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (26 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 12760258011796397723950010011597605000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (26 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((421933546359 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (26 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 1976522231143349068385734461694020000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (26 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((16339031579 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (26 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 1976521590822271933907637482138085000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (26 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((65356105143 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (26 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 12760257286403616533396397667969935000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (26 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((421933522373 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 2 (26 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 9819227063336722784139505345605000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 2) (m3 2) (26 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((324684759 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 2 (26 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 374571952380744550366580961807885000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 2) (m3 2) (26 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((12385679983 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_27 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (27 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -8) else if j.val = 2 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (27 : Fin 88)), (alphaG (n3 2) (m3 2) (27 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -8) else if j.val = 2 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (20239756374482216018426 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (27 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (27 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (27 : Fin 88) = 1067565323188657636037000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (27 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 188977570412522506302611094067043000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (27 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((177017336839 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (27 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 336983649247873649653107289270415000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (27 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((63131246759 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (27 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 7821418019401857313661911797705000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (27 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((1465281393 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (27 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 7821438986384804738897883564385000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (27 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((1465285321 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (27 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 336983668101077257164801141683835000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (27 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((63131250291 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (27 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 188977578421397560863920679616617000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (27 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((177017344341 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_28 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (28 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else 3) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else 3) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else -5) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 4 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (28 : Fin 88)), (alphaG (n3 2) (m3 2) (28 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else 3) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else 3) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else -5) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 4 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (6452114226374007672304 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (28 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (28 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (28 : Fin 88) = 1778178124458896328960000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (28 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 313147375963984730887010524700160000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (28 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((88052870423 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (28 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12904144178150814407018555013120000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (28 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((907118359 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (28 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 563037541904160272366704598403840000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (28 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((316637312179 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (28 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 563037534631411743329818612957440000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (28 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((316637308089 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (28 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 12904161506496637258963280728320000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (28 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((7256956617 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (28 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 313147366274692130710484428197120000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (28 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((176105735397 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_29 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (29 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 3 then (if k.val = 0 then (37 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -8) else if j.val = 4 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (29 : Fin 88)), (alphaG (n3 2) (m3 2) (29 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 3 then (if k.val = 0 then (37 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -8) else if j.val = 4 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5479168424635914260119 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (29 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (29 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (29 : Fin 88) = 110875819618488495483000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (29 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 42290954756947635669473649755715000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (29 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((76285262021 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (29 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 13146954851611378562562173420055000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (29 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((23714737617 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (29 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 13146955328488278741681192492438000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (29 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((59286846193 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (29 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 42290954681441202509282984331792000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (29 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((23839144339 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_30 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (30 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 5) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 2) else if j.val = 4 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (30 : Fin 88)), (alphaG (n3 2) (m3 2) (30 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 5) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 2) else if j.val = 4 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1925798183544522436002 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (30 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (30 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (30 : Fin 88) = 109633592578680084800000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (30 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 12569928401034286302528862382400000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (30 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((114653986113 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (30 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 42246812947075339180626841369600000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (30 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((24084094547 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (30 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 42246897750742237048667355780800000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (30 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((385346286271 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (30 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 12569953479828222268176940467200000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (30 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((7165888429 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_2_31 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (31 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else 8) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -2 else if k.val = 2 then 7 else 0) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -5) else if j.val = 2 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (31 : Fin 88)), (alphaG (n3 2) (m3 2) (31 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else 8) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -2 else if k.val = 2 then 7 else 0) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -5) else if j.val = 2 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (663208047110890953191 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (31 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (31 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 2 (31 : Fin 88) = 3442861992175346344736000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 2 (31 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 22779325082662356924069888635552000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 2) (m3 2) (31 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((6616392157 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 2 (31 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 593691378936612774713296754756128000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 2) (m3 2) (31 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((172441236473 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 2 (31 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 1104960149984926485646265055698336000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 2) (m3 2) (31 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((320942330101 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 2 (31 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1104960378594405628081437692513472000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 2) (m3 2) (31 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((160471198251 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 2 (31 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 593691512598843896936767896441856000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 2) (m3 2) (31 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((5388789853 : ℚ)/31250000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 2 (31 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 22779246977895202434162711954656000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 2) (m3 2) (31 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((6616369471 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    (((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (16 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else 4) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -1) else if j.val = 4 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (16 : Fin 88)), (alphaG (n3 2) (m3 2) (16 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else 4) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -1) else if j.val = 4 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3870159008721074389464 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (17 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else -6) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -2) else if j.val = 2 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else 2) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 5) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 5) else if j.val = 4 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (17 : Fin 88)), (alphaG (n3 2) (m3 2) (17 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else -6) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -2) else if j.val = 2 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else 2) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 5) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 5) else if j.val = 4 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1432151561761682503066 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (18 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-40 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 6) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 3 then (if k.val = 0 then (-40 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 8 else if k.val = 2 then -7 else 8) else if j.val = 1 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else 5) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 0) else if j.val = 3 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else 5) else if j.val = 4 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 8 else if k.val = 2 then -7 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (18 : Fin 88)), (alphaG (n3 2) (m3 2) (18 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-40 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 6) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 3 then (if k.val = 0 then (-40 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 8 else if k.val = 2 then -7 else 8) else if j.val = 1 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else 5) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 0) else if j.val = 3 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 2 else if k.val = 2 then 6 else 5) else if j.val = 4 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 8 else if k.val = 2 then -7 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (959986475987715193510 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (19 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else -1) else if j.val = 3 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -6 else if k.val = 2 then -4 else 3) else if j.val = 4 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (19 : Fin 88)), (alphaG (n3 2) (m3 2) (19 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else -1) else if j.val = 3 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -6 else if k.val = 2 then -4 else 3) else if j.val = 4 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (11287538636038196778693 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (20 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else -5) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -3) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 1) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 4 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (20 : Fin 88)), (alphaG (n3 2) (m3 2) (20 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else -5) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -3) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 1) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -3) else if j.val = 4 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (11085311997805938436689 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (21 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -7) else if j.val = 1 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 5 else if k.val = 2 then -6 else -3) else if j.val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else 2) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else -3) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 6) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 4) else if j.val = 3 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 4 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (21 : Fin 88)), (alphaG (n3 2) (m3 2) (21 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -7) else if j.val = 1 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 5 else if k.val = 2 then -6 else -3) else if j.val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else 2) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else -3) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 6) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 4) else if j.val = 3 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 4 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (10221328523279419114689 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (22 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 3 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 3 else if k.val = 2 then 4 else 7) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -5) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 3 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (22 : Fin 88)), (alphaG (n3 2) (m3 2) (22 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 3 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 3 else if k.val = 2 then 4 else 7) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -5) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 3 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (816293504546845321965369 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (23 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -5 else 6) else if j.val = 1 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-49 : Int) else if k.val = 1 then 2 else if k.val = 2 then 7 else 8) else if j.val = 1 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 1) else if j.val = 2 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else 5) else if j.val = 3 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 1) else if j.val = 4 then (if k.val = 0 then (-49 : Int) else if k.val = 1 then 2 else if k.val = 2 then 7 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (23 : Fin 88)), (alphaG (n3 2) (m3 2) (23 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -5 else 6) else if j.val = 1 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-49 : Int) else if k.val = 1 then 2 else if k.val = 2 then 7 else 8) else if j.val = 1 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 1) else if j.val = 2 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else 5) else if j.val = 3 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 1) else if j.val = 4 then (if k.val = 0 then (-49 : Int) else if k.val = 1 then 2 else if k.val = 2 then 7 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2480581593300830232074 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (24 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -7) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 3 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else 1) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 3 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else 4) else if j.val = 1 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else -8) else if j.val = 2 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (24 : Fin 88)), (alphaG (n3 2) (m3 2) (24 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -7) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 3 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else 1) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 3 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else 4) else if j.val = 1 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else -8) else if j.val = 2 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3154671084367053930059529 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (25 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else if j.val = 1 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 5 else if k.val = 2 then -2 else 4) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 4 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else 4) else if j.val = 1 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else -4) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (25 : Fin 88)), (alphaG (n3 2) (m3 2) (25 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else if j.val = 1 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 5 else if k.val = 2 then -2 else 4) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 4 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else 4) else if j.val = 1 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else -4) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (36169001282656064757343 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (26 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 7) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 3 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else 7) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else -1) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -4 else if k.val = 2 then -4 else 8) else if j.val = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else -1) else if j.val = 4 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (26 : Fin 88)), (alphaG (n3 2) (m3 2) (26 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 7) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 3 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else 7) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else -1) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -4 else if k.val = 2 then -4 else 8) else if j.val = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else -1) else if j.val = 4 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (7100598145725263230292 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (27 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -8) else if j.val = 2 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (27 : Fin 88)), (alphaG (n3 2) (m3 2) (27 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -8) else if j.val = 2 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 7) else if j.val = 2 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (20239756374482216018426 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (28 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else 3) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else 3) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else -5) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 4 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (28 : Fin 88)), (alphaG (n3 2) (m3 2) (28 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else 3) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else 3) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else -5) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 4 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (6452114226374007672304 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (29 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 3 then (if k.val = 0 then (37 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -8) else if j.val = 4 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (29 : Fin 88)), (alphaG (n3 2) (m3 2) (29 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 3 then (if k.val = 0 then (37 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -8) else if j.val = 4 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5479168424635914260119 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (30 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 5) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 2) else if j.val = 4 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (30 : Fin 88)), (alphaG (n3 2) (m3 2) (30 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 5) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 2) else if j.val = 4 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1925798183544522436002 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (31 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else 8) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -2 else if k.val = 2 then 7 else 0) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -5) else if j.val = 2 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (31 : Fin 88)), (alphaG (n3 2) (m3 2) (31 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else 8) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -2 else if k.val = 2 then 7 else 0) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -5) else if j.val = 2 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (663208047110890953191 : ℚ)/10^30) :=
  ⟨L3C.pn_2_16, L3C.pn_2_17, L3C.pn_2_18, L3C.pn_2_19, L3C.pn_2_20, L3C.pn_2_21, L3C.pn_2_22, L3C.pn_2_23, L3C.pn_2_24, L3C.pn_2_25, L3C.pn_2_26, L3C.pn_2_27, L3C.pn_2_28, L3C.pn_2_29, L3C.pn_2_30, L3C.pn_2_31⟩

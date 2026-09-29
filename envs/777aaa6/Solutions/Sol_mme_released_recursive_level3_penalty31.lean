-- Prove2me | solution 1 for mme_released_recursive_level3_penalty31
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T09:46:07.560984+00:00
-- url     : https://prove2.me/submissions/81f37372-c9b5-4e5e-82a2-b33fdbaa8501

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

theorem pn_5_0 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (0 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (46 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -8) else if j.val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (0 : Fin 88)), (alphaG (n3 5) (m3 5) (0 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (46 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -8) else if j.val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1324353347151069108639 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (0 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (0 : Fin 88)))) =
        {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (0 : Fin 88) = 109665116943443773392000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (0 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 12524202159652761094048029395232000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (0 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((57102032573 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (0 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 42308333200803720472837390881120000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (0 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((38579572411 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (0 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 42308384051202465744393787470816000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (0 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((192898093899 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (0 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 12524197531784826080720792252832000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (0 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((57102011473 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_1 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (1 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else -7) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 0) else if j.val = 1 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 1) else if j.val = 2 then (if k.val = 0 then (-37 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else 4) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 1) else if j.val = 4 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 6 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (1 : Fin 88)), (alphaG (n3 5) (m3 5) (1 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else -7) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 0) else if j.val = 1 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 1) else if j.val = 2 then (if k.val = 0 then (-37 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else 4) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 1) else if j.val = 4 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 6 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (252098199267464890142 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (1 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (1 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (1 : Fin 88) = 33285559326110922829449000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (1 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 407380955135381020676980401834057000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (1 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((12238969793 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (1 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 10783251910140597082810297791834000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (1 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((161980933 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (1 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 14139963294504670090255059131794671000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (1 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((424807741879 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (1 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2084651102658341983795084040977299000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (1 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((62629294651 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (1 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 2084650165203849123207053472375663000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (1 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((62629266487 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (1 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 14139964620102070252622560814601096000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (1 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((53100972713 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 5 (1 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 10785306594432238583965636849155000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 5) (m3 5) (1 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((64804719 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 5 (1 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 407380630002037523225486203776225000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 5) (m3 5) (1 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((489558401 : ℚ)/40000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_2 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (2 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 5) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else 6) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 5 else if k.val = 2 then -6 else 7) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 4 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 5 else if k.val = 2 then -6 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (2 : Fin 88)), (alphaG (n3 5) (m3 5) (2 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 5) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else 6) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 5 else if k.val = 2 then -6 else 7) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 4 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 5 else if k.val = 2 then -6 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (4722242343617961277019 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (2 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (2 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (2 : Fin 88) = 2064084546351540896980000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (2 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 361554484176729672818737022222960000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (2 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((43791142763 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (2 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 14531700696386504060912831183460000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (2 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((7040264277 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (2 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 655955935576910517967136097249420000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (2 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((317795090679 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (2 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 655955948062557938847606983081440000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (2 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((39724387091 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (2 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 14531758831327752052062194625160000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (2 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((3520146221 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (2 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 361554719007628511233544871637560000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (2 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((87582342411 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_3 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (3 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else -8) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 2) else if j.val = 4 then (if k.val = 0 then (27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (3 : Fin 88)), (alphaG (n3 5) (m3 5) (3 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else -8) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 2) else if j.val = 4 then (if k.val = 0 then (27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5561561476460675582552 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (3 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (3 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (3 : Fin 88) = 110215252636049914834000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (3 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 42191683871388103995221923900984000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (3 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((95702915119 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (3 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12937174988854806494265825535938000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (3 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((117380985657 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (3 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 12898442716366758836868842296180000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (3 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((11702956177 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (3 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 42187951059440245507643408266898000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (3 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((382777792097 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_4 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (4 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else -4) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 3 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else -5) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -2) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -2) else if j.val = 3 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else -6) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (4 : Fin 88)), (alphaG (n3 5) (m3 5) (4 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else -4) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 3 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else -5) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -2) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -2) else if j.val = 3 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else -6) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3205405117843025254686788 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (4 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (4 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (4 : Fin 88) = 30701327069123727845853000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (4 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 329484060584749239973038477450495000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (4 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((2146383183 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (4 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 46211287908433699041688954871889000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (4 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((1505188613 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (4 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 5017749395658261652469438165377518000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (4 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((81718770403 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (4 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 9602980326409646667170885626352838000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (4 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((156393570623 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (4 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 354239297081282684943803873168415000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (4 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((2307648111 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (4 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 354234637909289328865113442208841000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (4 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((11538088797 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 5 (4 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 9602989647946571394517134184240698000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 5) (m3 5) (4 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((156393722433 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 5 (4 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 5017749568783044995258139488142585000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 5) (m3 5) (4 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((32687509289 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 5 (4 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 46209913010903562473784834036990000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 5) (m3 5) (4 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((150514383 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 5 (4 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 329478933831544621139972954149731000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 5) (m3 5) (4 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((10731748927 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_5 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (5 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else -8) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 7) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 6) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 6) else if j.val = 4 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 4) else if j.val = 1 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 4 else if k.val = 2 then -2 else 7) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (5 : Fin 88)), (alphaG (n3 5) (m3 5) (5 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else -8) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 7) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 6) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 6) else if j.val = 4 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 4) else if j.val = 1 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 4 else if k.val = 2 then -2 else 7) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1382585751671183425131 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (5 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (5 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (5 : Fin 88) = 7796889544689964670160000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (5 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 1125526022731738803399441855483120000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (5 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((144355773707 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (5 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 279582900952196418066713153393760000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (5 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((17929130543 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (5 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 2562625572522202632872316339120000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (5 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((328672807 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (5 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 314416080177437436554036635767120000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (5 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((40325834857 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (5 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 4352713624084565511927190592214240000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (5 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((279131415107 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (5 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 314415925900384015773705707311200000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (5 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((4032581507 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 5 (5 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 2562486928232318955920551554000000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 5) (m3 5) (5 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((13146201 : ℚ)/40000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 5 (5 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 279583192930116087616510121545440000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 5) (m3 5) (5 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((17929149267 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 5 (5 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 1125526685412771875233609066392000000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 5) (m3 5) (5 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((1443558587 : ℚ)/10000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_6 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (6 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else -4) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 0) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -1) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (6 : Fin 88)), (alphaG (n3 5) (m3 5) (6 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else -4) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 0) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -1) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (868263290291869917777 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (6 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (6 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (6 : Fin 88) = 597406891670887806759000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (6 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 105061773919049433483872083818810000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (6 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((17586300959 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (6 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 189367254792205553327820182585376000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (6 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((9905688727 : ℚ)/31250000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (6 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 4274353978280466954966559169514000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (6 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((3577422723 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (6 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 4274578455712232966072612284041000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (6 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((7155221199 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (6 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 189367079665959701357084958025080000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (6 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((7924543653 : ℚ)/25000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (6 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 105061850859680418669183604117179000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (6 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((175863138381 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_7 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (7 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 3 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -2) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -2) else if j.val = 3 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (7 : Fin 88)), (alphaG (n3 5) (m3 5) (7 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 3 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -2) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -2) else if j.val = 3 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (864960456231012282390194 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (7 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (7 : Fin 88)))) =
        {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (7 : Fin 88) = 23220288856244040721521000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (7 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 38111805013924014685213294772934000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (7 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((820657427 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (7 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 256375447014328052689046308653519000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (7 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((11041010239 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (7 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 281623756958852036005928662802802000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (7 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((6064174281 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (7 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 7284396134449633209501687583562370000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (7 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((31370824797 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (7 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 3749637218461019229870620012430483000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (7 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((161481075523 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (7 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 3749637294762888411488537823348489000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (7 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((161481078809 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 5 (7 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 7284395716786297552240127125564143000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 5) (m3 5) (7 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((313708229983 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 5 (7 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 281624057499050702372547721449105000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 5) (m3 5) (7 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((2425672301 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 5 (7 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 256375560584760848578649477612730000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 5) (m3 5) (7 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((1104101513 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 5 (7 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 38111864713286664088641989803425000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 5) (m3 5) (7 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((65652697 : ℚ)/40000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_8 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (8 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else -3) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else -4) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else -4) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -1) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (8 : Fin 88)), (alphaG (n3 5) (m3 5) (8 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else -3) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else -4) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else -4) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -1) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (6227031166120161187286 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (8 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (8 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (8 : Fin 88) = 6036149056696759585700000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (8 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 1976978196786056949192343398700000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (8 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((327523091 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (8 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 76467953591610789055668736797000000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (8 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((1266833421 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (8 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 409205453732992690290238006457400000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (8 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((33896234991 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (8 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 2530424001387945560036430301224500000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (8 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((83842329857 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (8 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 2530424413506022406007691014892000000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (8 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((10480292939 : ℚ)/25000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (8 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 409205848261731185047141287395100000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (8 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((67792535343 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 5 (8 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 76467422796807339369417808681800000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 5) (m3 5) (8 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((6334123137 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 5 (8 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 1976985222863558944220501153500000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 5) (m3 5) (8 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((65504851 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_9 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (9 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 8 else if k.val = 2 then -1 else -6) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -8) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -8) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 8 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else -4) else if j.val = 2 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 8) else if j.val = 3 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else -4) else if j.val = 4 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (9 : Fin 88)), (alphaG (n3 5) (m3 5) (9 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 8 else if k.val = 2 then -1 else -6) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -8) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -8) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 8 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else -4) else if j.val = 2 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 8) else if j.val = 3 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else -4) else if j.val = 4 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2541633195185746718190 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (9 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (9 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (9 : Fin 88) = 10624643803450066610363000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (9 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 3506934541373175837298406133959000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (9 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((330075493 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (9 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 720210851078069859148350035431963000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (9 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((67786823201 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (9 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 4452955484194490130381495298651038000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (9 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((209557871613 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (9 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 135648748962800922423740106152211000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (9 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((12767369097 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (9 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 135648492271406631070130799782131000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (9 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((12767344937 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (9 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 4452955706972021401122491984742422000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (9 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((209557882097 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 5 (9 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 720210653969678017542714279977587000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 5) (m3 5) (9 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((67786804649 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 5 (9 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 3506931460226472836779089128689000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 5) (m3 5) (9 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((330075203 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_10 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (10 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -6) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -3) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (10 : Fin 88)), (alphaG (n3 5) (m3 5) (10 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -6) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -3) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (783043955527853839913 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (10 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (10 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (10 : Fin 88) = 2822221029727433653130000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (10 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 20753221177603835769183655989620000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (10 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((3676753337 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (10 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 499314293023019360280330421410240000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (10 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((5528826939 : ℚ)/31250000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (10 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 891042852200156361703838599696490000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (10 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((315723978673 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (10 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 891042858979131275109134234514750000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (10 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((12628959243 : ℚ)/40000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (10 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 499314597360046321967865840336920000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (10 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((44230642471 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (10 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 20753206987476498299647248051980000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (10 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((3676750823 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_11 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (11 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else 7) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else -4) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 5) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (11 : Fin 88)), (alphaG (n3 5) (m3 5) (11 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else 7) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else -4) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 5) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (10362846267679648008440 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (11 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (11 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (11 : Fin 88) = 3196772137838708738496000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (11 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 23554823548170989608071959957184000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (11 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((7368314829 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (11 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1008192758917227341084761745565504000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (11 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((315378361499 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (11 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 566638477870622848458233331615552000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (11 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((177253320987 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (11 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 566638497297407130104066335455744000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (11 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((22156665883 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (11 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1008192704623249352032132530949440000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (11 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((63075668903 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (11 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 23554875582031077208734096456576000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (11 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((3684165553 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_12 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (12 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 2) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 0) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (12 : Fin 88)), (alphaG (n3 5) (m3 5) (12 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 2) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 0) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (8711716392680412667740 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (12 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (12 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (12 : Fin 88) = 111396472849910118576000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (12 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 13247800909819426797568819130928000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (12 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((118924778953 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (12 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 42450435270063392220628920001872000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (12 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((381075218847 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (12 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 42450435218486825291120535101184000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (12 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((23817201149 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (12 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 13247801451540474266681725766016000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (12 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((14865597977 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_13 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (13 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -5 else if k.val = 2 then 0 else -8) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (13 : Fin 88)), (alphaG (n3 5) (m3 5) (13 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -5 else if k.val = 2 then 0 else -8) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1010045491358706211448 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (13 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (13 : Fin 88)))) =
        {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (13 : Fin 88) = 110335816335137266200000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (13 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 12881024512527182422444317649200000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (13 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((58371909233 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (13 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 42286804049515337937380315310000000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (13 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((7665109201 : ℚ)/20000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (13 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 42286967811147636527797319278200000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (13 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((383256944261 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (13 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 12881019961947109312378047762600000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (13 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((116743777223 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_14 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (14 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 7) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 3 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 0) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 3) else if j.val = 2 then (if k.val = 0 then (37 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -4) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 3) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (14 : Fin 88)), (alphaG (n3 5) (m3 5) (14 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 7) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 3 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 0) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 3) else if j.val = 2 then (if k.val = 0 then (37 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -4) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 3) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (15789371111066898193690 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (14 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (14 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (14 : Fin 88) = 38685693388272646917456000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (14 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 468422457342689487368971422129024000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (14 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((1513551963 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (14 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12598713478074872984906630621520000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (14 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((65133709 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (14 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 16598522067184970988058144339269408000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (14 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((214530497109 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (14 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2263302553670732748691670317566480000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (14 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((11700979641 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (14 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 2263301148026063485805044571802720000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (14 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((5850486187 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (14 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 16598523085508478047559029147463696000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (14 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((429061020541 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 5 (14 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 12600616466018335504681147199616000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 5) (m3 5) (14 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((40714717 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 5 (14 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 468422746595618951483552423947536000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 5) (m3 5) (14 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((12108423181 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_15 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (15 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else 7) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -3) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (15 : Fin 88)), (alphaG (n3 5) (m3 5) (15 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else 7) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -3) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3137353365751687808022 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (15 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (15 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (15 : Fin 88) = 2344077425845504430662000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (15 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 403851811775001995271623394541372000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (15 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((86143018853 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (15 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 15553153932826018213666801702744000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (15 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((1658771353 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (15 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 752633666644294920684031513041620000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (15 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((32107884251 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (15 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 752633781478303935429448066742338000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (15 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((321078891499 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (15 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 15553211454141971036500025717562000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (15 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((6635109951 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (15 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 403851800560935590026730198254364000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (15 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((86143016461 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    (((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (0 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (46 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -8) else if j.val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (0 : Fin 88)), (alphaG (n3 5) (m3 5) (0 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (46 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -8) else if j.val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1324353347151069108639 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (1 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else -7) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 0) else if j.val = 1 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 1) else if j.val = 2 then (if k.val = 0 then (-37 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else 4) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 1) else if j.val = 4 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 6 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (1 : Fin 88)), (alphaG (n3 5) (m3 5) (1 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else -7) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -1 else if k.val = 2 then -8 else 0) else if j.val = 1 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 1) else if j.val = 2 then (if k.val = 0 then (-37 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else 4) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 4 else if k.val = 2 then 6 else 1) else if j.val = 4 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 6 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (252098199267464890142 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (2 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 5) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else 6) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 5 else if k.val = 2 then -6 else 7) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 4 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 5 else if k.val = 2 then -6 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (2 : Fin 88)), (alphaG (n3 5) (m3 5) (2 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 5) else if j.val = 1 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else 6) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 5 else if k.val = 2 then -6 else 7) else if j.val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 3 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 4) else if j.val = 4 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 5 else if k.val = 2 then -6 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (4722242343617961277019 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (3 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else -8) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 2) else if j.val = 4 then (if k.val = 0 then (27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (3 : Fin 88)), (alphaG (n3 5) (m3 5) (3 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else -8) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 2) else if j.val = 4 then (if k.val = 0 then (27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5561561476460675582552 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (4 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else -4) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 3 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else -5) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -2) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -2) else if j.val = 3 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else -6) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (4 : Fin 88)), (alphaG (n3 5) (m3 5) (4 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else -4) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 3 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else -5) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -2) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -2) else if j.val = 3 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else -6) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3205405117843025254686788 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (5 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else -8) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 7) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 6) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 6) else if j.val = 4 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 4) else if j.val = 1 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 4 else if k.val = 2 then -2 else 7) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (5 : Fin 88)), (alphaG (n3 5) (m3 5) (5 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else -8) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 7) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 6) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 6) else if j.val = 4 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 4) else if j.val = 1 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 4 else if k.val = 2 then -2 else 7) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1382585751671183425131 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (6 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else -4) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 0) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -1) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (6 : Fin 88)), (alphaG (n3 5) (m3 5) (6 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else -4) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 0) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -1) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (868263290291869917777 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (7 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 3 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -2) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -2) else if j.val = 3 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (7 : Fin 88)), (alphaG (n3 5) (m3 5) (7 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 3 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -2) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -2) else if j.val = 3 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (864960456231012282390194 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (8 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else -3) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else -4) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else -4) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -1) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (8 : Fin 88)), (alphaG (n3 5) (m3 5) (8 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else -3) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else -4) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else -4) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -1) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (6227031166120161187286 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (9 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 8 else if k.val = 2 then -1 else -6) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -8) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -8) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 8 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else -4) else if j.val = 2 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 8) else if j.val = 3 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else -4) else if j.val = 4 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (9 : Fin 88)), (alphaG (n3 5) (m3 5) (9 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 8 else if k.val = 2 then -1 else -6) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -8) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -8) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 8 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else -4) else if j.val = 2 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 8) else if j.val = 3 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else -4) else if j.val = 4 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2541633195185746718190 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (10 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -6) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -3) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (10 : Fin 88)), (alphaG (n3 5) (m3 5) (10 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -6) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -3) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (783043955527853839913 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (11 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else 7) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else -4) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 5) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (11 : Fin 88)), (alphaG (n3 5) (m3 5) (11 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else 7) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else -4) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 5) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (10362846267679648008440 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (12 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 2) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 0) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (12 : Fin 88)), (alphaG (n3 5) (m3 5) (12 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 2) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 0) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (8711716392680412667740 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (13 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -5 else if k.val = 2 then 0 else -8) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (13 : Fin 88)), (alphaG (n3 5) (m3 5) (13 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -5 else if k.val = 2 then 0 else -8) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1010045491358706211448 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (14 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 7) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 3 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 0) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 3) else if j.val = 2 then (if k.val = 0 then (37 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -4) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 3) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (14 : Fin 88)), (alphaG (n3 5) (m3 5) (14 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 7) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 3 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 0) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 3) else if j.val = 2 then (if k.val = 0 then (37 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -4) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 3) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (15789371111066898193690 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (15 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else 7) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -3) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (15 : Fin 88)), (alphaG (n3 5) (m3 5) (15 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else 7) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -3) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3137353365751687808022 : ℚ)/10^30) :=
  ⟨L3C.pn_5_0, L3C.pn_5_1, L3C.pn_5_2, L3C.pn_5_3, L3C.pn_5_4, L3C.pn_5_5, L3C.pn_5_6, L3C.pn_5_7, L3C.pn_5_8, L3C.pn_5_9, L3C.pn_5_10, L3C.pn_5_11, L3C.pn_5_12, L3C.pn_5_13, L3C.pn_5_14, L3C.pn_5_15⟩

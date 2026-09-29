-- Prove2me | solution 1 for mme_released_recursive_level3_penalty20
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T08:49:31.457644+00:00
-- url     : https://prove2.me/submissions/96ce399e-edba-49aa-a4a2-54aa7c34aaec

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

theorem pn_3_16 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (16 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else -7) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else -3) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -7) else if j.val = 2 then (if k.val = 0 then (-37 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else 4) else if j.val = 3 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -7) else if j.val = 4 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (16 : Fin 88)), (alphaG (n3 3) (m3 3) (16 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else -7) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else -3) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -7) else if j.val = 2 then (if k.val = 0 then (-37 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else 4) else if j.val = 3 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -7) else if j.val = 4 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (89926478834341366425 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (16 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (16 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (16 : Fin 88) = 33339339783860258325681000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (16 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 408035279665218988138123117012068000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (16 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((3059713257 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (16 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 10801584124758690326696002081383000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (16 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((323989143 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (16 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 14162882163882684455357724945725244000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (16 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((106202479231 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (16 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2087951095299091731169546132150635000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (16 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((12525449567 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (16 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 2087950289353891796131661367138141000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (16 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((62627223661 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (16 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 14162881379641394719612868350731081000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (16 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((424809893401 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 3 (16 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 10801686876603904184012161830225000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 3) (m3 3) (16 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((12959689 : ℚ)/40000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 3 (16 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 408036305016614040760367923331223000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 3) (m3 3) (16 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((12238883783 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_17 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (17 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else -1) else if j.val = 3 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -6 else if k.val = 2 then -4 else 3) else if j.val = 4 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (17 : Fin 88)), (alphaG (n3 3) (m3 3) (17 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else -1) else if j.val = 3 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -6 else if k.val = 2 then -4 else 3) else if j.val = 4 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (13735533926319930892115 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (17 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (17 : Fin 88)))) =
        {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (17 : Fin 88) = 109599799194566392880000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (17 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 12511948826738998084376192705840000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (17 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((114160326193 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (17 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 42245430285365743858733983249200000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (17 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((77090342493 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (17 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 42236863943031136911358637480320000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (17 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((48171694033 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (17 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 12605556139430514025531186564640000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (17 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((57507204539 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_18 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (18 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else -3) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -1) else if j.val = 2 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (18 : Fin 88)), (alphaG (n3 3) (m3 3) (18 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else -3) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -1) else if j.val = 2 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3473522521529815763284 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (18 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (18 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (18 : Fin 88) = 529049551400317061884000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (18 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 93022419190012216337656790538664000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (18 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((87914656523 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (18 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 167709599798954746224610823641968000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (18 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((79250421513 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (18 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 3792785522172038538198941898240000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (18 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((11201649 : ℚ)/1562500000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (18 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 3792700110825311816811520159628000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (18 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((7168893917 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (18 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 167709661880274355294816450419948000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (18 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((317001803397 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (18 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 93022384898078393671905473341552000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (18 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((43957312057 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_19 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (19 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else -3) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 5 else -3) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 8) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 6) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 6) else if j.val = 4 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -1 else -1) else if j.val = 1 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -8) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -1 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (19 : Fin 88)), (alphaG (n3 3) (m3 3) (19 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else -3) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 5 else -3) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 8) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 6) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 6) else if j.val = 4 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -1 else -1) else if j.val = 1 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -8) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -1 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5207128527507821569307 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (19 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (19 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (19 : Fin 88) = 7164376588717888573347000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (19 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 1034227387594756501158330718787811000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (19 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((144356926913 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (19 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 257188886541056378706365524331175000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (19 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((1435931701 : ℚ)/40000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (19 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 2355345889293664772623978678896000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (19 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((20547373 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (19 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 288625341083802060097281935241348000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (19 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((10071544171 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (19 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 3999582627138986385461715863953122000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (19 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((279129843163 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (19 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 288625390532329275428148868482342000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (19 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((20143091793 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 3 (19 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 2355362904688062977609340378021000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 3) (m3 3) (19 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((328760343 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 3 (19 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 257188907418049758230292827064333000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 3) (m3 3) (19 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((35898295439 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 3 (19 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 1034227339614926486514630943082952000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 3) (m3 3) (19 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((18044615027 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_20 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (20 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else 8) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -2) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -2) else if j.val = 3 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else -6) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (20 : Fin 88)), (alphaG (n3 3) (m3 3) (20 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else 8) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -2) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -2) else if j.val = 3 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else -6) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3211133297798025253301163 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (20 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (20 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (20 : Fin 88) = 31109205273370554580928000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (20 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 333717969890588923765904580792256000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (20 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((10727306177 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (20 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 46795445827767583358948996051584000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (20 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((752115739 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (20 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 5084688091234988391686750700231424000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (20 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((40861603877 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (20 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 9730488505550326598384897015667072000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (20 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((156392431437 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (20 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 358908941411667121114506307839168000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (20 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((11537065581 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (20 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 358927690991903792094493342306624000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (20 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((11537668283 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 3 (20 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 9730452271165702850578189988940928000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 3) (m3 3) (20 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((156391849063 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 3 (20 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 5084687978495228480991860898948352000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 3) (m3 3) (20 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((40861602971 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 3 (20 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 46800824764905375494688811407424000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 3) (m3 3) (20 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((1504404383 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 3 (20 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 333737554037475463457759357815168000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 3) (m3 3) (20 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((5363967853 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_21 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (21 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -4 else if k.val = 2 then 5 else 4) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 3 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -4 else if k.val = 2 then 5 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -2) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -2) else if j.val = 3 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (21 : Fin 88)), (alphaG (n3 3) (m3 3) (21 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -4 else if k.val = 2 then 5 else 4) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 3 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -4 else if k.val = 2 then 5 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -2) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -2) else if j.val = 3 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (865396450223593837617905 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (21 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (21 : Fin 88)))) =
        {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (21 : Fin 88) = 22483508635258846272548000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (21 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 36898368395810372723862894631800000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (21 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((32822607 : ℚ)/20000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (21 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 248196935871093382898064437803288000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (21 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((5519533003 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (21 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 272716429007876398104036817292744000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (21 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((6064810289 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (21 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 7053221028210151617616544029686308000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (21 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((313706421121 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (21 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 3630721610262296649999534798608896000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (21 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((1261591909 : ℚ)/7812500000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (21 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 3630721416656803791785609545698068000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (21 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((161483755741 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 3 (21 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 7053220958960945021019297510238468000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 3) (m3 3) (21 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((313706418041 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 3 (21 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 272716272162920158538325219997896000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 3) (m3 3) (21 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((6064806801 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 3 (21 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 248197224941563906421050963952924000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 3) (m3 3) (21 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((11039078863 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 3 (21 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 36898390789384973441673782089608000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 3) (m3 3) (21 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((820565673 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_22 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (22 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 8 else if k.val = 2 then -1 else -6) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -8) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -8) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 8 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else -4) else if j.val = 2 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 8) else if j.val = 3 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else -4) else if j.val = 4 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (22 : Fin 88)), (alphaG (n3 3) (m3 3) (22 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 8 else if k.val = 2 then -1 else -6) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -8) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -8) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 8 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else -4) else if j.val = 2 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 8) else if j.val = 3 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else -4) else if j.val = 4 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1735880245107569646120 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (22 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (22 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (22 : Fin 88) = 10521294106958200123520000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (22 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 3473113157965573228802150846080000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (22 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((330103229 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (22 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 713206453566558500546466451873920000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (22 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((67786951521 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (22 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 4409621910760046006603140443368320000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (22 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((419114023991 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (22 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 134345466267953739914521865721600000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (22 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((1276891083 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (22 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 134345654883193195354175480064640000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (22 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((12768928757 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (22 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 4409621823517475271705745019140480000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (22 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((419114015699 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 3 (22 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 713206574361536142533562070007040000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 3) (m3 3) (22 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((33893481501 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 3 (22 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 3473110443471693633586518977920000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 3) (m3 3) (22 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((330102971 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_23 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (23 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else -3) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else -4) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else -4) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -1) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (23 : Fin 88)), (alphaG (n3 3) (m3 3) (23 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else -3) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else -4) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else -4) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -1) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (6064377769175666102842 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (23 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (23 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (23 : Fin 88) = 5885273584830393740685000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (23 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 1927628699078602315211924664675000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (23 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((65506851 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (23 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 74560962589787139574189694468310000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (23 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((6334536663 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (23 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 398979714796589287239598451258610000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (23 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((33896445853 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (23 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 2467168609255451207565933991296000000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (23 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((16375411 : ℚ)/39062500) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (23 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 2467168212440879750376636025609875000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (23 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((16768418167 : ℚ)/40000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (23 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 398979342735478527846936558893595000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (23 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((67792828487 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 3 (23 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 74561502328227604369599652689660000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 3) (m3 3) (23 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((3167291259 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 3 (23 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 1927611984901621396893701119275000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 3) (m3 3) (23 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((65506283 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_24 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (24 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else 7) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else -4) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 3 else if k.val = 2 then -4 else 4) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (24 : Fin 88)), (alphaG (n3 3) (m3 3) (24 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else 7) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else -4) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 3 else if k.val = 2 then -4 else 4) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (8842032238649816369841 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (24 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (24 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (24 : Fin 88) = 3146725697841622797835000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (24 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 23177285766615615563812983482955000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (24 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((7365524673 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (24 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 992421027757858453127806806393405000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (24 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((315382121943 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (24 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 557764534710351128096406440195610000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (24 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((88626176583 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (24 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 557764545289642924239942286516880000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (24 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((11078272283 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (24 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 992420990522653270567884239611850000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (24 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((31538211011 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (24 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 23177313794501406239147243799300000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (24 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((368276679 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_25 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (25 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -6) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -3) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (25 : Fin 88)), (alphaG (n3 3) (m3 3) (25 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -6) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -3) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (724906566450534625884 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (25 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (25 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (25 : Fin 88) = 2840772159474113391315000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (25 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 20891213421089159730900167699535000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (25 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((7354061589 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (25 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 502596086459066640042684987468105000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (25 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((176922350067 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (25 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 896898765525205351337012785648185000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (25 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((315723583299 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (25 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 896898910890357523786869132628050000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (25 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((31572363447 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (25 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 502596134882868870438421855823595000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (25 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((176922367113 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (25 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 20891048295525845979111070732530000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (25 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((3677001731 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_26 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (26 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -1 else -6) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 0) else if j.val = 4 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (26 : Fin 88)), (alphaG (n3 3) (m3 3) (26 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -1 else -6) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 0) else if j.val = 4 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (745348563627313524536 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (26 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (26 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (26 : Fin 88) = 111393274900139108910000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (26 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 13251853575608672659918469190840000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (26 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((29741143681 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (26 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 42444783865326633253270123878540000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (26 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((190517712597 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (26 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 42444783864769666878769428333990000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (26 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((381035425189 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (26 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 13251853594434136118041978596630000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (26 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((118964574893 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_27 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (27 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -4) else if j.val = 3 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -1) else if j.val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (27 : Fin 88)), (alphaG (n3 3) (m3 3) (27 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -4) else if j.val = 3 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -1) else if j.val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1849891479629902482774 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (27 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (27 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (27 : Fin 88) = 109696006936286759600000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (27 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 42313077340029773087632620676800000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (27 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((96432583377 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (27 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12534904604550389736605991447600000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (27 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((114269470281 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (27 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 12534922139018314474299366469200000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (27 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((114269630127 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (27 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 42313102852688282301462021406400000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (27 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((96432641521 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_28 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (28 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 0) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -2) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 4 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (28 : Fin 88)), (alphaG (n3 3) (m3 3) (28 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 0) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -2) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 4 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (4780761329636999305253 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (28 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (28 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (28 : Fin 88) = 2348564872837052434686000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (28 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 404575380031133084643985232514078000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (28 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((172264937073 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (28 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 15585569375365153031748448942704000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (28 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((829526233 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (28 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 754121636150594534565770025973590000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (28 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((64219783313 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (28 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 754121325355610652547273134236466000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (28 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((321098784231 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (28 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 15585478709018237157339207889674000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (28 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((6636171259 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (28 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 404575483215330772739883950443488000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (28 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((10766561313 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_29 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (29 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else 6) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 3 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else -4) else if j.val = 1 then (if k.val = 0 then (24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 8 else -4) else if j.val = 3 then (if k.val = 0 then (24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -3 else if k.val = 2 then 4 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (29 : Fin 88)), (alphaG (n3 3) (m3 3) (29 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else 6) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 3 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else -4) else if j.val = 1 then (if k.val = 0 then (24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 8 else -4) else if j.val = 3 then (if k.val = 0 then (24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -3 else if k.val = 2 then 4 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2517584651714917991896 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (29 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (29 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (29 : Fin 88) = 38322531645240821519332000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (29 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 467774355601102550219433829646944000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (29 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((1525781099 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (29 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12578365467642460189804883247652000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (29 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((328223761 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (29 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 16442369777959630936680510293950368000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (29 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((53631535653 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (29 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2238543510567666709706219185975864000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (29 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((29206623551 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (29 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 2238543554293675316925996539533676000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (29 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((58413248243 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (29 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 16442369456816815749562425961948208000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (29 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((107263069211 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 3 (29 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 12578098053016639699352321348956000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 3) (m3 3) (29 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((328216783 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 3 (29 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 467774526481271156348256984348332000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 3) (m3 3) (29 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((12206253251 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_30 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (30 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 3 then (if k.val = 0 then (35 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -8) else if j.val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (30 : Fin 88)), (alphaG (n3 3) (m3 3) (30 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 3 then (if k.val = 0 then (35 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -8) else if j.val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5609123342259148525262 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (30 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (30 : Fin 88)))) =
        {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (30 : Fin 88) = 110787618363508759365000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (30 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 13134741190028735264502891574275000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (30 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((23711568827 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (30 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 42257501804890858432827366919125000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (30 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((15257120761 : ℚ)/40000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (30 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 42257174396347273504297481962560000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (30 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((5959766621 : ℚ)/15625000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (30 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 13138200972241892163372259544040000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (30 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((14823634137 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_3_31 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (31 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else -2) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 3 else if k.val = 2 then -4 else 5) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else -1) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else 4) else if j.val = 1 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else 0) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (31 : Fin 88)), (alphaG (n3 3) (m3 3) (31 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else -2) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 3 else if k.val = 2 then -4 else 5) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else -1) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else 4) else if j.val = 1 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else 0) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5228722975500714892444 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (31 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (31 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 3 (31 : Fin 88) = 746782730372678154442000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 3 (31 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 109141874733794266108981942920186000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 3) (m3 3) (31 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((146149435833 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 3 (31 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 25402349905573697808052319902142000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 3) (m3 3) (31 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((34015716851 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 3 (31 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 238157773970839795711661713544000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 3) (m3 3) (31 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((79727933 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 3 (31 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 28192109977194839288831484508508000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 3) (m3 3) (31 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((18875710987 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 3 (31 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 420833747176283822289668225637164000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 3) (m3 3) (31 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((281764514671 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 3 (31 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 28192110428251608433929089791476000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 3) (m3 3) (31 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((18875711289 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 3 (31 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 238159025578695900320248558336000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 3) (m3 3) (31 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((2491511 : ℚ)/7812500000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 3 (31 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 25402343723706255783022557431266000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 3) (m3 3) (31 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((34015708573 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 3 (31 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 109141877628324129033482469537378000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 3) (m3 3) (31 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((146149439709 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    (((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (16 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else -7) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else -3) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -7) else if j.val = 2 then (if k.val = 0 then (-37 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else 4) else if j.val = 3 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -7) else if j.val = 4 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (16 : Fin 88)), (alphaG (n3 3) (m3 3) (16 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else -7) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else -3) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -7) else if j.val = 2 then (if k.val = 0 then (-37 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else 4) else if j.val = 3 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 4 else if k.val = 2 then -5 else -7) else if j.val = 4 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (89926478834341366425 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (17 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else -1) else if j.val = 3 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -6 else if k.val = 2 then -4 else 3) else if j.val = 4 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (17 : Fin 88)), (alphaG (n3 3) (m3 3) (17 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else -1) else if j.val = 3 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -6 else if k.val = 2 then -4 else 3) else if j.val = 4 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (13735533926319930892115 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (18 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else -3) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -1) else if j.val = 2 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (18 : Fin 88)), (alphaG (n3 3) (m3 3) (18 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else -3) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -1) else if j.val = 2 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3473522521529815763284 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (19 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else -3) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 5 else -3) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 8) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 6) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 6) else if j.val = 4 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -1 else -1) else if j.val = 1 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -8) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -1 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (19 : Fin 88)), (alphaG (n3 3) (m3 3) (19 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else -3) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 5 else -3) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -7 else if k.val = 2 then 3 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 8) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 6) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 6) else if j.val = 4 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -1 else -1) else if j.val = 1 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -8) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -1 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5207128527507821569307 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (20 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else 8) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -2) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -2) else if j.val = 3 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else -6) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (20 : Fin 88)), (alphaG (n3 3) (m3 3) (20 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else 8) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -2) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -2) else if j.val = 3 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else -6) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3211133297798025253301163 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (21 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -4 else if k.val = 2 then 5 else 4) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 3 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -4 else if k.val = 2 then 5 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -2) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -2) else if j.val = 3 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (21 : Fin 88)), (alphaG (n3 3) (m3 3) (21 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -4 else if k.val = 2 then 5 else 4) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 3 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -4 else if k.val = 2 then 5 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -2) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -2) else if j.val = 3 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (865396450223593837617905 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (22 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 8 else if k.val = 2 then -1 else -6) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -8) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -8) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 8 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else -4) else if j.val = 2 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 8) else if j.val = 3 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else -4) else if j.val = 4 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (22 : Fin 88)), (alphaG (n3 3) (m3 3) (22 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 8 else if k.val = 2 then -1 else -6) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -8) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -8) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 8 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else -4) else if j.val = 2 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 8) else if j.val = 3 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else -4) else if j.val = 4 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1735880245107569646120 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (23 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else -3) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else -4) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else -4) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -1) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (23 : Fin 88)), (alphaG (n3 3) (m3 3) (23 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else -3) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else -4) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else -4) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -1) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (6064377769175666102842 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (24 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else 7) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else -4) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 3 else if k.val = 2 then -4 else 4) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (24 : Fin 88)), (alphaG (n3 3) (m3 3) (24 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else 7) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else -4) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 3 else if k.val = 2 then -4 else 4) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (8842032238649816369841 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (25 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -6) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -3) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (25 : Fin 88)), (alphaG (n3 3) (m3 3) (25 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -6) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -3) else if j.val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (724906566450534625884 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (26 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -1 else -6) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 0) else if j.val = 4 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (26 : Fin 88)), (alphaG (n3 3) (m3 3) (26 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -1 else -6) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 0) else if j.val = 4 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (745348563627313524536 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (27 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -4) else if j.val = 3 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -1) else if j.val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (27 : Fin 88)), (alphaG (n3 3) (m3 3) (27 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -4) else if j.val = 3 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -1) else if j.val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1849891479629902482774 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (28 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 0) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -2) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 4 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (28 : Fin 88)), (alphaG (n3 3) (m3 3) (28 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 0) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -2) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 4 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (4780761329636999305253 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (29 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else 6) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 3 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else -4) else if j.val = 1 then (if k.val = 0 then (24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 8 else -4) else if j.val = 3 then (if k.val = 0 then (24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -3 else if k.val = 2 then 4 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (29 : Fin 88)), (alphaG (n3 3) (m3 3) (29 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else 6) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 3 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else -4) else if j.val = 1 then (if k.val = 0 then (24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 8 else -4) else if j.val = 3 then (if k.val = 0 then (24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -3 else if k.val = 2 then 4 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2517584651714917991896 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (30 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 3 then (if k.val = 0 then (35 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -8) else if j.val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (30 : Fin 88)), (alphaG (n3 3) (m3 3) (30 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 3 then (if k.val = 0 then (35 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -8) else if j.val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5609123342259148525262 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (31 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else -2) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 3 else if k.val = 2 then -4 else 5) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else -1) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else 4) else if j.val = 1 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else 0) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (31 : Fin 88)), (alphaG (n3 3) (m3 3) (31 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else -2) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 3 else if k.val = 2 then -4 else 5) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else -1) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else 4) else if j.val = 1 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else 0) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5228722975500714892444 : ℚ)/10^30) :=
  ⟨L3C.pn_3_16, L3C.pn_3_17, L3C.pn_3_18, L3C.pn_3_19, L3C.pn_3_20, L3C.pn_3_21, L3C.pn_3_22, L3C.pn_3_23, L3C.pn_3_24, L3C.pn_3_25, L3C.pn_3_26, L3C.pn_3_27, L3C.pn_3_28, L3C.pn_3_29, L3C.pn_3_30, L3C.pn_3_31⟩

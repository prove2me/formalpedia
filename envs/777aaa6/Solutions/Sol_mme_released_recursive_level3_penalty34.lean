-- Prove2me | solution 1 for mme_released_recursive_level3_penalty34
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T09:53:37.469564+00:00
-- url     : https://prove2.me/submissions/3d0cd520-b46d-4df9-a496-b6ab9af2d8a8

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

theorem pn_5_48 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (48 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 8) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else -1) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 4 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else 1) else if j.val = 1 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -8) else if j.val = 2 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (48 : Fin 88)), (alphaG (n3 5) (m3 5) (48 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 8) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else -1) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 4 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else 1) else if j.val = 1 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -8) else if j.val = 2 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (26610939119659347745850 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (48 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (48 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (48 : Fin 88) = 8429254993169915859441000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (48 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 1206049798501802658232473131845902000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (48 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((71539525111 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (48 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 313253693061244884154529512794711000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (48 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((37162678471 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (48 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 2829850672209859397079334247688000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (48 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((41964721 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (48 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 354227089717482732101639017821582000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (48 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((21011767351 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (48 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 4676534331364253307911460652537650000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (48 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((11095961233 : ℚ)/20000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (48 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 354227008004284828312474676400528000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (48 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((2626470313 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 5 (48 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 2829738209089740524061937585866000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 5) (m3 5) (48 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((167852213 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 5 (48 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 313253795451405286189497457424538000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 5) (m3 5) (48 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((18581345309 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 5 (48 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 1206049688188142562617784279341535000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 5) (m3 5) (48 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((28615807427 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_49 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (49 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -5) else if j.val = 2 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else 4) else if j.val = 2 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (49 : Fin 88)), (alphaG (n3 5) (m3 5) (49 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -5) else if j.val = 2 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else 4) else if j.val = 2 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (952399425185747065234 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (49 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (49 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (49 : Fin 88) = 1017811243177689751232000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (49 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 180200139560832773964335070115136000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (49 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((177046717423 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (49 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 321246374950231205996364811218368000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (49 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((315624706549 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (49 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 7459043127682675557875359008704000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (49 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((7328513197 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (49 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 7459402419122762255068302909632000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (49 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((7328866201 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (49 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 321246042579898501349065787403840000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (49 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((63124875999 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (49 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 180200240539921832109290669344320000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (49 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((35409363327 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_50 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (50 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else 0) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -2) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 2) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 2) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (50 : Fin 88)), (alphaG (n3 5) (m3 5) (50 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else 0) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -2) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 2) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 2) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (808668111586379131516474 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (50 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (50 : Fin 88)))) =
        {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (50 : Fin 88) = 32436682289619259119210000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (50 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 52747118467594329490342445324790000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (50 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((1626156399 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (50 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 360453159104354587854420330400920000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (50 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((2778129063 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (50 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 387531292202837610536028730306860000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (50 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((5973657983 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (50 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 10178575510846727763143589011871150000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (50 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((62759658463 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (50 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 5239033905021315273418914984132810000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (50 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((161515714161 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (50 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 5239034043688132061541247718755560000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (50 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((40378929609 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 5 (50 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 10178574763408257763447001127915120000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 5) (m3 5) (50 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((39224783659 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 5 (50 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 387531829516479738079056040020510000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 5) (m3 5) (50 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((11947332531 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 5 (50 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 360453431734669232104293227360970000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 5) (m3 5) (50 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((11112524657 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 5 (50 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 52747235628890759595106383911310000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 5) (m3 5) (50 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((1626160011 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_51 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (51 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 1) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 1) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 1) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -6) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -7) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 6) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -7) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (51 : Fin 88)), (alphaG (n3 5) (m3 5) (51 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 1) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 1) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 1) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -6) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -7) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 6) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -7) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3129956813746275439141 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (51 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (51 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (51 : Fin 88) = 771035885974560881320000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (51 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 249381799859334708995000895400000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (51 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((64687469 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (51 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 9287191669696002533959277811280000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (51 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((6022541777 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (51 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 47460638304499822027197548404080000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (51 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((30777191547 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (51 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 328520722003972659309693006403160000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (51 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((426077084063 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (51 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 328520742801123611701523658247520000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (51 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((106519277759 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (51 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 47460658996018858040513359507600000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (51 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((6155440993 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 5 (51 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 9287169185518531629789417638760000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 5) (m3 5) (51 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((12045054393 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 5 (51 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 249381213872061368328731092200000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 5) (m3 5) (51 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((64687317 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_52 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (52 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -1) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 8) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 5) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -8 else if k.val = 2 then 1 else 8) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else -6) else if j.val = 4 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (52 : Fin 88)), (alphaG (n3 5) (m3 5) (52 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -1) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 8) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 5) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -8 else if k.val = 2 then 1 else 8) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else -6) else if j.val = 4 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5700984369205773901574 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (52 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (52 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (52 : Fin 88) = 35078003847440647647750000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (52 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 11215249955971850998860015708000000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (52 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((19982697 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (52 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1273317551185565219536974734959500000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (52 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((18149800609 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (52 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 5146943387671373925191640036619500000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (52 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((73364257129 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (52 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 1286427169867352032788983054928000000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (52 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((573020763 : ℚ)/15625000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (52 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 19642197008885618297809646692593750000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (52 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((4479661293 : ℚ)/8000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (52 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 1286428507005780693379030739510250000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (52 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((36673366951 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 5 (52 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 5146943379533277032585409782341500000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 5) (m3 5) (52 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((73364257013 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 5 (52 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 1273318876888564625861371286375250000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 5) (m3 5) (52 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((36299639011 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 5 (52 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 11212716447143969598083656964250000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 5) (m3 5) (52 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((319650927 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_53 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (53 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else -5) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else -1) else if j.val = 1 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 4 else if k.val = 2 then 4 else 3) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -8) else if j.val = 3 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 4 else if k.val = 2 then 4 else 3) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (53 : Fin 88)), (alphaG (n3 5) (m3 5) (53 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else -5) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else -1) else if j.val = 1 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 4 else if k.val = 2 then 4 else 3) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -8) else if j.val = 3 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 4 else if k.val = 2 then 4 else 3) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (14765248875875496192487 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (53 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (53 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (53 : Fin 88) = 7148700823204087157112000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (53 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 2346024570963464258601308529960000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (53 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((65634991 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (53 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 438679728622815862282948056983688000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (53 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((61364958399 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (53 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 3045786105004216426421171579834712000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (53 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((426061487301 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (53 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 87538673866805397405351739145952000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (53 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((3061349049 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (53 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 87538482167244122364550534030560000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (53 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((612268469 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (53 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 3045786218797236130183830946743528000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (53 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((426061503219 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 5 (53 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 438679575797889663825972812243352000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 5) (m3 5) (53 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((61364937021 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 5 (53 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2346014376916090369573022488248000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 5) (m3 5) (53 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((328173529 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_54 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (54 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else if j.val = 1 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else -8) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else -6) else if j.val = 2 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 4 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (54 : Fin 88)), (alphaG (n3 5) (m3 5) (54 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else if j.val = 1 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else -8) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else -6) else if j.val = 2 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 4 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2184449449248143599425 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (54 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (54 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (54 : Fin 88) = 3461797411253924839028000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (54 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 22877638771957197394938911204588000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (54 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((6608601271 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (54 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 597071833020306221590509684321196000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (54 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((172474516007 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (54 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 1110949286377860108540622611241200000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (54 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((3209168979 : ℚ)/10000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (54 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1110949090637449084009950438080996000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (54 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((320916841357 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (54 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 597071717828997362116160665664496000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (54 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((43118620683 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (54 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 22877844617354865375817689487524000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (54 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((6608660733 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_55 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (55 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 5) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 5 else if k.val = 2 then -2 else -2) else if j.val = 2 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 4 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (55 : Fin 88)), (alphaG (n3 5) (m3 5) (55 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 5) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 5 else if k.val = 2 then -2 else -2) else if j.val = 2 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 4 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (4552097907405688851147 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (55 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (55 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (55 : Fin 88) = 3868304141858839720803000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (55 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 25480754834492379762926647116201000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (55 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((6587060867 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (55 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1239975064905767915637513054547836000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (55 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((80136864853 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (55 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 668696167784653962382617078102480000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (55 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((2160818227 : ℚ)/12500000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (55 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 668696422879970597263802466456315000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (55 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((34573104821 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (55 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1239974385306623057309115544993584000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (55 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((20034205233 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (55 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 25481346147331808447025208783584000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (55 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((205850429 : ℚ)/31250000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_56 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (56 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else -1) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (56 : Fin 88)), (alphaG (n3 5) (m3 5) (56 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else -1) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (550582123745306811964 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (56 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (56 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (56 : Fin 88) = 109592786278022729400000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (56 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 12571846330145168689964477442000000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (56 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((11471417743 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (56 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 42224778361546312385247244430400000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (56 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((48160991927 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (56 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 42224778274639232866775220016200000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (56 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((385287934623 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (56 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 12571383311692015458013058111400000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (56 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((114709952531 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_57 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (57 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (57 : Fin 88)), (alphaG (n3 5) (m3 5) (57 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2077630512182625889118 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (57 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (57 : Fin 88)))) =
        {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (57 : Fin 88) = 110788500636063901022000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (57 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 13129884041277161221237421841876000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (57 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((59256529179 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (57 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 42264392777807295438791958224612000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (57 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((190743590423 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (57 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 42264352201518937480388208917112000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (57 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((95371703649 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (57 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 13129871615460506881582411016400000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (57 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((592564731 : ℚ)/5000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_58 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (58 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 4 else if k.val = 2 then -7 else -3) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 3 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 4 else if k.val = 2 then -7 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else 8) else if j.val = 1 then (if k.val = 0 then (24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 8 else -4) else if j.val = 3 then (if k.val = 0 then (24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (58 : Fin 88)), (alphaG (n3 5) (m3 5) (58 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 4 else if k.val = 2 then -7 else -3) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 3 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 4 else if k.val = 2 then -7 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else 8) else if j.val = 1 then (if k.val = 0 then (24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 8 else -4) else if j.val = 3 then (if k.val = 0 then (24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (487191028431954900188 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (58 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (58 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (58 : Fin 88) = 37987377121623153187820000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (58 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 463546391910728507114621651741540000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (58 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((12202642747 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (58 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12467285354409997774720655490140000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (58 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((328195477 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (58 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 16298442866198005794096564762634940000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (58 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((429048913117 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (58 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2219231107702699740536066694595660000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (58 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((58420224713 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (58 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 2219229308316620243490546493937900000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (58 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((11684035469 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (58 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 16298444007110890264926347605620820000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (58 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((429048943151 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 5 (58 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 12469461689232672686789938885760000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 5) (m3 5) (58 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((10257899 : ℚ)/31250000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 5 (58 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 463546693340565967194342197093240000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 5) (m3 5) (58 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((6101325341 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_59 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (59 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 0) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 1) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 4 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (59 : Fin 88)), (alphaG (n3 5) (m3 5) (59 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 0) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 1) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 4 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5204548619398910931713 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (59 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (59 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (59 : Fin 88) = 2358405063333493340540000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (59 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 406268770373979791520718641749320000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (59 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((86132101879 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (59 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 15654534976858098523324682073800000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (59 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((663776347 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (59 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 757279155403385335914478912820160000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (59 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((20068625169 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (59 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 757279250315038704707584909511920000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (59 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((80274510737 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (59 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 15654605344589973204765483765780000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (59 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((6637793307 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (59 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 406268746919641436669127370079020000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (59 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((172264193813 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_60 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (60 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 5) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -8 else if k.val = 2 then 1 else 4) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 2) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (60 : Fin 88)), (alphaG (n3 5) (m3 5) (60 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 5) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -8 else if k.val = 2 then 1 else 4) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 2) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3945932757588146863732 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (60 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (60 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (60 : Fin 88) = 109632842416394854830000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (60 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 42251511063210557482982448992970000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (60 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((385391002659 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (60 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12615081723055872930355306141230000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (60 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((115066630081 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (60 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 12523112872682171678829933971130000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (60 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((114227749611 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (60 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 42243136757446252737832310894670000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (60 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((385314617649 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_61 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (61 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else 5) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 8 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else 8) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (61 : Fin 88)), (alphaG (n3 5) (m3 5) (61 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else 5) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 8 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else 8) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3002610138491004669313 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (61 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (61 : Fin 88)))) =
        {(⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (61 : Fin 88) = 938494294883714664666000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (61 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 6859128197782496592270772914672000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (61 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((913581499 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (61 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 166084015177199922630569802355806000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (61 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((176968593291 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (61 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 296300387225297229544538705719440000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (61 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((7892972521 : ℚ)/25000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (61 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 296308336743099030639373188401772000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (61 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((157863685671 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (61 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 166079816547054437637205307593002000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (61 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((176964119497 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (61 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 6862610993281547622042223015308000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (61 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((3656181519 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_62 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (62 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else 0) else if j.val = 1 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else -8) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else 5) else if j.val = 3 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else -8) else if j.val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (45 : Int) else if k.val = 1 then -6 else if k.val = 2 then -7 else -7) else if j.val = 1 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 0 else if k.val = 2 then -3 else -3) else if j.val = 2 then (if k.val = 0 then (45 : Int) else if k.val = 1 then -6 else if k.val = 2 then -7 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else 7) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (62 : Fin 88)), (alphaG (n3 5) (m3 5) (62 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else 0) else if j.val = 1 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else -8) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else 5) else if j.val = 3 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else -8) else if j.val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (45 : Int) else if k.val = 1 then -6 else if k.val = 2 then -7 else -7) else if j.val = 1 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 0 else if k.val = 2 then -3 else -3) else if j.val = 2 then (if k.val = 0 then (45 : Int) else if k.val = 1 then -6 else if k.val = 2 then -7 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else 7) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5115744178068067865504 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (62 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (62 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (62 : Fin 88) = 28732036887626339785320000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (62 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 9658800312103043444743126994520000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (62 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((336168311 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (62 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1187430322755576171770783867217240000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (62 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((41327746007 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (62 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 1107268387800285798752004660141360000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (62 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((19268880799 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (62 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 4108852250202761197158899067158880000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (62 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((35751487671 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (62 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 15905617407060144739462452226334040000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (62 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((553584748247 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (62 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 4108852210437622144684044804276000000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (62 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((1430059493 : ℚ)/10000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 5 (62 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 1107268404378671082912402716271000000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 5) (m3 5) (62 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((1541510487 : ℚ)/40000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 5 (62 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 1187430333242769635754397888859040000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 5) (m3 5) (62 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((10331936593 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 5 (62 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 9658771436405971380271642747920000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 5) (m3 5) (62 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((168083653 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_63 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (63 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 1) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -6) else if j.val = 1 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 3 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (63 : Fin 88)), (alphaG (n3 5) (m3 5) (63 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 1) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -6) else if j.val = 1 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 3 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3392355158030136610964960 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (63 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (63 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (63 : Fin 88) = 37632411689244315100870000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (63 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 409450259716864445160399561911150000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (63 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((2176051129 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (63 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 56968794141077458754644517535030000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (63 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((1513822569 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (63 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 6151405113387628373389352693883010000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (63 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((163460294923 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (63 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 11767762469638669160892693399396600000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (63 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((15635142609 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (63 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 430620203642061056399464656697890000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (63 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((11442801147 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (63 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 430615722976595688214331486712210000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (63 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((11442682083 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 5 (63 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 11767770488164789846625133517271850000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 5) (m3 5) (63 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((62540613051 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 5 (63 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 6151404854439003539699220484796540000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 5) (m3 5) (63 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((81730144021 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 5 (63 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 56967592914496338076106497764630000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 5) (m3 5) (63 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((1513790649 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 5 (63 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 409446190223129193658653184031090000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 5) (m3 5) (63 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((10880147507 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    (((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (48 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 8) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else -1) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 4 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else 1) else if j.val = 1 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -8) else if j.val = 2 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (48 : Fin 88)), (alphaG (n3 5) (m3 5) (48 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else 8) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else -1) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 4 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else 1) else if j.val = 1 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -8) else if j.val = 2 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (26610939119659347745850 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (49 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -5) else if j.val = 2 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else 4) else if j.val = 2 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (49 : Fin 88)), (alphaG (n3 5) (m3 5) (49 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -5) else if j.val = 2 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else 4) else if j.val = 2 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (952399425185747065234 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (50 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else 0) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -2) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 2) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 2) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (50 : Fin 88)), (alphaG (n3 5) (m3 5) (50 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else 0) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -2) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 2) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 2) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (808668111586379131516474 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (51 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 1) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 1) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 1) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -6) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -7) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 6) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -7) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (51 : Fin 88)), (alphaG (n3 5) (m3 5) (51 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 1) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 1) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 1) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -6) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -7) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 6) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else -7) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3129956813746275439141 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (52 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -1) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 8) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 5) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -8 else if k.val = 2 then 1 else 8) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else -6) else if j.val = 4 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (52 : Fin 88)), (alphaG (n3 5) (m3 5) (52 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -1) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 8) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 5) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -8 else if k.val = 2 then 1 else 8) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else -6) else if j.val = 4 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5700984369205773901574 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (53 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else -5) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else -1) else if j.val = 1 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 4 else if k.val = 2 then 4 else 3) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -8) else if j.val = 3 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 4 else if k.val = 2 then 4 else 3) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (53 : Fin 88)), (alphaG (n3 5) (m3 5) (53 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else -5) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else 4) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else -1) else if j.val = 1 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 4 else if k.val = 2 then 4 else 3) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -8) else if j.val = 3 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 4 else if k.val = 2 then 4 else 3) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (14765248875875496192487 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (54 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else if j.val = 1 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else -8) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else -6) else if j.val = 2 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 4 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (54 : Fin 88)), (alphaG (n3 5) (m3 5) (54 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else if j.val = 1 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else -8) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else -6) else if j.val = 2 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 4 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2184449449248143599425 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (55 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 5) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 5 else if k.val = 2 then -2 else -2) else if j.val = 2 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 4 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (55 : Fin 88)), (alphaG (n3 5) (m3 5) (55 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 5) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 5 else if k.val = 2 then -2 else -2) else if j.val = 2 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 4 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (4552097907405688851147 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (56 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else -1) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (56 : Fin 88)), (alphaG (n3 5) (m3 5) (56 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else -1) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (550582123745306811964 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (57 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (57 : Fin 88)), (alphaG (n3 5) (m3 5) (57 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2077630512182625889118 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (58 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 4 else if k.val = 2 then -7 else -3) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 3 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 4 else if k.val = 2 then -7 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else 8) else if j.val = 1 then (if k.val = 0 then (24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 8 else -4) else if j.val = 3 then (if k.val = 0 then (24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (58 : Fin 88)), (alphaG (n3 5) (m3 5) (58 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 4 else if k.val = 2 then -7 else -3) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 3 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 4 else if k.val = 2 then -7 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else 8) else if j.val = 1 then (if k.val = 0 then (24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 6 else if k.val = 2 then 8 else -4) else if j.val = 3 then (if k.val = 0 then (24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (487191028431954900188 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (59 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 0) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 1) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 4 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (59 : Fin 88)), (alphaG (n3 5) (m3 5) (59 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 0) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 1) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 4 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5204548619398910931713 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (60 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 5) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -8 else if k.val = 2 then 1 else 4) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 2) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (60 : Fin 88)), (alphaG (n3 5) (m3 5) (60 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 5) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -8 else if k.val = 2 then 1 else 4) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 2) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3945932757588146863732 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (61 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else 5) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 8 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else 8) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (61 : Fin 88)), (alphaG (n3 5) (m3 5) (61 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else 5) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else -5) else if j.val = 4 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 8 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else 8) else if j.val = 1 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3002610138491004669313 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (62 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else 0) else if j.val = 1 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else -8) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else 5) else if j.val = 3 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else -8) else if j.val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (45 : Int) else if k.val = 1 then -6 else if k.val = 2 then -7 else -7) else if j.val = 1 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 0 else if k.val = 2 then -3 else -3) else if j.val = 2 then (if k.val = 0 then (45 : Int) else if k.val = 1 then -6 else if k.val = 2 then -7 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else 7) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (62 : Fin 88)), (alphaG (n3 5) (m3 5) (62 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else 0) else if j.val = 1 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else -8) else if j.val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else 5) else if j.val = 3 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else -8) else if j.val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (45 : Int) else if k.val = 1 then -6 else if k.val = 2 then -7 else -7) else if j.val = 1 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 0 else if k.val = 2 then -3 else -3) else if j.val = 2 then (if k.val = 0 then (45 : Int) else if k.val = 1 then -6 else if k.val = 2 then -7 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else if j.val = 1 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else 7) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5115744178068067865504 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (63 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 1) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -6) else if j.val = 1 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 3 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (63 : Fin 88)), (alphaG (n3 5) (m3 5) (63 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 1) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 7 else if k.val = 2 then -8 else 6) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -6) else if j.val = 1 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 3 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 3) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3392355158030136610964960 : ℚ)/10^30) :=
  ⟨L3C.pn_5_48, L3C.pn_5_49, L3C.pn_5_50, L3C.pn_5_51, L3C.pn_5_52, L3C.pn_5_53, L3C.pn_5_54, L3C.pn_5_55, L3C.pn_5_56, L3C.pn_5_57, L3C.pn_5_58, L3C.pn_5_59, L3C.pn_5_60, L3C.pn_5_61, L3C.pn_5_62, L3C.pn_5_63⟩

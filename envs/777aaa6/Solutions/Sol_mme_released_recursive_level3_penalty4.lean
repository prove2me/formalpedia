-- Prove2me | solution 1 for mme_released_recursive_level3_penalty4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T07:36:55.528971+00:00
-- url     : https://prove2.me/submissions/bc0006de-3212-4b06-84a3-fa5eb4b60eb6

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

theorem pn_0_52 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (52 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else -6) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -2) else if j.val = 2 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 6) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 5) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 5) else if j.val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (52 : Fin 88)), (alphaG (n3 0) (m3 0) (52 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else -6) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -2) else if j.val = 2 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 6) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 5) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 5) else if j.val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (209787359010809299605 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (52 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (52 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (52 : Fin 88) = 3190272719450719236191000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (52 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 22549136772919156330195310241768000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (52 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((883511331 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (52 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 559391224607475429196558109333469000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (52 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((175342760259 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (52 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 1013196524637875014914997536381651000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (52 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((317589314061 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (52 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1013191715620777714900820902068251000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (52 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((317587806661 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (52 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 559389010373172312669266477080391000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (52 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((175342066201 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (52 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 22555107438499608179161664894470000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (52 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((706996217 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_53 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (53 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -4) else if j.val = 1 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else -6) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else 2) else if j.val = 1 then (if k.val = 0 then (-40 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else 5) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else 8) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 4) else if j.val = 3 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 4 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (53 : Fin 88)), (alphaG (n3 0) (m3 0) (53 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -4) else if j.val = 1 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else -6) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else 2) else if j.val = 1 then (if k.val = 0 then (-40 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else 5) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else 8) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 4) else if j.val = 3 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 4 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3834087257060591849234 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (53 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (53 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (53 : Fin 88) = 10616090467421600222432000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (53 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 3539716356415389686557361627840000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (53 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((33342937 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (53 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 409855713105022069787183486316896000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (53 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((38607029053 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (53 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 1534002905710265546675873952864288000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (53 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((144497911959 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (53 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 413348227722277138520859860776896000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (53 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((19468006089 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (53 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 5894597155852056753213046784268160000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (53 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((27762560869 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (53 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 413348219324949578790374084833184000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (53 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((38936011387 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 0 (53 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 1534003039993193869091695166406656000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 0) (m3 0) (53 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((282222509 : ℚ)/1953125000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 0 (53 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 409855740653776832746236063527936000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 0) (m3 0) (53 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((1206469739 : ℚ)/31250000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 0 (53 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 3539748703643043920173239378144000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 0) (m3 0) (53 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((333432417 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_54 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (54 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 1) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 4 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else 1) else if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -6) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (54 : Fin 88)), (alphaG (n3 0) (m3 0) (54 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 1) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 4 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else 1) else if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -6) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5009239826173148986975 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (54 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (54 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (54 : Fin 88) = 8127611271510001136598000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (54 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 1162886984670421879901114606741340000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (54 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((14307856833 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (54 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 302472651448968031974857726022228000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (54 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((18607721343 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (54 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 2729001713353343846854626186756000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (54 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((167884611 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (54 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 341120920425281743566817818850482000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (54 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((41970624459 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (54 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 4509192183009827190913684362251694000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (54 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((554799194053 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (54 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 341120826486350667454224682050798000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (54 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((41970612901 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 0 (54 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 2728870614983534390536292861016000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 0) (m3 0) (54 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((83938273 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 0 (54 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 302472721882847310880527575780496000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 0) (m3 0) (54 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((4651931419 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 0 (54 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 1162887111257967433669382309255190000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 0) (m3 0) (54 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((28615716781 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_55 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (55 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else 3) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else 3) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else -5) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (55 : Fin 88)), (alphaG (n3 0) (m3 0) (55 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else 3) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else 3) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else -5) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (6310335278515963727813 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (55 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (55 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (55 : Fin 88) = 1780804576694274160481000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (55 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 313613995244191963701700168016414000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (55 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((88054017647 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (55 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12923830823095221266933238217307000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (55 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((7257298747 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (55 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 563864784739038620187560202863354000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (55 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((158317423517 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (55 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 563864394162294032139185681207548000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (55 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((79158656927 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (55 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 12923399148942612268099640980983000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (55 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((7257056343 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (55 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 313614172576711710917521068714394000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (55 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((88054067437 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_56 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (56 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -1) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 3 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 8 else if k.val = 2 then -7 else 8) else if j.val = 1 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -3) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 0) else if j.val = 3 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -3) else if j.val = 4 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 8 else if k.val = 2 then -7 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (56 : Fin 88)), (alphaG (n3 0) (m3 0) (56 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -1) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 3 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 8 else if k.val = 2 then -7 else 8) else if j.val = 1 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -3) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 0) else if j.val = 3 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -3) else if j.val = 4 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 8 else if k.val = 2 then -7 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1132636157466808998616 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (56 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (56 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (56 : Fin 88) = 4273642688720194215951000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (56 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 1391841459458261970479479910703000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (56 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((325680353 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (56 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 53087093125734192665044529168754000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (56 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((6210988727 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (56 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 278802551764201874636542209182169000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (56 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((65237684119 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (56 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1803539826864394863310658335887486000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (56 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((211007325393 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (56 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 1803539908478149289800207277903733000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (56 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((422014669883 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (56 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 278802614595296684200837572093771000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (56 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((65237698821 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 0 (56 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 53087008182812111662464292926678000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 0) (m3 0) (56 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((6210978789 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 0 (56 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 1391844250146937704766302926706000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 0) (m3 0) (56 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((162840503 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_57 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (57 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 3 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -5) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 3 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (57 : Fin 88)), (alphaG (n3 0) (m3 0) (57 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 3 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -5) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 3 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (816084470811397477129235 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (57 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (57 : Fin 88)))) =
        {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (57 : Fin 88) = 26234019409813223425551000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (57 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 42681625320864306967681575011895000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (57 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((325391429 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (57 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 289713837937261525074055567581210000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (57 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((1104344071 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (57 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 315524028373461609596097169864959000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (57 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((12027285009 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (57 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 8231805204277594588105837152454821000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (57 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((313783605771 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (57 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 4237284959310196920845583367093521000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (57 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((161518709471 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (57 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 4237285140902079275572715918757543000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (57 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((161518716393 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 0 (57 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 8231805468978850433121261516264411000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 0) (m3 0) (57 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((313783615861 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 0 (57 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 315524135460728840453675192964141000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 0) (m3 0) (57 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((12027289091 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 0 (57 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 289713431467364789427971812094016000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 0) (m3 0) (57 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((172553519 : ℚ)/15625000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 0 (57 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 42681577784821136386120727913483000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 0) (m3 0) (57 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((1626955333 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_58 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (58 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -6) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 3 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then 0 else -6) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then 0 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else 4) else if j.val = 1 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else -8) else if j.val = 2 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (58 : Fin 88)), (alphaG (n3 0) (m3 0) (58 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -6) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 3 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then 0 else -6) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then 0 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else 4) else if j.val = 1 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else -8) else if j.val = 2 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3154491334019105118345151 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (58 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (58 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (58 : Fin 88) = 28069108486075679996000000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (58 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 301168044238537397787803682372000000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (58 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((10729519407 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (58 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 42634468657578981634186757280000000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (58 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((37972767 : ℚ)/25000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (58 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 4585641557532305746214781559204000000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (58 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((163369690199 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (58 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 8778287812810382959597762437700000000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (58 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((12509535623 : ℚ)/40000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (58 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 326822814069486651414270618708000000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (58 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((11643505323 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (58 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 326820954406842123442243843720000000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (58 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((1164343907 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 0 (58 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 8778291172738806959828809318892000000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 0) (m3 0) (58 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((312738510277 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 0 (58 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 4585641455950202135106895653680000000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 0) (m3 0) (58 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((8168484329 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 0 (58 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 42633954459580625213804910556000000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 0) (m3 0) (58 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((1518892361 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 0 (58 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 301166251211956415759441217888000000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 0) (m3 0) (58 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((1341181941 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_59 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (59 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else 7) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else -1) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -4 else if k.val = 2 then -4 else 8) else if j.val = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else -1) else if j.val = 4 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (59 : Fin 88)), (alphaG (n3 0) (m3 0) (59 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else 7) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else -1) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -4 else if k.val = 2 then -4 else 8) else if j.val = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else -1) else if j.val = 4 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5945970091496359589700 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (59 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (59 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (59 : Fin 88) = 30355291583649730909196000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (59 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 375978923597358390384780850052380000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (59 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((2477188681 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (59 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 9856976900496305856475463324728000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (59 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((162360109 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (59 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 12808036351088052944799179440851392000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (59 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((26371094797 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (59 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 1983773477130306611149773685553016000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (59 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((32675908773 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (59 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 1983773819416574508384139417647112000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (59 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((32675914411 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (59 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 12808036613145285186447306379940460000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (59 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((84387505077 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 0 (59 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 9856901801504927907041193973824000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 0) (m3 0) (59 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((20294859 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 0 (59 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 375978520570152034267303568657088000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 0) (m3 0) (59 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((774120633 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_60 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (60 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (46 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -8) else if j.val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (60 : Fin 88)), (alphaG (n3 0) (m3 0) (60 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (46 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -8) else if j.val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (10396956796409201105330 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (60 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (60 : Fin 88)))) =
        {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (60 : Fin 88) = 109686396664275155878000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (60 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 12530342289469304695209969596662000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (60 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((114237887929 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (60 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 42274718500124216872986768230884000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (60 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((192707207939 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (60 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 42350087933043849430678473302194000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (60 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((386101551523 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (60 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 12531247941637784879124788870260000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (60 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((11424614467 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_61 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (61 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then -2 else if k.val = 2 then 7 else 6) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 3) else if j.val = 4 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (61 : Fin 88)), (alphaG (n3 0) (m3 0) (61 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then -2 else if k.val = 2 then 7 else 6) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 3) else if j.val = 4 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (9928603211678323602194 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (61 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (61 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (61 : Fin 88) = 111367256841534290010000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (61 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 13238708938706762296572355070610000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (61 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((118874338061 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (61 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 42439168403971532646486568572840000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (61 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((95268505321 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (61 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 42447849922545300080027102222430000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (61 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((381151975243 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (61 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 13241529576310694986913974134120000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (61 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((29724916353 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_62 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (62 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else -1) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else -5) else if j.val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 5) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (62 : Fin 88)), (alphaG (n3 0) (m3 0) (62 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else -1) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else -5) else if j.val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 5) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3783325623664480151343 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (62 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (62 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (62 : Fin 88) = 3200020600325682870540000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (62 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 23583714019981890398229232810980000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (62 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((7369863187 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (62 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1009068218260735617561955054262040000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (62 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((157665894113 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (62 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 567358355603644883860170538665000000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (62 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((709193379 : ℚ)/4000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (62 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 567358374122164097944897310479980000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (62 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((177298350537 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (62 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1009068160861966109520181405386060000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (62 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((315331770289 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (62 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 23583777457190271254566458395940000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (62 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((7369883011 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_63 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (63 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -7 else if k.val = 2 then 7 else 5) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -7 else if k.val = 2 then 7 else 5) else if j.val = 4 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (63 : Fin 88)), (alphaG (n3 0) (m3 0) (63 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -7 else if k.val = 2 then 7 else 5) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -7 else if k.val = 2 then 7 else 5) else if j.val = 4 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (6673508589586349343684 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (63 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (63 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (63 : Fin 88) = 10614889161665752679443000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (63 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 3488130056599357328793777054457000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (63 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((328607299 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (63 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 719975292675693923791989562729779000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (63 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((67826925153 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (63 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 4449024309059100789417604862080970000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (63 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((41913054779 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (63 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 134957125824717159617612914611019000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (63 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((12713945833 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (63 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 134956548618889215718979464539008000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (63 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((99327277 : ℚ)/7812500000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (63 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 4449024764766907388890033143248403000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (63 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((419130590721 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 0 (63 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 719974850905236793586694549671005000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 0) (m3 0) (63 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((13565376707 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 0 (63 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 3488139758608051091291726065359000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 0) (m3 0) (63 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((328608213 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_64 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (64 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 4) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else -8) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 2) else if j.val = 4 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (64 : Fin 88)), (alphaG (n3 0) (m3 0) (64 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 4) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else -8) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 2) else if j.val = 4 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (7161703250583737962154 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (64 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (64 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (64 : Fin 88) = 109632826179711249051000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (64 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 42243410690157483255888612488952000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (64 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((48164646669 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (64 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12615094544238520889096717148519000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (64 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((115066764069 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (64 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 12523133828537055674139300667374000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (64 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((57113978837 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (64 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 42251187116778189231875369695155000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (64 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((77077620981 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_65 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (65 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 5) else if j.val = 1 then (if k.val = 0 then (-47 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else 8) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 4 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (65 : Fin 88)), (alphaG (n3 0) (m3 0) (65 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 5) else if j.val = 1 then (if k.val = 0 then (-47 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else 8) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 4 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (7689124763875012790408 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (65 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (65 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (65 : Fin 88) = 2802759484678642772007000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (65 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 20591325038713749495856316377113000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (65 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((7346804159 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (65 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 495759588871114501558356465853614000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (65 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((88441336401 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (65 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 885028779585803595454579630003284000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (65 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((78942626403 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (65 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 885029115148985658089764151313366000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (65 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((157885312669 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (65 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 495759729735003442022263544153427000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (65 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((176882723061 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (65 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 20590946299021825386179892299196000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (65 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((1836667257 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_66 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (66 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -8 else if k.val = 2 then -4 else 3) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 6) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -8 else if k.val = 2 then -4 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else -5) else if j.val = 1 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -2) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -2) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 8) else if j.val = 1 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 8) else if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (66 : Fin 88)), (alphaG (n3 0) (m3 0) (66 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -8 else if k.val = 2 then -4 else 3) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 6) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -8 else if k.val = 2 then -4 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else -5) else if j.val = 1 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -2) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -2) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 8) else if j.val = 1 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 8) else if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (17114077261382542085413 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (66 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (66 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (66 : Fin 88) = 1184415063497108503930000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (66 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 173106714272206381672951948614920000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (66 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((36538439861 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (66 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 40258842347712818685453774712020000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (66 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((16995242457 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (66 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 377632792001350684301594936920000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (66 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((79708711 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (66 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 44736521882090320901499357359360000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (66 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((295085809 : ℚ)/7812500000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (66 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 667455676195180331747443197836120000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (66 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((140882976071 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (66 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 44736472417364024071756907730770000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (66 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((37770941789 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 0 (66 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 377597228754654120121655934740000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 0) (m3 0) (66 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((159402409 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 0 (66 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 40258885671247011282688631463560000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 0) (m3 0) (66 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((8497630373 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 0 (66 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 173106720690551610763782931411590000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 0) (m3 0) (66 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((146153764863 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_0_67 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (67 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else 7) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -6) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (67 : Fin 88)), (alphaG (n3 0) (m3 0) (67 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else 7) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -6) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1582988684907849863634 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (67 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (67 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 0 (67 : Fin 88) = 2341315562025556471236000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 0 (67 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 403385693087772717362441641500708000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 0) (m3 0) (67 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((172290185753 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 0 (67 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 15532918921721722229092150475268000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 0) (m3 0) (67 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((6634269713 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 0 (67 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 751739574200720222417371346011128000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 0) (m3 0) (67 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((160537858799 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 0 (67 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 751739060881331141686268366345544000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 0) (m3 0) (67 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((160537749177 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 0 (67 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 15532475542111110325412079571476000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 0) (m3 0) (67 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((6634080341 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 0 (67 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 403385839391899557215414416095876000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 0) (m3 0) (67 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((172290248241 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    (((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (52 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else -6) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -2) else if j.val = 2 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 6) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 5) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 5) else if j.val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (52 : Fin 88)), (alphaG (n3 0) (m3 0) (52 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else -6) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -2) else if j.val = 2 then (if k.val = 0 then (32 : Int) else if k.val = 1 then -4 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 6) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 5) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 5) else if j.val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (209787359010809299605 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (53 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -4) else if j.val = 1 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else -6) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else 2) else if j.val = 1 then (if k.val = 0 then (-40 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else 5) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else 8) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 4) else if j.val = 3 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 4 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (53 : Fin 88)), (alphaG (n3 0) (m3 0) (53 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -4) else if j.val = 1 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else -6) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else 2) else if j.val = 1 then (if k.val = 0 then (-40 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else 5) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else 8) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 4) else if j.val = 3 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -5) else if j.val = 4 then (if k.val = 0 then (-36 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3834087257060591849234 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (54 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 1) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 4 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else 1) else if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -6) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (54 : Fin 88)), (alphaG (n3 0) (m3 0) (54 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else 1) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 7 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 8) else if j.val = 4 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else 1) else if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -6) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5009239826173148986975 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (55 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else 3) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else 3) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else -5) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (55 : Fin 88)), (alphaG (n3 0) (m3 0) (55 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else 3) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else 3) else if j.val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else -5) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else 2) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (6310335278515963727813 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (56 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -1) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 3 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 8 else if k.val = 2 then -7 else 8) else if j.val = 1 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -3) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 0) else if j.val = 3 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -3) else if j.val = 4 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 8 else if k.val = 2 then -7 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (56 : Fin 88)), (alphaG (n3 0) (m3 0) (56 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -1) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else if j.val = 3 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 8 else if k.val = 2 then -7 else 8) else if j.val = 1 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -3) else if j.val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 6 else if k.val = 2 then 1 else 0) else if j.val = 3 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 2 else if k.val = 2 then -5 else -3) else if j.val = 4 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 8 else if k.val = 2 then -7 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1132636157466808998616 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (57 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 3 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -5) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 3 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (57 : Fin 88)), (alphaG (n3 0) (m3 0) (57 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -7 else if k.val = 2 then -8 else 5) else if j.val = 3 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -5) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 3 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (816084470811397477129235 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (58 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -6) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 3 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then 0 else -6) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then 0 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else 4) else if j.val = 1 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else -8) else if j.val = 2 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (58 : Fin 88)), (alphaG (n3 0) (m3 0) (58 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -6) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 8) else if j.val = 3 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -8 else if k.val = 2 then 3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then 0 else -6) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then 0 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else 4) else if j.val = 1 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else -8) else if j.val = 2 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 1 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3154491334019105118345151 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (59 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else 7) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else -1) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -4 else if k.val = 2 then -4 else 8) else if j.val = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else -1) else if j.val = 4 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (59 : Fin 88)), (alphaG (n3 0) (m3 0) (59 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else 7) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else -1) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -4 else if k.val = 2 then -4 else 8) else if j.val = 3 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then 4 else -1) else if j.val = 4 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -4 else if k.val = 2 then 8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5945970091496359589700 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (60 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (46 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -8) else if j.val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (60 : Fin 88)), (alphaG (n3 0) (m3 0) (60 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (46 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -8) else if j.val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (10396956796409201105330 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (61 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then -2 else if k.val = 2 then 7 else 6) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 3) else if j.val = 4 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (61 : Fin 88)), (alphaG (n3 0) (m3 0) (61 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then -2 else if k.val = 2 then 7 else 6) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 3) else if j.val = 4 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (9928603211678323602194 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (62 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else -1) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else -5) else if j.val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 5) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (62 : Fin 88)), (alphaG (n3 0) (m3 0) (62 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else -1) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else -5) else if j.val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 5) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3783325623664480151343 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (63 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -7 else if k.val = 2 then 7 else 5) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -7 else if k.val = 2 then 7 else 5) else if j.val = 4 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (63 : Fin 88)), (alphaG (n3 0) (m3 0) (63 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -7 else if k.val = 2 then 7 else 5) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -7 else if k.val = 2 then 7 else 5) else if j.val = 4 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -5 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (6673508589586349343684 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (64 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 4) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else -8) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 2) else if j.val = 4 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (64 : Fin 88)), (alphaG (n3 0) (m3 0) (64 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 4) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else -8) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 2) else if j.val = 4 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (7161703250583737962154 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (65 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 5) else if j.val = 1 then (if k.val = 0 then (-47 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else 8) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 4 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (65 : Fin 88)), (alphaG (n3 0) (m3 0) (65 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 5) else if j.val = 1 then (if k.val = 0 then (-47 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else 8) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 4 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (7689124763875012790408 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (66 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -8 else if k.val = 2 then -4 else 3) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 6) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -8 else if k.val = 2 then -4 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else -5) else if j.val = 1 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -2) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -2) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 8) else if j.val = 1 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 8) else if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (66 : Fin 88)), (alphaG (n3 0) (m3 0) (66 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -8 else if k.val = 2 then -4 else 3) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 6) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -8 else if k.val = 2 then -4 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else -5) else if j.val = 1 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -2) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -2) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 8) else if j.val = 1 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 8) else if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (17114077261382542085413 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (67 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else 7) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -6) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (67 : Fin 88)), (alphaG (n3 0) (m3 0) (67 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else 7) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -6) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1582988684907849863634 : ℚ)/10^30) :=
  ⟨L3C.pn_0_52, L3C.pn_0_53, L3C.pn_0_54, L3C.pn_0_55, L3C.pn_0_56, L3C.pn_0_57, L3C.pn_0_58, L3C.pn_0_59, L3C.pn_0_60, L3C.pn_0_61, L3C.pn_0_62, L3C.pn_0_63, L3C.pn_0_64, L3C.pn_0_65, L3C.pn_0_66, L3C.pn_0_67⟩

-- Prove2me | solution 1 for mme_released_recursive_level3_penalty36
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T09:53:52.291403+00:00
-- url     : https://prove2.me/submissions/1993e7e9-00a9-4d94-ae28-5ce574080363

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

theorem pn_5_80 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (80 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then -7 else if k.val = 2 then 8 else 8) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then -7 else if k.val = 2 then 8 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 1) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -2) else if j.val = 2 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (80 : Fin 88)), (alphaG (n3 5) (m3 5) (80 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then -7 else if k.val = 2 then 8 else 8) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then -7 else if k.val = 2 then 8 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 1) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -2) else if j.val = 2 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5532610655987484173432 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (80 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (80 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (80 : Fin 88) = 525291696974997602590000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (80 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 92404155261755143693358150590270000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (80 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((175910176753 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (80 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 166480302349544689473952252363720000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (80 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((79232311927 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (80 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 3761289230154436677753505470650000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (80 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((1432076407 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (80 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 3761495118235066028063840621150000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (80 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((1432154797 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (80 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 166480314365066966080047414007380000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (80 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((158464635291 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (80 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 92404140650241300636824836946830000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (80 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((175910148937 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_81 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (81 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 6) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 3 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (81 : Fin 88)), (alphaG (n3 5) (m3 5) (81 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 6) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 3 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (868495353169649096052844 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (81 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (81 : Fin 88)))) =
        {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (81 : Fin 88) = 36384827260980355605668000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (81 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 59661912001637645860973686898024000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (81 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((819873509 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (81 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 407850708044074451027359741457292000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (81 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((11209362219 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (81 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 434292550044613147367555148971832000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (81 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((5968044687 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (81 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 11415450488596611760001074207752140000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (81 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((62748411071 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (81 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 5875157697279719114480254170155652000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (81 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((161472738489 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (81 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 5875157844492730212406772950688380000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (81 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((32294548507 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 5 (81 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 11415449583378494334070807094337968000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 5) (m3 5) (81 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((78435507619 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 5 (81 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 434293230149804309612362130118088000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 5) (m3 5) (81 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((5968054033 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 5 (81 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 407851168821526884082583131636844000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 5) (m3 5) (81 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((11209374883 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 5 (81 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 59662078171143746758257737983780000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 5) (m3 5) (81 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((327950317 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_82 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (82 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 7 else if k.val = 2 then -1 else 1) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 7 else if k.val = 2 then -1 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 8 else if k.val = 2 then 8 else -3) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 1) else if j.val = 2 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else -1) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 1) else if j.val = 4 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 8 else if k.val = 2 then 8 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (82 : Fin 88)), (alphaG (n3 5) (m3 5) (82 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 7 else if k.val = 2 then -1 else 1) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 7 else if k.val = 2 then -1 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 8 else if k.val = 2 then 8 else -3) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 1) else if j.val = 2 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else -1) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 1) else if j.val = 4 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 8 else if k.val = 2 then 8 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (11140997437797271105300 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (82 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (82 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (82 : Fin 88) = 1096877623071500644950000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (82 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 356582920903736572813692471750000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (82 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((65017813 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (82 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 13285818900506117512214426763900000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (82 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((6056199261 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (82 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 67483413753162435263243855662650000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (82 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((61523193047 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (82 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 467312984733538683366847423393500000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (82 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((42603930913 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (82 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 467313003820306202434030146168450000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (82 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((426039326531 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (82 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 67483437987576639404979105187950000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (82 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((61523215141 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 5 (82 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 13285797094578970850781605157900000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 5) (m3 5) (82 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((6056189321 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 5 (82 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 356583860927859545089745193900000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 5) (m3 5) (82 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((162544961 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_83 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (83 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 7) else if j.val = 1 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else 0) else if j.val = 2 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 4) else if j.val = 2 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else -4) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else -6) else if j.val = 4 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -8 else if k.val = 2 then 1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (83 : Fin 88)), (alphaG (n3 5) (m3 5) (83 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 7) else if j.val = 1 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else 0) else if j.val = 2 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 4) else if j.val = 2 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else -4) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else -6) else if j.val = 4 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -8 else if k.val = 2 then 1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5488367681801522996678 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (83 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (83 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (83 : Fin 88) = 35414560703905846673420000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (83 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 11321604840955268133266985293840000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (83 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((79921963 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (83 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1284642462277168609583898714109500000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (83 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((1450976589 : ℚ)/40000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (83 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 5196347703550392924245464895487500000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (83 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((234766609 : ℚ)/1600000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (83 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 1299759804869479808429970622649240000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (83 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((18350641361 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (83 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 19830417365982631178827550515955920000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (83 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((139987740719 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (83 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 1299761188516366510031400153168640000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (83 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((573458153 : ℚ)/15625000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 5 (83 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 5196347707339750919563390489543440000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 5) (m3 5) (83 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((36682282683 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 5 (83 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 1284643827048094456003511967696040000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 5) (m3 5) (83 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((18137226631 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 5 (83 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 11319039481006998601545656095880000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 5) (m3 5) (83 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((159807707 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_84 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (84 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else -1) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else -8) else if j.val = 1 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else 7) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -8) else if j.val = 3 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else 7) else if j.val = 4 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (84 : Fin 88)), (alphaG (n3 5) (m3 5) (84 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else -1) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else -8) else if j.val = 1 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else 7) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -8) else if j.val = 3 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else 7) else if j.val = 4 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (8317760032113706770744 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (84 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (84 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (84 : Fin 88) = 6970646113921213585948000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (84 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 2275091795793288988966114610116000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (84 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((326381767 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (84 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 428035488390705545038886986198744000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (84 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((30702712589 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (84 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 2970142456265832183819482409515160000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (84 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((42609284817 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (84 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 84870213685791530225256597052904000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (84 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((6087686299 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (84 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 84869805136222793302928324640624000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (84 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((3043828497 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (84 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 2970142744948170345752621857965632000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (84 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((26630805599 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 5 (84 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 428035233655413957902057701315032000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 5) (m3 5) (84 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((30702694317 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 5 (84 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2275080043283940917800008701788000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 5) (m3 5) (84 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((326380081 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_85 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (85 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -2 else if k.val = 2 then 7 else 0) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else 2) else if j.val = 2 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (85 : Fin 88)), (alphaG (n3 5) (m3 5) (85 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -2 else if k.val = 2 then 7 else 0) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else 2) else if j.val = 2 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2303823121828684249418 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (85 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (85 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (85 : Fin 88) = 3446777849244032817410000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (85 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 22793358045239643249357652446140000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (85 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((3306473327 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (85 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 594392254460627935211677758292260000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (85 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((86224334793 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (85 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 1106202955009282981466700508681140000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (85 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((160469140077 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (85 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1106203527608699964980896333734800000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (85 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((8023461157 : ℚ)/25000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (85 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 594392894006811084592722995900350000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (85 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((34489771027 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (85 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 22792860113371207908644750945310000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (85 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((6612802191 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_86 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (86 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -5) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else -5) else if j.val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 4 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (86 : Fin 88)), (alphaG (n3 5) (m3 5) (86 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -5) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else -5) else if j.val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 4 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2774726708745677058933 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (86 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (86 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (86 : Fin 88) = 3876039984640571513468000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (86 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 25547611166613783918879708204876000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (86 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((6591162957 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (86 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1242339614876179459857591201809764000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (86 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((320517750023 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (86 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 670135386127802491381580186627772000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (86 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((172891762929 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (86 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 670128669849750385707759937708348000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (86 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((172890030161 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 5 (86 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1242357438884809229372101599542444000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 5) (m3 5) (86 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((320522348533 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 5 (86 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 25531263735416163230087366106796000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 5) (m3 5) (86 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((6586945397 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_5_87 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (87 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else -1) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (87 : Fin 88)), (alphaG (n3 5) (m3 5) (87 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else -1) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (750003786705782802726 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (87 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (87 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 5 (87 : Fin 88) = 109605285797941197480000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 5 (87 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 12572658975862170509613310660920000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 5) (m3 5) (87 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((114708509579 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 5 (87 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 42229679860837594871228111814720000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 5) (m3 5) (87 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((48161089533 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 5 (87 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 42229679980636172248377840660360000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 5) (m3 5) (87 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((385288717357 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 5 (87 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 12573266980605259850780736864000000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 5) (m3 5) (87 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((143392571 : ℚ)/1250000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    (((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (80 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then -7 else if k.val = 2 then 8 else 8) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then -7 else if k.val = 2 then 8 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 1) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -2) else if j.val = 2 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (80 : Fin 88)), (alphaG (n3 5) (m3 5) (80 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then -7 else if k.val = 2 then 8 else 8) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then -7 else if k.val = 2 then 8 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 1) else if j.val = 1 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -2) else if j.val = 2 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5532610655987484173432 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (81 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 6) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 3 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (81 : Fin 88)), (alphaG (n3 5) (m3 5) (81 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 6) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 1) else if j.val = 3 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -7) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else if j.val = 1 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (868495353169649096052844 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (82 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 7 else if k.val = 2 then -1 else 1) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 7 else if k.val = 2 then -1 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 8 else if k.val = 2 then 8 else -3) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 1) else if j.val = 2 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else -1) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 1) else if j.val = 4 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 8 else if k.val = 2 then 8 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (82 : Fin 88)), (alphaG (n3 5) (m3 5) (82 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 7 else if k.val = 2 then -1 else 1) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 7 else if k.val = 2 then -1 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 8 else if k.val = 2 then 8 else -3) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 1) else if j.val = 2 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -7 else if k.val = 2 then -7 else -1) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 1) else if j.val = 4 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 8 else if k.val = 2 then 8 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (11140997437797271105300 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (83 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 7) else if j.val = 1 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else 0) else if j.val = 2 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 4) else if j.val = 2 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else -4) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else -6) else if j.val = 4 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -8 else if k.val = 2 then 1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (83 : Fin 88)), (alphaG (n3 5) (m3 5) (83 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 7) else if j.val = 1 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else 0) else if j.val = 2 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else if j.val = 1 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 4) else if j.val = 2 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -4 else if k.val = 2 then -1 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else -4) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else -6) else if j.val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else -6) else if j.val = 4 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -8 else if k.val = 2 then 1 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5488367681801522996678 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (84 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else -1) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else -8) else if j.val = 1 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else 7) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -8) else if j.val = 3 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else 7) else if j.val = 4 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (84 : Fin 88)), (alphaG (n3 5) (m3 5) (84 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else -1) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -4) else if j.val = 3 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else -8) else if j.val = 1 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else 7) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -8) else if j.val = 3 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else 7) else if j.val = 4 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (8317760032113706770744 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (85 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -2 else if k.val = 2 then 7 else 0) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else 2) else if j.val = 2 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (85 : Fin 88)), (alphaG (n3 5) (m3 5) (85 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else if j.val = 1 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then -2 else if k.val = 2 then 7 else 0) else if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else 2) else if j.val = 2 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -5) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -4 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2303823121828684249418 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (86 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -5) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else -5) else if j.val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 4 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (86 : Fin 88)), (alphaG (n3 5) (m3 5) (86 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -5) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else -5) else if j.val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 5 else if k.val = 2 then 7 else -2) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -4 else if k.val = 2 then 3 else 7) else if j.val = 4 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2774726708745677058933 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (87 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else -1) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (87 : Fin 88)), (alphaG (n3 5) (m3 5) (87 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else 2) else if j.val = 3 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else -1) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (750003786705782802726 : ℚ)/10^30) :=
  ⟨L3C.pn_5_80, L3C.pn_5_81, L3C.pn_5_82, L3C.pn_5_83, L3C.pn_5_84, L3C.pn_5_85, L3C.pn_5_86, L3C.pn_5_87⟩

-- Prove2me | solution 1 for mme_released_recursive_level3_penalty9
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T07:54:06.953124+00:00
-- url     : https://prove2.me/submissions/9e218574-d83d-4aad-81a9-c057918127d8

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

theorem pn_1_32 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (32 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 5 else if k.val = 2 then -3 else -5) else if j.val = 1 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 8) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 8) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (32 : Fin 88)), (alphaG (n3 1) (m3 1) (32 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 5 else if k.val = 2 then -3 else -5) else if j.val = 1 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 8) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 8) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5010086535956937448418 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (32 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (32 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (32 : Fin 88) = 10523423710807000306144000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (32 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 3459020550084717100255694271584000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (32 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((328697261 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (32 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 713801587488837041313000272753856000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (32 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((33914893437 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (32 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 4410669546134624442014712545654944000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (32 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((419128761451 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (32 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 133780245756267358349433145155264000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (32 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((6356308053 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (32 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 133783182633356570367078583822784000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (32 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((6356447593 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (32 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 4410667522448674582696132673245312000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (32 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((104782142287 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 1 (32 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 713803998878763254183085424120736000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 1) (m3 1) (32 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((67830016019 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 1 (32 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 3458606916392340120301660975520000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 1) (m3 1) (32 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((65731591 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_33 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (33 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else -1) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else -5) else if j.val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 6 else if k.val = 2 then 5 else -3) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 4 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 6 else if k.val = 2 then 5 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (33 : Fin 88)), (alphaG (n3 1) (m3 1) (33 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else -1) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else -5) else if j.val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 6 else if k.val = 2 then 5 else -3) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 4 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 6 else if k.val = 2 then 5 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5606419870025608398041 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (33 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (33 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (33 : Fin 88) = 3237129756997996772000000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (33 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 23864847783314882289162836256000000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (33 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((921528081 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (33 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 1020780516995133417921715506200000000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (33 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((6306701267 : ℚ)/20000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (33 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 573919496945743685025502385040000000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (33 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((8864635341 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (33 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 573919513092546912931510283776000000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (33 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((1385099311 : ℚ)/7812500000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (33 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 1020780484170637681962028238120000000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (33 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((31533505321 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (33 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 23864898010620191870080750608000000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (33 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((1843060041 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_34 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (34 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -1 else -6) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 0) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (34 : Fin 88)), (alphaG (n3 1) (m3 1) (34 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -1 else -6) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 0) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (11022741169134187954360 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (34 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (34 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (34 : Fin 88) = 111371972178627657280000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (34 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 13242618161643332303425008322240000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (34 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((118904405683 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (34 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 42440067127814531514482919776000000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (34 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((3810659567 : ℚ)/10000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (34 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 42439231587436254405141090896000000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (34 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((7621169089 : ℚ)/20000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (34 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 13250055301733539056950981005760000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (34 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((118971183167 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_35 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (35 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else 7) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 4 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (35 : Fin 88)), (alphaG (n3 1) (m3 1) (35 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else 7) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 4 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (518382528218507735864 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (35 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (35 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (35 : Fin 88) = 2337548271600266664368000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (35 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 402754616617781389374251001566832000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (35 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((172297882149 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (35 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 15499380250935113388086695329008000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (35 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((6630613981 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (35 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 750520449418603552998682264448128000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (35 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((40133954587 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (35 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 750519935742370868840082769580128000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (35 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((160535708473 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (35 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 15499092080321738778812578706336000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (35 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((3315245351 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (35 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 402754797490254000988084690369568000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (35 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((86148979763 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_36 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (36 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else -4) else if j.val = 1 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 2) else if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else -1) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 1 else 1) else if j.val = 1 then (if k.val = 0 then (20 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -7) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 1 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (36 : Fin 88)), (alphaG (n3 1) (m3 1) (36 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else -4) else if j.val = 1 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 2) else if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else -1) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 1 else 1) else if j.val = 1 then (if k.val = 0 then (20 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -7) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 1 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (13706571043332992359788 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (36 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (36 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (36 : Fin 88) = 774507148045033287717000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (36 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 113196259853236623528184323160116000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (36 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((36538158537 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (36 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 26351561811360936669534874546758000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (36 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((17011826087 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (36 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 246976579686161871976994460099000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (36 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((318882247 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (36 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 29229127472063926061766932719752000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (36 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((4717375357 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (36 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 436459296474475719102057825012924000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (36 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((140882914243 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (36 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 29229126191803610343326908123551000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (36 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((37739001203 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 1 (36 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 246976794999149028496248445425000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 1) (m3 1) (36 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((12755301 : ℚ)/40000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 1 (36 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 26351565680024141154476146693173000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 1) (m3 1) (36 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((34023657169 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 1 (36 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 113196257187383019957179746838202000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 1) (m3 1) (36 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((73076315353 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_37 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (37 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 5) else if j.val = 1 then (if k.val = 0 then (-47 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else 8) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (37 : Fin 88)), (alphaG (n3 1) (m3 1) (37 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 5) else if j.val = 1 then (if k.val = 0 then (-47 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else 8) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (10838749761778335214263 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (37 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (37 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (37 : Fin 88) = 2831677960029220116958000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (37 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 20820836619374960209016196640848000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (37 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((919103307 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (37 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 500860990245880596274083436251242000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (37 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((176877807899 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (37 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 894157128576053164862328192146386000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (37 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((315769356967 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (37 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 894158732718785843455495228736428000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (37 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((157884961733 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (37 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 500861974554129570191171411553790000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (37 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((35375631101 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (37 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 20818297314995981965905534671306000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (37 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((7351929707 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_38 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (38 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 5 else if k.val = 2 then -6 else -4) else if j.val = 1 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 7) else if j.val = 2 then (if k.val = 0 then (37 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -4) else if j.val = 3 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 7) else if j.val = 4 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (38 : Fin 88)), (alphaG (n3 1) (m3 1) (38 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 5 else if k.val = 2 then -6 else -4) else if j.val = 1 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 7) else if j.val = 2 then (if k.val = 0 then (37 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -4) else if j.val = 3 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 7) else if j.val = 4 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (6190568372096511075569 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (38 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (38 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (38 : Fin 88) = 38948654436342761089250000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (38 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 471754611411826303497954601912000000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (38 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((378506827 : ℚ)/31250000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (38 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12686507778552483624129802432000000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (38 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((1272359 : ℚ)/3906250000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (38 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 16711666230095387221195191160123000000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (38 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((107267288639 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (38 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 2278219698251559450690088103528750000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (38 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((11698579739 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (38 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 2278219894046445302185148099188500000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (38 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((29246451861 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (38 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 16711666618841907150332289591927250000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (38 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((429069164537 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 1 (38 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 12686668247008761356305490142000000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 1) (m3 1) (38 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((40716003 : ℚ)/125000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 1 (38 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 471754207670074416368893150746500000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 1) (m3 1) (38 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((6056104049 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_39 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (39 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 3 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else -1) else if j.val = 1 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 3 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then -2 else if k.val = 2 then 6 else 7) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (39 : Fin 88)), (alphaG (n3 1) (m3 1) (39 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 3 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else -1) else if j.val = 1 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 3 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then -2 else if k.val = 2 then 6 else 7) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3310034849146271626079104 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (39 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (39 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (39 : Fin 88) = 35562042575249745026250000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (39 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 383612115014864939129885709615000000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (39 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((2696780663 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (39 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 53402973671271267473831942220000000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (39 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((93855291 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (39 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 5814062792341252661986047903948750000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (39 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((163490687579 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (39 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 11122634698162054932751612010280000000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (39 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((9773969917 : ℚ)/31250000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (39 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 407308737916362006665661060697500000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (39 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((5726734299 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (39 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 407308101426923994845724580875000000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (39 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((114534507 : ℚ)/10000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 1 (39 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 11122636312572101721364286966951250000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 1) (m3 1) (39 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((312767082741 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 1 (39 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 5814062917164022101112652946086250000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 1) (m3 1) (39 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((163490691089 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 1 (39 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 53402751230694959286676803026250000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 1) (m3 1) (39 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((1501678401 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 1 (39 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 383611175750196441633620076300000000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 1) (m3 1) (39 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((134838703 : ℚ)/12500000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_40 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (40 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 3 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 3 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (40 : Fin 88)), (alphaG (n3 1) (m3 1) (40 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 3 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 3 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (888187667851191181564003 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (40 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (40 : Fin 88)))) =
        {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (40 : Fin 88) = 25781021993817692799460000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (40 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 42535543583218146742356745826000000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (40 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((16498781 : ℚ)/10000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (40 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 286175400351252957788221521148600000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (40 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((1110023491 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (40 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 312664681365635185576579108610280000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (40 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((6063853509 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (40 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 8085845786436264847321543871591360000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (40 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((19602223751 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (40 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 4163290128842667067928804507836240000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (40 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((40371655261 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (40 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 4163290020974871045795577834895600000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (40 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((8074330843 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 1 (40 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 8085849643741213518337105141197640000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 1) (m3 1) (40 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((156817864817 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 1 (40 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 312662579155320787688090547842420000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 1) (m3 1) (40 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((12127625477 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 1 (40 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 286173288498836334211915853382700000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 1) (m3 1) (40 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((2220030599 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  have hm9 : m3 1 (40 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 42534920868412908069804867669160000000000000000000000000 := by decide +kernel
  have ha9 : alphaG (n3 1) (m3 1) (40 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((824926973 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm9, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_41 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (41 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -8) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else -6) else if j.val = 1 then (if k.val = 0 then (33 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else -8) else if j.val = 2 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 8) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else -8) else if j.val = 4 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (41 : Fin 88)), (alphaG (n3 1) (m3 1) (41 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -8) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else -6) else if j.val = 1 then (if k.val = 0 then (33 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else -8) else if j.val = 2 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 8) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else -8) else if j.val = 4 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1286076114677344023760 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (41 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (41 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (41 : Fin 88) = 5887082376587153617382000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (41 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 1934866620215771419734756039178000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (41 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((328663079 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (41 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 74875204980128027792185760224268000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (41 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((6359279537 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (41 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 398952555249893223090531177699762000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (41 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((67767449091 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (41 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 2467778515035469411752016340214486000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (41 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((419185320873 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (41 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 2467778692001165651961854078717406000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (41 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((419185350933 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (41 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 398952762957933633838485106171486000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (41 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((67767484373 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 1 (41 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 74874938807472535157209257531902000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 1) (m3 1) (41 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((12718513861 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 1 (41 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 1934840934875362369983523401512000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 1) (m3 1) (41 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((82164679 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_42 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (42 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 5 else -8) else if j.val = 1 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -1) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 2) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else 5) else if j.val = 2 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 5 else if k.val = 2 then -4 else 1) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -5 else if k.val = 2 then -1 else 2) else if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 5 else if k.val = 2 then -4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (42 : Fin 88)), (alphaG (n3 1) (m3 1) (42 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 5 else -8) else if j.val = 1 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -1) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 2) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else 5) else if j.val = 2 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 5 else if k.val = 2 then -4 else 1) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -5 else if k.val = 2 then -1 else 2) else if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 5 else if k.val = 2 then -4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (10989399414881096396302 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (42 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (42 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (42 : Fin 88) = 18561628792168432026484000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (42 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 6098850298430332514427543676292000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (42 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((328573013 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (42 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 737812063889246257682378923137592000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (42 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((19874658419 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (42 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 687697794556680202788467303978420000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (42 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((7409886301 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (42 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 2678753333801844558467241027225256000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (42 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((72158358617 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (42 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 10340904678008518635043205850490936000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (42 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((278555960627 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (42 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) = 2678753314423504099443397991575960000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (42 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) =
      ((14431671619 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 1 (42 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 687698522228213742167508038230672000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 1) (m3 1) (42 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((9262367677 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 1 (42 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 737812838688755300377068572632720000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 1) (m3 1) (42 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((1987467929 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  have hm8 : m3 1 (42 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 6097396273238898000304749052152000000000000000000000000 := by decide +kernel
  have ha8 : alphaG (n3 1) (m3 1) (42 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((164247339 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm8, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_43 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (43 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else 3) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else -3) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -1) else if j.val = 2 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (43 : Fin 88)), (alphaG (n3 1) (m3 1) (43 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else 3) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else -3) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -1) else if j.val = 2 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (10250594126870920754019 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (43 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (43 : Fin 88)))) =
        {(⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (43 : Fin 88) = 469860220723925525436000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (43 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 3360646380250045313101579280472000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (43 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((3576219301 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (43 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) = 82614185957170232362764225972432000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (43 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) =
      ((43956788803 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (43 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 148955270561752599284025074247108000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (43 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((317020390303 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (43 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 148955265561030270119285707031760000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (43 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((15851018983 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (43 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 82614203918047029755541361288968000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (43 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((87913596719 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (43 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 3360648345675348601282052179260000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (43 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((1430488557 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_44 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (44 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -5 else if k.val = 2 then 0 else -8) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (44 : Fin 88)), (alphaG (n3 1) (m3 1) (44 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -5 else if k.val = 2 then 0 else -8) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2122151178821023883402 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (44 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (44 : Fin 88)))) =
        {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (44 : Fin 88) = 110287419028478157012000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (44 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) = 12875036679305397178263663666504000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (44 : Fin 88) (⟨![2,1,1], by decide +kernel⟩) =
      ((58370378021 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (44 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) = 42268675297651748233653582411456000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (44 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) =
      ((23953704143 : ℚ)/62500000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (44 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) = 42268675311106813355127917566920000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (44 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) =
      ((38325926641 : ℚ)/100000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (44 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) = 12875031740414198244954836355120000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (44 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) =
      ((5837035563 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_45 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (45 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else 1) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 2) else if j.val = 4 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (45 : Fin 88)), (alphaG (n3 1) (m3 1) (45 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else 1) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 2) else if j.val = 4 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (6931496288506364188011 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (45 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (45 : Fin 88)))) =
        {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (45 : Fin 88) = 110188257316306301420000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (45 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 42201699844807346135577767996180000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (45 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((382996345279 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (45 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 12923697809027521589201461965840000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (45 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((29321858163 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (45 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 12908560559773937137609931595100000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (45 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((23430011281 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (45 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 42154299102697496557610838442880000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (45 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((11955192677 : ℚ)/31250000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_46 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (46 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else 2) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else -6) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else 2) else if j.val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (46 : Fin 88)), (alphaG (n3 1) (m3 1) (46 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else 2) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else -6) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else 2) else if j.val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3624605509608328572250 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (46 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (46 : Fin 88)))) =
        {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (46 : Fin 88) = 520541098375637167186000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (46 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 91509086336924622790262153306168000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (46 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((43949020847 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (46 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 165021865582119863365805102578770000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (46 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((63403971789 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (46 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) = 3739651921945639190205838474760000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (46 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) =
      ((359208133 : ℚ)/50000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (46 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 3739606195012852382358887020590000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (46 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((1436814963 : ℚ)/200000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (46 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 165021802788726625214317987764404000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (46 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((158509869157 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (46 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 91509085550907564243050030855308000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (46 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((87898040939 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem pn_1_47 :
    ((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (47 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -8) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -8) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -1) else if j.val = 1 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else -4) else if j.val = 2 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 8) else if j.val = 3 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else -4) else if j.val = 4 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -4 else if k.val = 2 then 5 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (47 : Fin 88)), (alphaG (n3 1) (m3 1) (47 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -8) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -8) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -1) else if j.val = 1 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else -4) else if j.val = 2 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 8) else if j.val = 3 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else -4) else if j.val = 4 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -4 else if k.val = 2 then 5 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3368988338457544557181 : ℚ)/10^30 := by
  have hsp : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (47 : Fin 88)) → ℚ,
      ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
    have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (47 : Fin 88)))) =
        {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by decide +kernel
    intro g
    rw [hu]
    rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
    ring
  have hn : n3 1 (47 : Fin 88) = 10218134039343253602246000000000000000000000000000000000000 := by decide +kernel
  have hm0 : m3 1 (47 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) = 3374002508600590728849442027674000000000000000000000000 := by decide +kernel
  have ha0 : alphaG (n3 1) (m3 1) (47 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) =
      ((330197519 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm0, hn]
    norm_num
  have hm1 : m3 1 (47 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) = 692587403125525253991102682303026000000000000000000000000 := by decide +kernel
  have ha1 : alphaG (n3 1) (m3 1) (47 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) =
      ((67780222931 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm1, hn]
    norm_num
  have hm2 : m3 1 (47 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) = 4282586629281577904328638690498712000000000000000000000000 := by decide +kernel
  have ha2 : alphaG (n3 1) (m3 1) (47 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) =
      ((104779077393 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm2, hn]
    norm_num
  have hm3 : m3 1 (47 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) = 130517516369189062291493528011404000000000000000000000000 := by decide +kernel
  have ha3 : alphaG (n3 1) (m3 1) (47 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) =
      ((6386563137 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm3, hn]
    norm_num
  have hm4 : m3 1 (47 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) = 130520554721127526968608902257258000000000000000000000000 := by decide +kernel
  have ha4 : alphaG (n3 1) (m3 1) (47 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) =
      ((12773423623 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm4, hn]
    norm_num
  have hm5 : m3 1 (47 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) = 4282584423309056418592305008814264000000000000000000000000 := by decide +kernel
  have ha5 : alphaG (n3 1) (m3 1) (47 : Fin 88) (⟨![1,1,2], by decide +kernel⟩) =
      ((104779023421 : ℚ)/250000000000) := by
    unfold alphaG
    rw [hm5, hn]
    norm_num
  have hm6 : m3 1 (47 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) = 692589892906719682486305166370124000000000000000000000000 := by decide +kernel
  have ha6 : alphaG (n3 1) (m3 1) (47 : Fin 88) (⟨![1,2,1], by decide +kernel⟩) =
      ((33890233297 : ℚ)/500000000000) := by
    unfold alphaG
    rw [hm6, hn]
    norm_num
  have hm7 : m3 1 (47 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) = 3373617121457162858696579717538000000000000000000000000 := by decide +kernel
  have ha7 : alphaG (n3 1) (m3 1) (47 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) =
      ((330159803 : ℚ)/1000000000000) := by
    unfold alphaG
    rw [hm7, hn]
    norm_num
  simp only [hsp, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, Fin.sum_univ_three]
  norm_num [qvalQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    (((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (32 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 5 else if k.val = 2 then -3 else -5) else if j.val = 1 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 8) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 8) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (32 : Fin 88)), (alphaG (n3 1) (m3 1) (32 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 5 else if k.val = 2 then -3 else -5) else if j.val = 1 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 8) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 8) else if j.val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5010086535956937448418 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (33 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else -1) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else -5) else if j.val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 6 else if k.val = 2 then 5 else -3) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 4 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 6 else if k.val = 2 then 5 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (33 : Fin 88)), (alphaG (n3 1) (m3 1) (33 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else -1) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else -5) else if j.val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 6 else if k.val = 2 then 5 else -3) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -5 else -2) else if j.val = 4 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 6 else if k.val = 2 then 5 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (5606419870025608398041 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (34 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -1 else -6) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 0) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (34 : Fin 88)), (alphaG (n3 1) (m3 1) (34 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -1 else -6) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 0) else if j.val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (11022741169134187954360 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (35 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else 7) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 4 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (35 : Fin 88)), (alphaG (n3 1) (m3 1) (35 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 3) else if j.val = 1 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else 7) else if j.val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 3 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else 2) else if j.val = 4 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (518382528218507735864 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (36 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else -4) else if j.val = 1 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 2) else if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else -1) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 1 else 1) else if j.val = 1 then (if k.val = 0 then (20 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -7) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 1 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (36 : Fin 88)), (alphaG (n3 1) (m3 1) (36 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else -4) else if j.val = 1 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 2) else if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -5 else if k.val = 2 then 5 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else -1) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 0 else 0) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 1 else 1) else if j.val = 1 then (if k.val = 0 then (20 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -7) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 1 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (13706571043332992359788 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (37 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 5) else if j.val = 1 then (if k.val = 0 then (-47 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else 8) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (37 : Fin 88)), (alphaG (n3 1) (m3 1) (37 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 5) else if j.val = 1 then (if k.val = 0 then (-47 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else 8) else if j.val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 1 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 1) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -6) else if j.val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (10838749761778335214263 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (38 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 5 else if k.val = 2 then -6 else -4) else if j.val = 1 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 7) else if j.val = 2 then (if k.val = 0 then (37 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -4) else if j.val = 3 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 7) else if j.val = 4 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (38 : Fin 88)), (alphaG (n3 1) (m3 1) (38 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else -7) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 5 else if k.val = 2 then -6 else -4) else if j.val = 1 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 7) else if j.val = 2 then (if k.val = 0 then (37 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -4) else if j.val = 3 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 7) else if j.val = 4 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (6190568372096511075569 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (39 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 3 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else -1) else if j.val = 1 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 3 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then -2 else if k.val = 2 then 6 else 7) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (39 : Fin 88)), (alphaG (n3 1) (m3 1) (39 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -4) else if j.val = 3 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else -1) else if j.val = 1 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if j.val = 3 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else if j.val = 1 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then -2 else if k.val = 2 then 6 else 7) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3310034849146271626079104 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (40 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 3 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 3 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (40 : Fin 88)), (alphaG (n3 1) (m3 1) (40 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -7) else if j.val = 3 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else if j.val = 1 then (if k.val = 0 then (23 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -8) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 1) else if j.val = 3 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (888187667851191181564003 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (41 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -8) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else -6) else if j.val = 1 then (if k.val = 0 then (33 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else -8) else if j.val = 2 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 8) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else -8) else if j.val = 4 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (41 : Fin 88)), (alphaG (n3 1) (m3 1) (41 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -8) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -7) else if j.val = 3 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else -6) else if j.val = 1 then (if k.val = 0 then (33 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else -8) else if j.val = 2 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 8) else if j.val = 3 then (if k.val = 0 then (33 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else -8) else if j.val = 4 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 4 else if k.val = 2 then -8 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (1286076114677344023760 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (42 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 5 else -8) else if j.val = 1 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -1) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 2) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else 5) else if j.val = 2 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 5 else if k.val = 2 then -4 else 1) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -5 else if k.val = 2 then -1 else 2) else if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 5 else if k.val = 2 then -4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (42 : Fin 88)), (alphaG (n3 1) (m3 1) (42 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then 5 else -8) else if j.val = 1 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -1) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 2) else if j.val = 1 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else 5) else if j.val = 2 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -7 else if k.val = 2 then -6 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 5 else if k.val = 2 then -4 else 1) else if j.val = 1 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -5 else if k.val = 2 then -1 else 2) else if j.val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 5 else if k.val = 2 then -4 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (10989399414881096396302 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (43 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else 3) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else -3) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -1) else if j.val = 2 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (43 : Fin 88)), (alphaG (n3 1) (m3 1) (43 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 1 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else 3) else if j.val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else -3) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -1) else if j.val = 2 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (10250594126870920754019 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (44 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -5 else if k.val = 2 then 0 else -8) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (44 : Fin 88)), (alphaG (n3 1) (m3 1) (44 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else if j.val = 3 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -5 else if k.val = 2 then 0 else -8) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (2122151178821023883402 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (45 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else 1) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 2) else if j.val = 4 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (45 : Fin 88)), (alphaG (n3 1) (m3 1) (45 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else 1) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 2) else if j.val = 4 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (6931496288506364188011 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (46 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else 2) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else -6) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else 2) else if j.val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (46 : Fin 88)), (alphaG (n3 1) (m3 1) (46 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 1 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else 2) else if j.val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 3 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 4) else if j.val = 4 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else -6) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else 2) else if j.val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3624605509608328572250 : ℚ)/10^30) ∧
(((∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (47 : Fin 88)), qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -8) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -8) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -1) else if j.val = 1 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else -4) else if j.val = 2 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 8) else if j.val = 3 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else -4) else if j.val = 4 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -4 else if k.val = 2 then 5 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) - 2 +
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (47 : Fin 88)), (alphaG (n3 1) (m3 1) (47 : Fin 88) c) ^ 2 /
        qvalQ (fun k ↦ ∑ i, (fun (i : Fin 3) (j : Fin (2 * 2 ^ (2 - 1) + 1)) (k : Fin 4) => if i.val = 0 then (if j.val = 0 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else if i.val = 1 then (if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -2) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -8) else if j.val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else -8) else if j.val = 3 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) else (if j.val = 0 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -6 else -1) else if j.val = 1 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else -4) else if j.val = 2 then (if k.val = 0 then (-38 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 8) else if j.val = 3 then (if k.val = 0 then (28 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else -4) else if j.val = 4 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -4 else if k.val = 2 then 5 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) i (c.val i) k)) ≤ (3368988338457544557181 : ℚ)/10^30) :=
  ⟨L3C.pn_1_32, L3C.pn_1_33, L3C.pn_1_34, L3C.pn_1_35, L3C.pn_1_36, L3C.pn_1_37, L3C.pn_1_38, L3C.pn_1_39, L3C.pn_1_40, L3C.pn_1_41, L3C.pn_1_42, L3C.pn_1_43, L3C.pn_1_44, L3C.pn_1_45, L3C.pn_1_46, L3C.pn_1_47⟩

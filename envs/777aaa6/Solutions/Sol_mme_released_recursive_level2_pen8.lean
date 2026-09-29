-- Prove2me | solution 1 for mme_released_recursive_level2_pen8
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T03:44:02.288981+00:00
-- url     : https://prove2.me/submissions/b880cdd2-2912-471e-b4b6-b72abd2d36e9

import Mathlib
import Definitions.Def_mme_released_recursive_level2_penalty_data
import Definitions.Def_mme_released_recursive_level2_cert_data
import Definitions.Def_mme_released_recursive_level2_split_data
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_certified_entropy_rational_data
import Theorems.Thm_mme_released_recursive_level2_marginals
import Theorems.Thm_mme_released_recursive_level2_penalty_tools

open BigOperators MME MME.RecursiveYZ MME.RecStage MME.Cert MME.L2Cert MME.RegionRate
  MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace MME.L2Cert

theorem alphaQ_jwv (r : Fin 1104)
    (c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r)) :
    alphaQ r c = (jwv r c.val : ℚ) / (D : ℚ) :=
  (mme_released_recursive_level2_penalty_tools.1 r c).2

theorem PE_sum (r : Fin 1104) (a : Tri) (k : Fin 4) :
    ∑ i, PE r i (a i) k = PE r (certMode r) (a (certMode r)) k :=
  mme_released_recursive_level2_penalty_tools.2.2.1 r a k

theorem sum_triP (g : Tri → ℚ) :
    ∑ a : Tri, g a = ∑ x : Fin 3, ∑ y : Fin 3, ∑ z : Fin 3, g ![x, y, z] :=
  mme_released_recursive_level2_penalty_tools.2.2.2.1 g

theorem jwv_112 (r : Fin 1104) (hp : parent2 r = ![1, 1, 2]) :
    jwv r ![0, 0, 2] = (l2At r).2.2 ∧ jwv r ![0, 1, 1] = D / 2 - (l2At r).2.2 ∧
      jwv r ![1, 0, 1] = D / 2 - (l2At r).2.2 ∧ jwv r ![1, 1, 0] = (l2At r).2.2 :=
  mme_released_recursive_level2_penalty_tools.2.2.2.2.1 r hp

theorem jwv_121 (r : Fin 1104) (hp : parent2 r = ![1, 2, 1]) :
    jwv r ![0, 1, 1] = D / 2 - (l2At r).2.2 ∧ jwv r ![0, 2, 0] = (l2At r).2.2 ∧
      jwv r ![1, 0, 1] = (l2At r).2.2 ∧ jwv r ![1, 1, 0] = D / 2 - (l2At r).2.2 :=
  mme_released_recursive_level2_penalty_tools.2.2.2.2.2.1 r hp

theorem jwv_211 (r : Fin 1104) (hp : parent2 r = ![2, 1, 1]) :
    jwv r ![0, 1, 1] = (l2At r).2.2 ∧ jwv r ![1, 0, 1] = D / 2 - (l2At r).2.2 ∧
      jwv r ![1, 1, 0] = D / 2 - (l2At r).2.2 ∧ jwv r ![2, 0, 0] = (l2At r).2.2 :=
  mme_released_recursive_level2_penalty_tools.2.2.2.2.2.2.1 r hp

end MME.L2Cert

namespace MME.L2Cert

theorem pcert_368 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 368),
        qvalQ (fun t ↦ ∑ i, PE 368 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 368),
        (alphaQ 368 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 368 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 368 = 2 := by decide +kernel
  have hce : certE (368 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -12 else if j.val = 1 then -6 else if j.val = 2 then -8 else 7)) := by decide +kernel
  have hs : (l2At (368 : Fin 1104)).2.2 = 706013 := by decide +kernel
  have hp : parent2 (368 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 368 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 368 c] :
    ∀ c ∈ Finset.univ, (alphaQ 368 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 368 i (c.val i) t) =
      ((jwv 368 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 368 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 368 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 368 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 368 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_369 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 369),
        qvalQ (fun t ↦ ∑ i, PE 369 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 369),
        (alphaQ 369 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 369 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 369 = 2 := by decide +kernel
  have hce : certE (369 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -22 else if j.val = 1 then 4 else if j.val = 2 then 4 else -5)) := by decide +kernel
  have hs : (l2At (369 : Fin 1104)).2.2 = 718182 := by decide +kernel
  have hp : parent2 (369 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 369 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 369 c] :
    ∀ c ∈ Finset.univ, (alphaQ 369 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 369 i (c.val i) t) =
      ((jwv 369 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 369 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 369 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 369 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 369 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_370 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 370),
        qvalQ (fun t ↦ ∑ i, PE 370 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 370),
        (alphaQ 370 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 370 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 370 = 2 := by decide +kernel
  have hce : certE (370 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -12 else if j.val = 1 then -6 else if j.val = 2 then -8 else 7)) := by decide +kernel
  have hs : (l2At (370 : Fin 1104)).2.2 = 706027 := by decide +kernel
  have hp : parent2 (370 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 370 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 370 c] :
    ∀ c ∈ Finset.univ, (alphaQ 370 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 370 i (c.val i) t) =
      ((jwv 370 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 370 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 370 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 370 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 370 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_371 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 371),
        qvalQ (fun t ↦ ∑ i, PE 371 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 371),
        (alphaQ 371 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 371 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 371 = 2 := by decide +kernel
  have hce : certE (371 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -22 else if j.val = 1 then -7 else if j.val = 2 then -3 else 7)) := by decide +kernel
  have hs : (l2At (371 : Fin 1104)).2.2 = 718228 := by decide +kernel
  have hp : parent2 (371 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 371 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 371 c] :
    ∀ c ∈ Finset.univ, (alphaQ 371 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 371 i (c.val i) t) =
      ((jwv 371 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 371 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 371 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 371 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 371 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_372 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 372),
        qvalQ (fun t ↦ ∑ i, PE 372 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 372),
        (alphaQ 372 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 372 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 372 = 2 := by decide +kernel
  have hce : certE (372 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -8 else if j.val = 1 then 4 else if j.val = 2 then -1 else -6)) := by decide +kernel
  have hs : (l2At (372 : Fin 1104)).2.2 = 537850 := by decide +kernel
  have hp : parent2 (372 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 372 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 372 c] :
    ∀ c ∈ Finset.univ, (alphaQ 372 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 372 i (c.val i) t) =
      ((jwv 372 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 372 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 372 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 372 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 372 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_373 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 373),
        qvalQ (fun t ↦ ∑ i, PE 373 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 373),
        (alphaQ 373 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 373 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 373 = 2 := by decide +kernel
  have hce : certE (373 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -8 else if j.val = 1 then 4 else if j.val = 2 then -1 else -6)) := by decide +kernel
  have hs : (l2At (373 : Fin 1104)).2.2 = 537851 := by decide +kernel
  have hp : parent2 (373 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 373 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 373 c] :
    ∀ c ∈ Finset.univ, (alphaQ 373 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 373 i (c.val i) t) =
      ((jwv 373 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 373 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 373 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 373 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 373 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_374 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 374),
        qvalQ (fun t ↦ ∑ i, PE 374 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 374),
        (alphaQ 374 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 374 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 374 = 2 := by decide +kernel
  have hce : certE (374 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (374 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (374 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 374 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 374 c] :
    ∀ c ∈ Finset.univ, (alphaQ 374 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 374 i (c.val i) t) =
      ((jwv 374 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 374 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 374 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 374 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 374 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_375 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 375),
        qvalQ (fun t ↦ ∑ i, PE 375 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 375),
        (alphaQ 375 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 375 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 375 = 1 := by decide +kernel
  have hce : certE (375 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (375 : Fin 1104)).2.2 = 21076398884 := by decide +kernel
  have hp : parent2 (375 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 375 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 375 c] :
    ∀ c ∈ Finset.univ, (alphaQ 375 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 375 i (c.val i) t) =
      ((jwv 375 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 375 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 375 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 375 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 375 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_376 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 376),
        qvalQ (fun t ↦ ∑ i, PE 376 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 376),
        (alphaQ 376 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 376 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 376 = 2 := by decide +kernel
  have hce : certE (376 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (376 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (376 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 376 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 376 c] :
    ∀ c ∈ Finset.univ, (alphaQ 376 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 376 i (c.val i) t) =
      ((jwv 376 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 376 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 376 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 376 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 376 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_377 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 377),
        qvalQ (fun t ↦ ∑ i, PE 377 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 377),
        (alphaQ 377 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 377 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 377 = 1 := by decide +kernel
  have hce : certE (377 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (377 : Fin 1104)).2.2 = 21076343901 := by decide +kernel
  have hp : parent2 (377 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 377 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 377 c] :
    ∀ c ∈ Finset.univ, (alphaQ 377 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 377 i (c.val i) t) =
      ((jwv 377 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 377 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 377 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 377 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 377 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_378 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 378),
        qvalQ (fun t ↦ ∑ i, PE 378 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 378),
        (alphaQ 378 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 378 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 378 = 2 := by decide +kernel
  have hce : certE (378 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (378 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (378 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 378 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 378 c] :
    ∀ c ∈ Finset.univ, (alphaQ 378 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 378 i (c.val i) t) =
      ((jwv 378 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 378 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 378 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 378 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 378 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_379 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 379),
        qvalQ (fun t ↦ ∑ i, PE 379 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 379),
        (alphaQ 379 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 379 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 379 = 1 := by decide +kernel
  have hce : certE (379 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (379 : Fin 1104)).2.2 = 21076125716 := by decide +kernel
  have hp : parent2 (379 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 379 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 379 c] :
    ∀ c ∈ Finset.univ, (alphaQ 379 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 379 i (c.val i) t) =
      ((jwv 379 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 379 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 379 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 379 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 379 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_380 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 380),
        qvalQ (fun t ↦ ∑ i, PE 380 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 380),
        (alphaQ 380 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 380 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 380 = 2 := by decide +kernel
  have hce : certE (380 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (9 : Int) else if j.val = 1 then -5 else if j.val = 2 then 8 else -7) else (if j.val = 0 then -5 else if j.val = 1 then -2 else if j.val = 2 then -4 else 2)) := by decide +kernel
  have hs : (l2At (380 : Fin 1104)).2.2 = 272209549 := by decide +kernel
  have hp : parent2 (380 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 380 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 380 c] :
    ∀ c ∈ Finset.univ, (alphaQ 380 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 380 i (c.val i) t) =
      ((jwv 380 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 380 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 380 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 380 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 380 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_381 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 381),
        qvalQ (fun t ↦ ∑ i, PE 381 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 381),
        (alphaQ 381 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 381 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 381 = 1 := by decide +kernel
  have hce : certE (381 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (381 : Fin 1104)).2.2 = 21076587467 := by decide +kernel
  have hp : parent2 (381 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 381 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 381 c] :
    ∀ c ∈ Finset.univ, (alphaQ 381 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 381 i (c.val i) t) =
      ((jwv 381 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 381 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 381 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 381 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 381 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_382 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 382),
        qvalQ (fun t ↦ ∑ i, PE 382 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 382),
        (alphaQ 382 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 382 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 382 = 2 := by decide +kernel
  have hce : certE (382 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (9 : Int) else if j.val = 1 then -5 else if j.val = 2 then 8 else -7) else (if j.val = 0 then -1 else if j.val = 1 then -8 else if j.val = 2 then 2 else -1)) := by decide +kernel
  have hs : (l2At (382 : Fin 1104)).2.2 = 272183611 := by decide +kernel
  have hp : parent2 (382 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 382 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 382 c] :
    ∀ c ∈ Finset.univ, (alphaQ 382 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 382 i (c.val i) t) =
      ((jwv 382 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 382 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 382 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 382 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 382 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_383 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 383),
        qvalQ (fun t ↦ ∑ i, PE 383 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 383),
        (alphaQ 383 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 383 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 383 = 1 := by decide +kernel
  have hce : certE (383 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (383 : Fin 1104)).2.2 = 21076605989 := by decide +kernel
  have hp : parent2 (383 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 383 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 383 c] :
    ∀ c ∈ Finset.univ, (alphaQ 383 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 383 i (c.val i) t) =
      ((jwv 383 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 383 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 383 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 383 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 383 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_384 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 384),
        qvalQ (fun t ↦ ∑ i, PE 384 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 384),
        (alphaQ 384 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 384 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 384 = 2 := by decide +kernel
  have hce : certE (384 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then -17 else if j.val = 1 then 2 else if j.val = 2 then 5 else -3)) := by decide +kernel
  have hs : (l2At (384 : Fin 1104)).2.2 = 625637903 := by decide +kernel
  have hp : parent2 (384 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 384 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 384 c] :
    ∀ c ∈ Finset.univ, (alphaQ 384 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 384 i (c.val i) t) =
      ((jwv 384 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 384 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 384 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 384 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 384 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_385 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 385),
        qvalQ (fun t ↦ ∑ i, PE 385 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 385),
        (alphaQ 385 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 385 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 385 = 1 := by decide +kernel
  have hce : certE (385 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (385 : Fin 1104)).2.2 = 21076589974 := by decide +kernel
  have hp : parent2 (385 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 385 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 385 c] :
    ∀ c ∈ Finset.univ, (alphaQ 385 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 385 i (c.val i) t) =
      ((jwv 385 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 385 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 385 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 385 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 385 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_386 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 386),
        qvalQ (fun t ↦ ∑ i, PE 386 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 386),
        (alphaQ 386 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 386 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 386 = 2 := by decide +kernel
  have hce : certE (386 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hs : (l2At (386 : Fin 1104)).2.2 = 20922602514 := by decide +kernel
  have hp : parent2 (386 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 386 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 386 c] :
    ∀ c ∈ Finset.univ, (alphaQ 386 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 386 i (c.val i) t) =
      ((jwv 386 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 386 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 386 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 386 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 386 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_387 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 387),
        qvalQ (fun t ↦ ∑ i, PE 387 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 387),
        (alphaQ 387 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 387 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 387 = 1 := by decide +kernel
  have hce : certE (387 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (22 : Int) else if j.val = 1 then 7 else if j.val = 2 then -7 else -6) else (if j.val = 0 then -14 else if j.val = 1 then -6 else if j.val = 2 then 1 else 4)) := by decide +kernel
  have hs : (l2At (387 : Fin 1104)).2.2 = 1005152886 := by decide +kernel
  have hp : parent2 (387 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 387 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 387 c] :
    ∀ c ∈ Finset.univ, (alphaQ 387 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 387 i (c.val i) t) =
      ((jwv 387 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 387 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 387 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 387 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 387 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_388 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 388),
        qvalQ (fun t ↦ ∑ i, PE 388 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 388),
        (alphaQ 388 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 388 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 388 = 2 := by decide +kernel
  have hce : certE (388 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hs : (l2At (388 : Fin 1104)).2.2 = 20922613006 := by decide +kernel
  have hp : parent2 (388 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 388 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 388 c] :
    ∀ c ∈ Finset.univ, (alphaQ 388 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 388 i (c.val i) t) =
      ((jwv 388 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 388 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 388 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 388 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 388 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_389 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 389),
        qvalQ (fun t ↦ ∑ i, PE 389 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 389),
        (alphaQ 389 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 389 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 389 = 1 := by decide +kernel
  have hce : certE (389 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (22 : Int) else if j.val = 1 then 7 else if j.val = 2 then -7 else -6) else (if j.val = 0 then -18 else if j.val = 1 then 0 else if j.val = 2 then -5 else 7)) := by decide +kernel
  have hs : (l2At (389 : Fin 1104)).2.2 = 1005218206 := by decide +kernel
  have hp : parent2 (389 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 389 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 389 c] :
    ∀ c ∈ Finset.univ, (alphaQ 389 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 389 i (c.val i) t) =
      ((jwv 389 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 389 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 389 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 389 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 389 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_390 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 390),
        qvalQ (fun t ↦ ∑ i, PE 390 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 390),
        (alphaQ 390 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 390 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 390 = 2 := by decide +kernel
  have hce : certE (390 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hs : (l2At (390 : Fin 1104)).2.2 = 20922592442 := by decide +kernel
  have hp : parent2 (390 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 390 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 390 c] :
    ∀ c ∈ Finset.univ, (alphaQ 390 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 390 i (c.val i) t) =
      ((jwv 390 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 390 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 390 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 390 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 390 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_391 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 391),
        qvalQ (fun t ↦ ∑ i, PE 391 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 391),
        (alphaQ 391 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 391 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 391 = 1 := by decide +kernel
  have hce : certE (391 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-6 : Int) else if j.val = 1 then 0 else if j.val = 2 then 5 else -2) else (if j.val = 0 then -16 else if j.val = 1 then 7 else if j.val = 2 then 3 else -4)) := by decide +kernel
  have hs : (l2At (391 : Fin 1104)).2.2 = 1737369556 := by decide +kernel
  have hp : parent2 (391 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 391 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 391 c] :
    ∀ c ∈ Finset.univ, (alphaQ 391 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 391 i (c.val i) t) =
      ((jwv 391 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 391 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 391 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 391 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 391 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_392 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 392),
        qvalQ (fun t ↦ ∑ i, PE 392 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 392),
        (alphaQ 392 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 392 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 392 = 2 := by decide +kernel
  have hce : certE (392 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (392 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (392 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 392 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 392 c] :
    ∀ c ∈ Finset.univ, (alphaQ 392 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 392 i (c.val i) t) =
      ((jwv 392 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 392 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 392 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 392 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 392 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_393 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 393),
        qvalQ (fun t ↦ ∑ i, PE 393 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 393),
        (alphaQ 393 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 393 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 393 = 1 := by decide +kernel
  have hce : certE (393 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (393 : Fin 1104)).2.2 = 21076589485 := by decide +kernel
  have hp : parent2 (393 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 393 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 393 c] :
    ∀ c ∈ Finset.univ, (alphaQ 393 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 393 i (c.val i) t) =
      ((jwv 393 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 393 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 393 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 393 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 393 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_394 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 394),
        qvalQ (fun t ↦ ∑ i, PE 394 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 394),
        (alphaQ 394 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 394 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 394 = 2 := by decide +kernel
  have hce : certE (394 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 17 else if j.val = 1 then -3 else if j.val = 2 then 2 else -8)) := by decide +kernel
  have hs : (l2At (394 : Fin 1104)).2.2 = 21054211020 := by decide +kernel
  have hp : parent2 (394 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 394 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 394 c] :
    ∀ c ∈ Finset.univ, (alphaQ 394 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 394 i (c.val i) t) =
      ((jwv 394 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 394 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 394 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 394 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 394 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_395 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 395),
        qvalQ (fun t ↦ ∑ i, PE 395 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 395),
        (alphaQ 395 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 395 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 395 = 1 := by decide +kernel
  have hce : certE (395 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (395 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (395 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 395 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 395 c] :
    ∀ c ∈ Finset.univ, (alphaQ 395 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 395 i (c.val i) t) =
      ((jwv 395 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 395 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 395 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 395 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 395 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_396 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 396),
        qvalQ (fun t ↦ ∑ i, PE 396 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 396),
        (alphaQ 396 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 396 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 396 = 2 := by decide +kernel
  have hce : certE (396 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (396 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (396 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 396 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 396 c] :
    ∀ c ∈ Finset.univ, (alphaQ 396 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 396 i (c.val i) t) =
      ((jwv 396 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 396 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 396 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 396 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 396 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_397 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 397),
        qvalQ (fun t ↦ ∑ i, PE 397 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 397),
        (alphaQ 397 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 397 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 397 = 1 := by decide +kernel
  have hce : certE (397 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (397 : Fin 1104)).2.2 = 21076590819 := by decide +kernel
  have hp : parent2 (397 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 397 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 397 c] :
    ∀ c ∈ Finset.univ, (alphaQ 397 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 397 i (c.val i) t) =
      ((jwv 397 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 397 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 397 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 397 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 397 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_398 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 398),
        qvalQ (fun t ↦ ∑ i, PE 398 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 398),
        (alphaQ 398 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 398 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 398 = 2 := by decide +kernel
  have hce : certE (398 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 17 else if j.val = 1 then -3 else if j.val = 2 then 2 else -8)) := by decide +kernel
  have hs : (l2At (398 : Fin 1104)).2.2 = 21054193374 := by decide +kernel
  have hp : parent2 (398 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 398 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 398 c] :
    ∀ c ∈ Finset.univ, (alphaQ 398 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 398 i (c.val i) t) =
      ((jwv 398 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 398 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 398 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 398 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 398 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_399 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 399),
        qvalQ (fun t ↦ ∑ i, PE 399 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 399),
        (alphaQ 399 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 399 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 399 = 1 := by decide +kernel
  have hce : certE (399 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (399 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (399 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 399 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 399 c] :
    ∀ c ∈ Finset.univ, (alphaQ 399 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 399 i (c.val i) t) =
      ((jwv 399 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 399 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 399 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 399 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 399 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_400 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 400),
        qvalQ (fun t ↦ ∑ i, PE 400 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 400),
        (alphaQ 400 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 400 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 400 = 2 := by decide +kernel
  have hce : certE (400 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 17 else if j.val = 1 then -3 else if j.val = 2 then 2 else -8)) := by decide +kernel
  have hs : (l2At (400 : Fin 1104)).2.2 = 21054205378 := by decide +kernel
  have hp : parent2 (400 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 400 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 400 c] :
    ∀ c ∈ Finset.univ, (alphaQ 400 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 400 i (c.val i) t) =
      ((jwv 400 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 400 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 400 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 400 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 400 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_401 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 401),
        qvalQ (fun t ↦ ∑ i, PE 401 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 401),
        (alphaQ 401 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 401 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 401 = 1 := by decide +kernel
  have hce : certE (401 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (21 : Int) else if j.val = 1 then -3 else if j.val = 2 then -7 else 0) else (if j.val = 0 then -37 else if j.val = 1 then -2 else if j.val = 2 then 4 else 8)) := by decide +kernel
  have hs : (l2At (401 : Fin 1104)).2.2 = 2913165353 := by decide +kernel
  have hp : parent2 (401 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 401 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 401 c] :
    ∀ c ∈ Finset.univ, (alphaQ 401 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 401 i (c.val i) t) =
      ((jwv 401 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 401 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 401 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 401 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 401 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_402 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 402),
        qvalQ (fun t ↦ ∑ i, PE 402 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 402),
        (alphaQ 402 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 402 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 402 = 1 := by decide +kernel
  have hce : certE (402 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (402 : Fin 1104)).2.2 = 21076016665 := by decide +kernel
  have hp : parent2 (402 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 402 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 402 c] :
    ∀ c ∈ Finset.univ, (alphaQ 402 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 402 i (c.val i) t) =
      ((jwv 402 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 402 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 402 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 402 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 402 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_403 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 403),
        qvalQ (fun t ↦ ∑ i, PE 403 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 403),
        (alphaQ 403 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 403 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 403 = 1 := by decide +kernel
  have hce : certE (403 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (403 : Fin 1104)).2.2 = 21076020768 := by decide +kernel
  have hp : parent2 (403 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 403 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 403 c] :
    ∀ c ∈ Finset.univ, (alphaQ 403 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 403 i (c.val i) t) =
      ((jwv 403 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 403 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 403 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 403 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 403 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_404 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 404),
        qvalQ (fun t ↦ ∑ i, PE 404 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 404),
        (alphaQ 404 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 404 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 404 = 1 := by decide +kernel
  have hce : certE (404 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (404 : Fin 1104)).2.2 = 21076016128 := by decide +kernel
  have hp : parent2 (404 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 404 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 404 c] :
    ∀ c ∈ Finset.univ, (alphaQ 404 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 404 i (c.val i) t) =
      ((jwv 404 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 404 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 404 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 404 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 404 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_405 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 405),
        qvalQ (fun t ↦ ∑ i, PE 405 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 405),
        (alphaQ 405 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 405 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 405 = 1 := by decide +kernel
  have hce : certE (405 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (405 : Fin 1104)).2.2 = 21076016132 := by decide +kernel
  have hp : parent2 (405 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 405 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 405 c] :
    ∀ c ∈ Finset.univ, (alphaQ 405 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 405 i (c.val i) t) =
      ((jwv 405 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 405 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 405 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 405 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 405 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_406 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 406),
        qvalQ (fun t ↦ ∑ i, PE 406 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 406),
        (alphaQ 406 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 406 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 406 = 1 := by decide +kernel
  have hce : certE (406 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (406 : Fin 1104)).2.2 = 21076020765 := by decide +kernel
  have hp : parent2 (406 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 406 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 406 c] :
    ∀ c ∈ Finset.univ, (alphaQ 406 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 406 i (c.val i) t) =
      ((jwv 406 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 406 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 406 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 406 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 406 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_407 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 407),
        qvalQ (fun t ↦ ∑ i, PE 407 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 407),
        (alphaQ 407 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 407 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 407 = 1 := by decide +kernel
  have hce : certE (407 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (407 : Fin 1104)).2.2 = 21076016664 := by decide +kernel
  have hp : parent2 (407 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 407 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 407 c] :
    ∀ c ∈ Finset.univ, (alphaQ 407 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 407 i (c.val i) t) =
      ((jwv 407 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 407 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 407 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 407 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 407 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_408 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 408),
        qvalQ (fun t ↦ ∑ i, PE 408 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 408),
        (alphaQ 408 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 408 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 408 = 2 := by decide +kernel
  have hce : certE (408 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (408 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (408 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 408 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 408 c] :
    ∀ c ∈ Finset.univ, (alphaQ 408 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 408 i (c.val i) t) =
      ((jwv 408 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 408 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 408 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 408 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 408 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_409 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 409),
        qvalQ (fun t ↦ ∑ i, PE 409 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 409),
        (alphaQ 409 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 409 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 409 = 0 := by decide +kernel
  have hce : certE (409 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hs : (l2At (409 : Fin 1104)).2.2 = 21067842950 := by decide +kernel
  have hp : parent2 (409 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 409 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 409 c] :
    ∀ c ∈ Finset.univ, (alphaQ 409 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 409 i (c.val i) t) =
      ((jwv 409 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 409 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 409 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 409 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 409 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_410 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 410),
        qvalQ (fun t ↦ ∑ i, PE 410 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 410),
        (alphaQ 410 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 410 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 410 = 2 := by decide +kernel
  have hce : certE (410 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (410 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (410 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 410 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 410 c] :
    ∀ c ∈ Finset.univ, (alphaQ 410 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 410 i (c.val i) t) =
      ((jwv 410 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 410 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 410 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 410 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 410 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_411 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 411),
        qvalQ (fun t ↦ ∑ i, PE 411 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 411),
        (alphaQ 411 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 411 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 411 = 0 := by decide +kernel
  have hce : certE (411 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 7 else if j.val = 1 then -5 else if j.val = 2 then -2 else 0)) := by decide +kernel
  have hs : (l2At (411 : Fin 1104)).2.2 = 21067962519 := by decide +kernel
  have hp : parent2 (411 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 411 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 411 c] :
    ∀ c ∈ Finset.univ, (alphaQ 411 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 411 i (c.val i) t) =
      ((jwv 411 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 411 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 411 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 411 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 411 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_412 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 412),
        qvalQ (fun t ↦ ∑ i, PE 412 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 412),
        (alphaQ 412 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 412 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 412 = 2 := by decide +kernel
  have hce : certE (412 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (412 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (412 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 412 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 412 c] :
    ∀ c ∈ Finset.univ, (alphaQ 412 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 412 i (c.val i) t) =
      ((jwv 412 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 412 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 412 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 412 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 412 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_413 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 413),
        qvalQ (fun t ↦ ∑ i, PE 413 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 413),
        (alphaQ 413 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 413 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 413 = 0 := by decide +kernel
  have hce : certE (413 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hs : (l2At (413 : Fin 1104)).2.2 = 21067809393 := by decide +kernel
  have hp : parent2 (413 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 413 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 413 c] :
    ∀ c ∈ Finset.univ, (alphaQ 413 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 413 i (c.val i) t) =
      ((jwv 413 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 413 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 413 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 413 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 413 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

end MME.L2Cert

theorem solution : ∀ j : Fin 46,
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 ⟨368 + j.val, by omega⟩),
        qvalQ (fun t ↦ ∑ i, PE ⟨368 + j.val, by omega⟩ i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 ⟨368 + j.val, by omega⟩),
        (alphaQ ⟨368 + j.val, by omega⟩ c) ^ 2 /
          qvalQ (fun t ↦ ∑ i, PE ⟨368 + j.val, by omega⟩ i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  intro j
  match j with
  | ⟨0, _⟩ => exact MME.L2Cert.pcert_368
  | ⟨1, _⟩ => exact MME.L2Cert.pcert_369
  | ⟨2, _⟩ => exact MME.L2Cert.pcert_370
  | ⟨3, _⟩ => exact MME.L2Cert.pcert_371
  | ⟨4, _⟩ => exact MME.L2Cert.pcert_372
  | ⟨5, _⟩ => exact MME.L2Cert.pcert_373
  | ⟨6, _⟩ => exact MME.L2Cert.pcert_374
  | ⟨7, _⟩ => exact MME.L2Cert.pcert_375
  | ⟨8, _⟩ => exact MME.L2Cert.pcert_376
  | ⟨9, _⟩ => exact MME.L2Cert.pcert_377
  | ⟨10, _⟩ => exact MME.L2Cert.pcert_378
  | ⟨11, _⟩ => exact MME.L2Cert.pcert_379
  | ⟨12, _⟩ => exact MME.L2Cert.pcert_380
  | ⟨13, _⟩ => exact MME.L2Cert.pcert_381
  | ⟨14, _⟩ => exact MME.L2Cert.pcert_382
  | ⟨15, _⟩ => exact MME.L2Cert.pcert_383
  | ⟨16, _⟩ => exact MME.L2Cert.pcert_384
  | ⟨17, _⟩ => exact MME.L2Cert.pcert_385
  | ⟨18, _⟩ => exact MME.L2Cert.pcert_386
  | ⟨19, _⟩ => exact MME.L2Cert.pcert_387
  | ⟨20, _⟩ => exact MME.L2Cert.pcert_388
  | ⟨21, _⟩ => exact MME.L2Cert.pcert_389
  | ⟨22, _⟩ => exact MME.L2Cert.pcert_390
  | ⟨23, _⟩ => exact MME.L2Cert.pcert_391
  | ⟨24, _⟩ => exact MME.L2Cert.pcert_392
  | ⟨25, _⟩ => exact MME.L2Cert.pcert_393
  | ⟨26, _⟩ => exact MME.L2Cert.pcert_394
  | ⟨27, _⟩ => exact MME.L2Cert.pcert_395
  | ⟨28, _⟩ => exact MME.L2Cert.pcert_396
  | ⟨29, _⟩ => exact MME.L2Cert.pcert_397
  | ⟨30, _⟩ => exact MME.L2Cert.pcert_398
  | ⟨31, _⟩ => exact MME.L2Cert.pcert_399
  | ⟨32, _⟩ => exact MME.L2Cert.pcert_400
  | ⟨33, _⟩ => exact MME.L2Cert.pcert_401
  | ⟨34, _⟩ => exact MME.L2Cert.pcert_402
  | ⟨35, _⟩ => exact MME.L2Cert.pcert_403
  | ⟨36, _⟩ => exact MME.L2Cert.pcert_404
  | ⟨37, _⟩ => exact MME.L2Cert.pcert_405
  | ⟨38, _⟩ => exact MME.L2Cert.pcert_406
  | ⟨39, _⟩ => exact MME.L2Cert.pcert_407
  | ⟨40, _⟩ => exact MME.L2Cert.pcert_408
  | ⟨41, _⟩ => exact MME.L2Cert.pcert_409
  | ⟨42, _⟩ => exact MME.L2Cert.pcert_410
  | ⟨43, _⟩ => exact MME.L2Cert.pcert_411
  | ⟨44, _⟩ => exact MME.L2Cert.pcert_412
  | ⟨45, _⟩ => exact MME.L2Cert.pcert_413
  | ⟨n + 46, h⟩ => exact absurd h (by omega)

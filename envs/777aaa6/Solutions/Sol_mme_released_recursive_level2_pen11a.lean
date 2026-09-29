-- Prove2me | solution 1 for mme_released_recursive_level2_pen11a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T05:00:43.743741+00:00
-- url     : https://prove2.me/submissions/1a4ddd4a-78af-4718-81fa-96ddb892e714

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

theorem pcert_506 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 506),
        qvalQ (fun t ↦ ∑ i, PE 506 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 506),
        (alphaQ 506 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 506 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 506 = 1 := by decide +kernel
  have hce : certE (506 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (506 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (506 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 506 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 506 c] :
    ∀ c ∈ Finset.univ, (alphaQ 506 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 506 i (c.val i) t) =
      ((jwv 506 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 506 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 506 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 506 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 506 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_507 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 507),
        qvalQ (fun t ↦ ∑ i, PE 507 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 507),
        (alphaQ 507 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 507 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 507 = 0 := by decide +kernel
  have hce : certE (507 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (4 : Int) else if j.val = 1 then 8 else if j.val = 2 then -6 else -1) else (if j.val = 0 then -32 else if j.val = 1 then 1 else if j.val = 2 then 1 else 8)) := by decide +kernel
  have hs : (l2At (507 : Fin 1104)).2.2 = 20134395249 := by decide +kernel
  have hp : parent2 (507 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 507 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 507 c] :
    ∀ c ∈ Finset.univ, (alphaQ 507 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 507 i (c.val i) t) =
      ((jwv 507 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 507 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 507 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 507 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 507 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_508 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 508),
        qvalQ (fun t ↦ ∑ i, PE 508 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 508),
        (alphaQ 508 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 508 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 508 = 2 := by decide +kernel
  have hce : certE (508 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (508 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (508 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 508 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 508 c] :
    ∀ c ∈ Finset.univ, (alphaQ 508 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 508 i (c.val i) t) =
      ((jwv 508 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 508 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 508 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 508 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 508 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_509 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 509),
        qvalQ (fun t ↦ ∑ i, PE 509 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 509),
        (alphaQ 509 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 509 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 509 = 1 := by decide +kernel
  have hce : certE (509 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (509 : Fin 1104)).2.2 = 21076591749 := by decide +kernel
  have hp : parent2 (509 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 509 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 509 c] :
    ∀ c ∈ Finset.univ, (alphaQ 509 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 509 i (c.val i) t) =
      ((jwv 509 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 509 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 509 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 509 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 509 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_510 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 510),
        qvalQ (fun t ↦ ∑ i, PE 510 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 510),
        (alphaQ 510 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 510 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 510 = 0 := by decide +kernel
  have hce : certE (510 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (19 : Int) else if j.val = 1 then -5 else if j.val = 2 then -6 else 1) else (if j.val = 0 then 14 else if j.val = 1 then 1 else if j.val = 2 then -2 else -6)) := by decide +kernel
  have hs : (l2At (510 : Fin 1104)).2.2 = 16710561351 := by decide +kernel
  have hp : parent2 (510 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 510 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 510 c] :
    ∀ c ∈ Finset.univ, (alphaQ 510 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 510 i (c.val i) t) =
      ((jwv 510 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 510 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 510 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 510 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 510 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_511 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 511),
        qvalQ (fun t ↦ ∑ i, PE 511 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 511),
        (alphaQ 511 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 511 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 511 = 2 := by decide +kernel
  have hce : certE (511 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hs : (l2At (511 : Fin 1104)).2.2 = 21066221783 := by decide +kernel
  have hp : parent2 (511 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 511 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 511 c] :
    ∀ c ∈ Finset.univ, (alphaQ 511 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 511 i (c.val i) t) =
      ((jwv 511 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 511 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 511 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 511 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 511 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_512 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 512),
        qvalQ (fun t ↦ ∑ i, PE 512 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 512),
        (alphaQ 512 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 512 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 512 = 1 := by decide +kernel
  have hce : certE (512 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (512 : Fin 1104)).2.2 = 21076588200 := by decide +kernel
  have hp : parent2 (512 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 512 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 512 c] :
    ∀ c ∈ Finset.univ, (alphaQ 512 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 512 i (c.val i) t) =
      ((jwv 512 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 512 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 512 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 512 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 512 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_513 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 513),
        qvalQ (fun t ↦ ∑ i, PE 513 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 513),
        (alphaQ 513 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 513 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 513 = 0 := by decide +kernel
  have hce : certE (513 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 5 else if j.val = 2 then -1 else -2) else (if j.val = 0 then 16 else if j.val = 1 then -6 else if j.val = 2 then -5 else -1)) := by decide +kernel
  have hs : (l2At (513 : Fin 1104)).2.2 = 4109402777 := by decide +kernel
  have hp : parent2 (513 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 513 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 513 c] :
    ∀ c ∈ Finset.univ, (alphaQ 513 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 513 i (c.val i) t) =
      ((jwv 513 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 513 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 513 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 513 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 513 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_514 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 514),
        qvalQ (fun t ↦ ∑ i, PE 514 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 514),
        (alphaQ 514 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 514 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 514 = 2 := by decide +kernel
  have hce : certE (514 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 17 else if j.val = 1 then -3 else if j.val = 2 then 2 else -8)) := by decide +kernel
  have hs : (l2At (514 : Fin 1104)).2.2 = 21054319970 := by decide +kernel
  have hp : parent2 (514 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 514 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 514 c] :
    ∀ c ∈ Finset.univ, (alphaQ 514 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 514 i (c.val i) t) =
      ((jwv 514 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 514 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 514 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 514 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 514 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_515 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 515),
        qvalQ (fun t ↦ ∑ i, PE 515 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 515),
        (alphaQ 515 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 515 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 515 = 1 := by decide +kernel
  have hce : certE (515 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (515 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (515 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 515 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 515 c] :
    ∀ c ∈ Finset.univ, (alphaQ 515 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 515 i (c.val i) t) =
      ((jwv 515 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 515 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 515 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 515 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 515 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_516 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 516),
        qvalQ (fun t ↦ ∑ i, PE 516 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 516),
        (alphaQ 516 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 516 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 516 = 0 := by decide +kernel
  have hce : certE (516 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (19 : Int) else if j.val = 1 then -5 else if j.val = 2 then -6 else 1) else (if j.val = 0 then 13 else if j.val = 1 then -6 else if j.val = 2 then 2 else -5)) := by decide +kernel
  have hs : (l2At (516 : Fin 1104)).2.2 = 16716577455 := by decide +kernel
  have hp : parent2 (516 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 516 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 516 c] :
    ∀ c ∈ Finset.univ, (alphaQ 516 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 516 i (c.val i) t) =
      ((jwv 516 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 516 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 516 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 516 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 516 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_517 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 517),
        qvalQ (fun t ↦ ∑ i, PE 517 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 517),
        (alphaQ 517 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 517 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 517 = 2 := by decide +kernel
  have hce : certE (517 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 17 else if j.val = 1 then -3 else if j.val = 2 then 2 else -8)) := by decide +kernel
  have hs : (l2At (517 : Fin 1104)).2.2 = 21054327710 := by decide +kernel
  have hp : parent2 (517 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 517 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 517 c] :
    ∀ c ∈ Finset.univ, (alphaQ 517 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 517 i (c.val i) t) =
      ((jwv 517 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 517 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 517 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 517 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 517 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_518 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 518),
        qvalQ (fun t ↦ ∑ i, PE 518 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 518),
        (alphaQ 518 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 518 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 518 = 1 := by decide +kernel
  have hce : certE (518 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -3 else if j.val = 1 then -7 else if j.val = 2 then -6 else 8)) := by decide +kernel
  have hs : (l2At (518 : Fin 1104)).2.2 = 21088598141 := by decide +kernel
  have hp : parent2 (518 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 518 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 518 c] :
    ∀ c ∈ Finset.univ, (alphaQ 518 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 518 i (c.val i) t) =
      ((jwv 518 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 518 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 518 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 518 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 518 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_519 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 519),
        qvalQ (fun t ↦ ∑ i, PE 519 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 519),
        (alphaQ 519 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 519 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 519 = 0 := by decide +kernel
  have hce : certE (519 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 5 else if j.val = 2 then -1 else -2) else (if j.val = 0 then 16 else if j.val = 1 then -6 else if j.val = 2 then -5 else -1)) := by decide +kernel
  have hs : (l2At (519 : Fin 1104)).2.2 = 4109280337 := by decide +kernel
  have hp : parent2 (519 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 519 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 519 c] :
    ∀ c ∈ Finset.univ, (alphaQ 519 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 519 i (c.val i) t) =
      ((jwv 519 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 519 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 519 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 519 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 519 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_520 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 520),
        qvalQ (fun t ↦ ∑ i, PE 520 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 520),
        (alphaQ 520 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 520 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 520 = 1 := by decide +kernel
  have hce : certE (520 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (520 : Fin 1104)).2.2 = 21076589675 := by decide +kernel
  have hp : parent2 (520 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 520 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 520 c] :
    ∀ c ∈ Finset.univ, (alphaQ 520 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 520 i (c.val i) t) =
      ((jwv 520 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 520 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 520 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 520 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 520 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_521 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 521),
        qvalQ (fun t ↦ ∑ i, PE 521 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 521),
        (alphaQ 521 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 521 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 521 = 0 := by decide +kernel
  have hce : certE (521 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-21 : Int) else if j.val = 1 then 8 else if j.val = 2 then 6 else -2) else (if j.val = 0 then -19 else if j.val = 1 then 8 else if j.val = 2 then 7 else -7)) := by decide +kernel
  have hs : (l2At (521 : Fin 1104)).2.2 = 1187109476 := by decide +kernel
  have hp : parent2 (521 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 521 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 521 c] :
    ∀ c ∈ Finset.univ, (alphaQ 521 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 521 i (c.val i) t) =
      ((jwv 521 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 521 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 521 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 521 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 521 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_522 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 522),
        qvalQ (fun t ↦ ∑ i, PE 522 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 522),
        (alphaQ 522 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 522 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 522 = 1 := by decide +kernel
  have hce : certE (522 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (522 : Fin 1104)).2.2 = 21076590524 := by decide +kernel
  have hp : parent2 (522 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 522 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 522 c] :
    ∀ c ∈ Finset.univ, (alphaQ 522 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 522 i (c.val i) t) =
      ((jwv 522 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 522 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 522 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 522 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 522 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_523 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 523),
        qvalQ (fun t ↦ ∑ i, PE 523 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 523),
        (alphaQ 523 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 523 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 523 = 0 := by decide +kernel
  have hce : certE (523 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then -12 else if j.val = 1 then -3 else if j.val = 2 then -1 else 3)) := by decide +kernel
  have hs : (l2At (523 : Fin 1104)).2.2 = 620281658 := by decide +kernel
  have hp : parent2 (523 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 523 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 523 c] :
    ∀ c ∈ Finset.univ, (alphaQ 523 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 523 i (c.val i) t) =
      ((jwv 523 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 523 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 523 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 523 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 523 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_524 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 524),
        qvalQ (fun t ↦ ∑ i, PE 524 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 524),
        (alphaQ 524 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 524 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 524 = 1 := by decide +kernel
  have hce : certE (524 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (524 : Fin 1104)).2.2 = 21076586832 := by decide +kernel
  have hp : parent2 (524 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 524 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 524 c] :
    ∀ c ∈ Finset.univ, (alphaQ 524 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 524 i (c.val i) t) =
      ((jwv 524 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 524 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 524 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 524 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 524 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_525 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 525),
        qvalQ (fun t ↦ ∑ i, PE 525 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 525),
        (alphaQ 525 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 525 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 525 = 0 := by decide +kernel
  have hce : certE (525 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-32 : Int) else if j.val = 1 then -1 else if j.val = 2 then 6 else 7) else (if j.val = 0 then -12 else if j.val = 1 then -3 else if j.val = 2 then -1 else 3)) := by decide +kernel
  have hs : (l2At (525 : Fin 1104)).2.2 = 620334521 := by decide +kernel
  have hp : parent2 (525 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 525 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 525 c] :
    ∀ c ∈ Finset.univ, (alphaQ 525 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 525 i (c.val i) t) =
      ((jwv 525 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 525 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 525 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 525 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 525 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_526 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 526),
        qvalQ (fun t ↦ ∑ i, PE 526 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 526),
        (alphaQ 526 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 526 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 526 = 2 := by decide +kernel
  have hce : certE (526 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (526 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (526 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 526 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 526 c] :
    ∀ c ∈ Finset.univ, (alphaQ 526 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 526 i (c.val i) t) =
      ((jwv 526 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 526 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 526 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 526 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 526 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_527 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 527),
        qvalQ (fun t ↦ ∑ i, PE 527 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 527),
        (alphaQ 527 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 527 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 527 = 0 := by decide +kernel
  have hce : certE (527 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (3 : Int) else if j.val = 1 then 4 else if j.val = 2 then 2 else -5) else (if j.val = 0 then -13 else if j.val = 1 then -4 else if j.val = 2 then 1 else 4)) := by decide +kernel
  have hs : (l2At (527 : Fin 1104)).2.2 = 18091684220 := by decide +kernel
  have hp : parent2 (527 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 527 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 527 c] :
    ∀ c ∈ Finset.univ, (alphaQ 527 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 527 i (c.val i) t) =
      ((jwv 527 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 527 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 527 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 527 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 527 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_528 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 528),
        qvalQ (fun t ↦ ∑ i, PE 528 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 528),
        (alphaQ 528 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 528 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 528 = 2 := by decide +kernel
  have hce : certE (528 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (528 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (528 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 528 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 528 c] :
    ∀ c ∈ Finset.univ, (alphaQ 528 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 528 i (c.val i) t) =
      ((jwv 528 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 528 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 528 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 528 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 528 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

end MME.L2Cert

theorem solution : ∀ j : Fin 23,
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 ⟨506 + j.val, by omega⟩),
        qvalQ (fun t ↦ ∑ i, PE ⟨506 + j.val, by omega⟩ i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 ⟨506 + j.val, by omega⟩),
        (alphaQ ⟨506 + j.val, by omega⟩ c) ^ 2 /
          qvalQ (fun t ↦ ∑ i, PE ⟨506 + j.val, by omega⟩ i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  intro j
  match j with
  | ⟨0, _⟩ => exact MME.L2Cert.pcert_506
  | ⟨1, _⟩ => exact MME.L2Cert.pcert_507
  | ⟨2, _⟩ => exact MME.L2Cert.pcert_508
  | ⟨3, _⟩ => exact MME.L2Cert.pcert_509
  | ⟨4, _⟩ => exact MME.L2Cert.pcert_510
  | ⟨5, _⟩ => exact MME.L2Cert.pcert_511
  | ⟨6, _⟩ => exact MME.L2Cert.pcert_512
  | ⟨7, _⟩ => exact MME.L2Cert.pcert_513
  | ⟨8, _⟩ => exact MME.L2Cert.pcert_514
  | ⟨9, _⟩ => exact MME.L2Cert.pcert_515
  | ⟨10, _⟩ => exact MME.L2Cert.pcert_516
  | ⟨11, _⟩ => exact MME.L2Cert.pcert_517
  | ⟨12, _⟩ => exact MME.L2Cert.pcert_518
  | ⟨13, _⟩ => exact MME.L2Cert.pcert_519
  | ⟨14, _⟩ => exact MME.L2Cert.pcert_520
  | ⟨15, _⟩ => exact MME.L2Cert.pcert_521
  | ⟨16, _⟩ => exact MME.L2Cert.pcert_522
  | ⟨17, _⟩ => exact MME.L2Cert.pcert_523
  | ⟨18, _⟩ => exact MME.L2Cert.pcert_524
  | ⟨19, _⟩ => exact MME.L2Cert.pcert_525
  | ⟨20, _⟩ => exact MME.L2Cert.pcert_526
  | ⟨21, _⟩ => exact MME.L2Cert.pcert_527
  | ⟨22, _⟩ => exact MME.L2Cert.pcert_528
  | ⟨n + 23, h⟩ => exact absurd h (by omega)

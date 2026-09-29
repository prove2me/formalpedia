-- Prove2me | solution 1 for mme_released_recursive_level2_pen9a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T05:01:56.780977+00:00
-- url     : https://prove2.me/submissions/fad0e7d2-151d-47a1-aab0-332f1b0a6531

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

theorem pcert_414 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 414),
        qvalQ (fun t ↦ ∑ i, PE 414 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 414),
        (alphaQ 414 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 414 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 414 = 2 := by decide +kernel
  have hce : certE (414 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-11 : Int) else if j.val = 1 then -1 else if j.val = 2 then 3 else 2) else (if j.val = 0 then -19 else if j.val = 1 then 2 else if j.val = 2 then 4 else -1)) := by decide +kernel
  have hs : (l2At (414 : Fin 1104)).2.2 = 1532537704 := by decide +kernel
  have hp : parent2 (414 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 414 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 414 c] :
    ∀ c ∈ Finset.univ, (alphaQ 414 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 414 i (c.val i) t) =
      ((jwv 414 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 414 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 414 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 414 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 414 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_415 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 415),
        qvalQ (fun t ↦ ∑ i, PE 415 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 415),
        (alphaQ 415 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 415 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 415 = 1 := by decide +kernel
  have hce : certE (415 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -4 else if j.val = 1 then -3 else if j.val = 2 then 5 else -3)) := by decide +kernel
  have hs : (l2At (415 : Fin 1104)).2.2 = 21088758930 := by decide +kernel
  have hp : parent2 (415 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 415 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 415 c] :
    ∀ c ∈ Finset.univ, (alphaQ 415 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 415 i (c.val i) t) =
      ((jwv 415 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 415 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 415 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 415 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 415 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_416 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 416),
        qvalQ (fun t ↦ ∑ i, PE 416 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 416),
        (alphaQ 416 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 416 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 416 = 0 := by decide +kernel
  have hce : certE (416 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hs : (l2At (416 : Fin 1104)).2.2 = 21067903718 := by decide +kernel
  have hp : parent2 (416 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 416 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 416 c] :
    ∀ c ∈ Finset.univ, (alphaQ 416 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 416 i (c.val i) t) =
      ((jwv 416 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 416 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 416 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 416 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 416 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_417 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 417),
        qvalQ (fun t ↦ ∑ i, PE 417 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 417),
        (alphaQ 417 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 417 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 417 = 2 := by decide +kernel
  have hce : certE (417 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (20 : Int) else if j.val = 1 then 5 else if j.val = 2 then -6 else -5) else (if j.val = 0 then -14 else if j.val = 1 then -3 else if j.val = 2 then -3 else 7)) := by decide +kernel
  have hs : (l2At (417 : Fin 1104)).2.2 = 14893969038 := by decide +kernel
  have hp : parent2 (417 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 417 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 417 c] :
    ∀ c ∈ Finset.univ, (alphaQ 417 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 417 i (c.val i) t) =
      ((jwv 417 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 417 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 417 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 417 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 417 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_418 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 418),
        qvalQ (fun t ↦ ∑ i, PE 418 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 418),
        (alphaQ 418 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 418 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 418 = 1 := by decide +kernel
  have hce : certE (418 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (418 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (418 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 418 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 418 c] :
    ∀ c ∈ Finset.univ, (alphaQ 418 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 418 i (c.val i) t) =
      ((jwv 418 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 418 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 418 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 418 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 418 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_419 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 419),
        qvalQ (fun t ↦ ∑ i, PE 419 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 419),
        (alphaQ 419 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 419 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 419 = 0 := by decide +kernel
  have hce : certE (419 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hs : (l2At (419 : Fin 1104)).2.2 = 21067721374 := by decide +kernel
  have hp : parent2 (419 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 419 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 419 c] :
    ∀ c ∈ Finset.univ, (alphaQ 419 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 419 i (c.val i) t) =
      ((jwv 419 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 419 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 419 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 419 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 419 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_420 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 420),
        qvalQ (fun t ↦ ∑ i, PE 420 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 420),
        (alphaQ 420 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 420 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 420 = 2 := by decide +kernel
  have hce : certE (420 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-11 : Int) else if j.val = 1 then -1 else if j.val = 2 then 3 else 2) else (if j.val = 0 then -19 else if j.val = 1 then 2 else if j.val = 2 then 4 else -1)) := by decide +kernel
  have hs : (l2At (420 : Fin 1104)).2.2 = 1532516182 := by decide +kernel
  have hp : parent2 (420 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 420 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 420 c] :
    ∀ c ∈ Finset.univ, (alphaQ 420 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 420 i (c.val i) t) =
      ((jwv 420 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 420 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 420 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 420 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 420 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_421 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 421),
        qvalQ (fun t ↦ ∑ i, PE 421 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 421),
        (alphaQ 421 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 421 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 421 = 1 := by decide +kernel
  have hce : certE (421 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (421 : Fin 1104)).2.2 = 21076588304 := by decide +kernel
  have hp : parent2 (421 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 421 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 421 c] :
    ∀ c ∈ Finset.univ, (alphaQ 421 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 421 i (c.val i) t) =
      ((jwv 421 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 421 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 421 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 421 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 421 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_422 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 422),
        qvalQ (fun t ↦ ∑ i, PE 422 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 422),
        (alphaQ 422 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 422 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 422 = 0 := by decide +kernel
  have hce : certE (422 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 1 else if j.val = 1 then -2 else if j.val = 2 then 7 else -7)) := by decide +kernel
  have hs : (l2At (422 : Fin 1104)).2.2 = 21080047956 := by decide +kernel
  have hp : parent2 (422 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 422 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 422 c] :
    ∀ c ∈ Finset.univ, (alphaQ 422 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 422 i (c.val i) t) =
      ((jwv 422 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 422 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 422 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 422 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 422 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_423 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 423),
        qvalQ (fun t ↦ ∑ i, PE 423 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 423),
        (alphaQ 423 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 423 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 423 = 2 := by decide +kernel
  have hce : certE (423 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (20 : Int) else if j.val = 1 then 5 else if j.val = 2 then -6 else -5) else (if j.val = 0 then -14 else if j.val = 1 then 8 else if j.val = 2 then 4 else -5)) := by decide +kernel
  have hs : (l2At (423 : Fin 1104)).2.2 = 14891659264 := by decide +kernel
  have hp : parent2 (423 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 423 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 423 c] :
    ∀ c ∈ Finset.univ, (alphaQ 423 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 423 i (c.val i) t) =
      ((jwv 423 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 423 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 423 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 423 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 423 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_424 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 424),
        qvalQ (fun t ↦ ∑ i, PE 424 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 424),
        (alphaQ 424 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 424 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 424 = 1 := by decide +kernel
  have hce : certE (424 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (424 : Fin 1104)).2.2 = 21076599831 := by decide +kernel
  have hp : parent2 (424 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 424 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 424 c] :
    ∀ c ∈ Finset.univ, (alphaQ 424 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 424 i (c.val i) t) =
      ((jwv 424 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 424 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 424 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 424 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 424 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_425 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 425),
        qvalQ (fun t ↦ ∑ i, PE 425 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 425),
        (alphaQ 425 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 425 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 425 = 0 := by decide +kernel
  have hce : certE (425 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (425 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (425 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 425 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 425 c] :
    ∀ c ∈ Finset.univ, (alphaQ 425 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 425 i (c.val i) t) =
      ((jwv 425 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 425 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 425 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 425 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 425 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_426 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 426),
        qvalQ (fun t ↦ ∑ i, PE 426 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 426),
        (alphaQ 426 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 426 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 426 = 2 := by decide +kernel
  have hce : certE (426 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (426 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (426 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 426 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 426 c] :
    ∀ c ∈ Finset.univ, (alphaQ 426 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 426 i (c.val i) t) =
      ((jwv 426 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 426 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 426 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 426 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 426 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_427 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 427),
        qvalQ (fun t ↦ ∑ i, PE 427 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 427),
        (alphaQ 427 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 427 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 427 = 1 := by decide +kernel
  have hce : certE (427 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (427 : Fin 1104)).2.2 = 21076600989 := by decide +kernel
  have hp : parent2 (427 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 427 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 427 c] :
    ∀ c ∈ Finset.univ, (alphaQ 427 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 427 i (c.val i) t) =
      ((jwv 427 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 427 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 427 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 427 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 427 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_428 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 428),
        qvalQ (fun t ↦ ∑ i, PE 428 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 428),
        (alphaQ 428 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 428 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 428 = 0 := by decide +kernel
  have hce : certE (428 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (35 : Int) else if j.val = 1 then 2 else if j.val = 2 then -8 else -7) else (if j.val = 0 then -4 else if j.val = 1 then -1 else if j.val = 2 then 6 else -5)) := by decide +kernel
  have hs : (l2At (428 : Fin 1104)).2.2 = 19369504580 := by decide +kernel
  have hp : parent2 (428 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 428 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 428 c] :
    ∀ c ∈ Finset.univ, (alphaQ 428 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 428 i (c.val i) t) =
      ((jwv 428 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 428 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 428 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 428 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 428 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_429 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 429),
        qvalQ (fun t ↦ ∑ i, PE 429 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 429),
        (alphaQ 429 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 429 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 429 = 2 := by decide +kernel
  have hce : certE (429 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-11 : Int) else if j.val = 1 then 1 else if j.val = 2 then -2 else 5) else (if j.val = 0 then 16 else if j.val = 1 then -8 else if j.val = 2 then 4 else -7)) := by decide +kernel
  have hs : (l2At (429 : Fin 1104)).2.2 = 7580579254 := by decide +kernel
  have hp : parent2 (429 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 429 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 429 c] :
    ∀ c ∈ Finset.univ, (alphaQ 429 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 429 i (c.val i) t) =
      ((jwv 429 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 429 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 429 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 429 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 429 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_430 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 430),
        qvalQ (fun t ↦ ∑ i, PE 430 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 430),
        (alphaQ 430 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 430 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 430 = 1 := by decide +kernel
  have hce : certE (430 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (430 : Fin 1104)).2.2 = 21076601526 := by decide +kernel
  have hp : parent2 (430 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 430 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 430 c] :
    ∀ c ∈ Finset.univ, (alphaQ 430 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 430 i (c.val i) t) =
      ((jwv 430 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 430 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 430 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 430 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 430 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_431 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 431),
        qvalQ (fun t ↦ ∑ i, PE 431 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 431),
        (alphaQ 431 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 431 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 431 = 0 := by decide +kernel
  have hce : certE (431 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (8 : Int) else if j.val = 1 then -6 else if j.val = 2 then -3 else 3) else (if j.val = 0 then -28 else if j.val = 1 then 7 else if j.val = 2 then 6 else -1)) := by decide +kernel
  have hs : (l2At (431 : Fin 1104)).2.2 = 18186042626 := by decide +kernel
  have hp : parent2 (431 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 431 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 431 c] :
    ∀ c ∈ Finset.univ, (alphaQ 431 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 431 i (c.val i) t) =
      ((jwv 431 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 431 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 431 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 431 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 431 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_432 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 432),
        qvalQ (fun t ↦ ∑ i, PE 432 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 432),
        (alphaQ 432 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 432 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 432 = 2 := by decide +kernel
  have hce : certE (432 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hs : (l2At (432 : Fin 1104)).2.2 = 20922586596 := by decide +kernel
  have hp : parent2 (432 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 432 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 432 c] :
    ∀ c ∈ Finset.univ, (alphaQ 432 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 432 i (c.val i) t) =
      ((jwv 432 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 432 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 432 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 432 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 432 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_433 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 433),
        qvalQ (fun t ↦ ∑ i, PE 433 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 433),
        (alphaQ 433 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 433 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 433 = 1 := by decide +kernel
  have hce : certE (433 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (433 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (433 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 433 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 433 c] :
    ∀ c ∈ Finset.univ, (alphaQ 433 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 433 i (c.val i) t) =
      ((jwv 433 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 433 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 433 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 433 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 433 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_434 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 434),
        qvalQ (fun t ↦ ∑ i, PE 434 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 434),
        (alphaQ 434 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 434 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 434 = 0 := by decide +kernel
  have hce : certE (434 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-13 : Int) else if j.val = 1 then 2 else if j.val = 2 then 3 else 1) else (if j.val = 0 then 3 else if j.val = 1 then 3 else if j.val = 2 then -7 else 1)) := by decide +kernel
  have hs : (l2At (434 : Fin 1104)).2.2 = 19353483895 := by decide +kernel
  have hp : parent2 (434 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 434 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 434 c] :
    ∀ c ∈ Finset.univ, (alphaQ 434 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 434 i (c.val i) t) =
      ((jwv 434 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 434 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 434 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 434 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 434 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_435 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 435),
        qvalQ (fun t ↦ ∑ i, PE 435 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 435),
        (alphaQ 435 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 435 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 435 = 2 := by decide +kernel
  have hce : certE (435 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (28 : Int) else if j.val = 1 then -5 else if j.val = 2 then 1 else -8) else (if j.val = 0 then -5 else if j.val = 1 then -5 else if j.val = 2 then 8 else -4)) := by decide +kernel
  have hs : (l2At (435 : Fin 1104)).2.2 = 20922585317 := by decide +kernel
  have hp : parent2 (435 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 435 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 435 c] :
    ∀ c ∈ Finset.univ, (alphaQ 435 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 435 i (c.val i) t) =
      ((jwv 435 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 435 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 435 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 435 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 435 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_436 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 436),
        qvalQ (fun t ↦ ∑ i, PE 436 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 436),
        (alphaQ 436 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 436 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 436 = 1 := by decide +kernel
  have hce : certE (436 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-6 : Int) else if j.val = 1 then 2 else if j.val = 2 then 0 else 1) else (if j.val = 0 then -7 else if j.val = 1 then -8 else if j.val = 2 then -3 else 7)) := by decide +kernel
  have hs : (l2At (436 : Fin 1104)).2.2 = 7845241478 := by decide +kernel
  have hp : parent2 (436 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 436 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 436 c] :
    ∀ c ∈ Finset.univ, (alphaQ 436 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 436 i (c.val i) t) =
      ((jwv 436 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 436 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 436 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 436 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 436 i (a i) t)),
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
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 ⟨414 + j.val, by omega⟩),
        qvalQ (fun t ↦ ∑ i, PE ⟨414 + j.val, by omega⟩ i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 ⟨414 + j.val, by omega⟩),
        (alphaQ ⟨414 + j.val, by omega⟩ c) ^ 2 /
          qvalQ (fun t ↦ ∑ i, PE ⟨414 + j.val, by omega⟩ i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  intro j
  match j with
  | ⟨0, _⟩ => exact MME.L2Cert.pcert_414
  | ⟨1, _⟩ => exact MME.L2Cert.pcert_415
  | ⟨2, _⟩ => exact MME.L2Cert.pcert_416
  | ⟨3, _⟩ => exact MME.L2Cert.pcert_417
  | ⟨4, _⟩ => exact MME.L2Cert.pcert_418
  | ⟨5, _⟩ => exact MME.L2Cert.pcert_419
  | ⟨6, _⟩ => exact MME.L2Cert.pcert_420
  | ⟨7, _⟩ => exact MME.L2Cert.pcert_421
  | ⟨8, _⟩ => exact MME.L2Cert.pcert_422
  | ⟨9, _⟩ => exact MME.L2Cert.pcert_423
  | ⟨10, _⟩ => exact MME.L2Cert.pcert_424
  | ⟨11, _⟩ => exact MME.L2Cert.pcert_425
  | ⟨12, _⟩ => exact MME.L2Cert.pcert_426
  | ⟨13, _⟩ => exact MME.L2Cert.pcert_427
  | ⟨14, _⟩ => exact MME.L2Cert.pcert_428
  | ⟨15, _⟩ => exact MME.L2Cert.pcert_429
  | ⟨16, _⟩ => exact MME.L2Cert.pcert_430
  | ⟨17, _⟩ => exact MME.L2Cert.pcert_431
  | ⟨18, _⟩ => exact MME.L2Cert.pcert_432
  | ⟨19, _⟩ => exact MME.L2Cert.pcert_433
  | ⟨20, _⟩ => exact MME.L2Cert.pcert_434
  | ⟨21, _⟩ => exact MME.L2Cert.pcert_435
  | ⟨22, _⟩ => exact MME.L2Cert.pcert_436
  | ⟨n + 23, h⟩ => exact absurd h (by omega)

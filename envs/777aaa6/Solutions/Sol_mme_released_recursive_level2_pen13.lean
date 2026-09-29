-- Prove2me | solution 1 for mme_released_recursive_level2_pen13
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T04:37:22.791081+00:00
-- url     : https://prove2.me/submissions/93c46542-4ca1-45f9-a99c-55deed2d9030

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

theorem pcert_598 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 598),
        qvalQ (fun t ↦ ∑ i, PE 598 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 598),
        (alphaQ 598 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 598 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 598 = 2 := by decide +kernel
  have hce : certE (598 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -17 else if j.val = 1 then 8 else if j.val = 2 then -2 else -3)) := by decide +kernel
  have hs : (l2At (598 : Fin 1104)).2.2 = 5837530 := by decide +kernel
  have hp : parent2 (598 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 598 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 598 c] :
    ∀ c ∈ Finset.univ, (alphaQ 598 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 598 i (c.val i) t) =
      ((jwv 598 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 598 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 598 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 598 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 598 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_599 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 599),
        qvalQ (fun t ↦ ∑ i, PE 599 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 599),
        (alphaQ 599 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 599 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 599 = 0 := by decide +kernel
  have hce : certE (599 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 13 else if j.val = 1 then 3 else if j.val = 2 then -4 else -5)) := by decide +kernel
  have hs : (l2At (599 : Fin 1104)).2.2 = 21055027375 := by decide +kernel
  have hp : parent2 (599 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 599 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 599 c] :
    ∀ c ∈ Finset.univ, (alphaQ 599 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 599 i (c.val i) t) =
      ((jwv 599 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 599 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 599 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 599 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 599 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_600 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 600),
        qvalQ (fun t ↦ ∑ i, PE 600 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 600),
        (alphaQ 600 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 600 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 600 = 2 := by decide +kernel
  have hce : certE (600 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (600 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (600 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 600 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 600 c] :
    ∀ c ∈ Finset.univ, (alphaQ 600 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 600 i (c.val i) t) =
      ((jwv 600 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 600 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 600 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 600 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 600 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_601 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 601),
        qvalQ (fun t ↦ ∑ i, PE 601 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 601),
        (alphaQ 601 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 601 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 601 = 0 := by decide +kernel
  have hce : certE (601 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 13 else if j.val = 1 then 3 else if j.val = 2 then -4 else -5)) := by decide +kernel
  have hs : (l2At (601 : Fin 1104)).2.2 = 21054577590 := by decide +kernel
  have hp : parent2 (601 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 601 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 601 c] :
    ∀ c ∈ Finset.univ, (alphaQ 601 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 601 i (c.val i) t) =
      ((jwv 601 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 601 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 601 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 601 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 601 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_602 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 602),
        qvalQ (fun t ↦ ∑ i, PE 602 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 602),
        (alphaQ 602 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 602 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 602 = 2 := by decide +kernel
  have hce : certE (602 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (3 : Int) else if j.val = 1 then 4 else if j.val = 2 then 2 else -5) else (if j.val = 0 then -2 else if j.val = 1 then 5 else if j.val = 2 then 1 else -5)) := by decide +kernel
  have hs : (l2At (602 : Fin 1104)).2.2 = 18073334132 := by decide +kernel
  have hp : parent2 (602 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 602 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 602 c] :
    ∀ c ∈ Finset.univ, (alphaQ 602 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 602 i (c.val i) t) =
      ((jwv 602 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 602 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 602 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 602 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 602 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_603 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 603),
        qvalQ (fun t ↦ ∑ i, PE 603 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 603),
        (alphaQ 603 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 603 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 603 = 0 := by decide +kernel
  have hce : certE (603 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (603 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (603 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 603 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 603 c] :
    ∀ c ∈ Finset.univ, (alphaQ 603 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 603 i (c.val i) t) =
      ((jwv 603 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 603 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 603 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 603 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 603 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_604 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 604),
        qvalQ (fun t ↦ ∑ i, PE 604 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 604),
        (alphaQ 604 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 604 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 604 = 2 := by decide +kernel
  have hce : certE (604 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (3 : Int) else if j.val = 1 then 4 else if j.val = 2 then 2 else -5) else (if j.val = 0 then -2 else if j.val = 1 then -6 else if j.val = 2 then -6 else 7)) := by decide +kernel
  have hs : (l2At (604 : Fin 1104)).2.2 = 18074207851 := by decide +kernel
  have hp : parent2 (604 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 604 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 604 c] :
    ∀ c ∈ Finset.univ, (alphaQ 604 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 604 i (c.val i) t) =
      ((jwv 604 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 604 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 604 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 604 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 604 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_605 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 605),
        qvalQ (fun t ↦ ∑ i, PE 605 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 605),
        (alphaQ 605 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 605 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 605 = 0 := by decide +kernel
  have hce : certE (605 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (605 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (605 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 605 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 605 c] :
    ∀ c ∈ Finset.univ, (alphaQ 605 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 605 i (c.val i) t) =
      ((jwv 605 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 605 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 605 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 605 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 605 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_606 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 606),
        qvalQ (fun t ↦ ∑ i, PE 606 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 606),
        (alphaQ 606 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 606 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 606 = 2 := by decide +kernel
  have hce : certE (606 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 5 else if j.val = 2 then -1 else -2) else (if j.val = 0 then -11 else if j.val = 1 then -6 else if j.val = 2 then 3 else 2)) := by decide +kernel
  have hs : (l2At (606 : Fin 1104)).2.2 = 4102528207 := by decide +kernel
  have hp : parent2 (606 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 606 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 606 c] :
    ∀ c ∈ Finset.univ, (alphaQ 606 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 606 i (c.val i) t) =
      ((jwv 606 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 606 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 606 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 606 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 606 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_607 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 607),
        qvalQ (fun t ↦ ∑ i, PE 607 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 607),
        (alphaQ 607 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 607 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 607 = 1 := by decide +kernel
  have hce : certE (607 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -3 else if j.val = 1 then -7 else if j.val = 2 then -6 else 8)) := by decide +kernel
  have hs : (l2At (607 : Fin 1104)).2.2 = 21088634959 := by decide +kernel
  have hp : parent2 (607 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 607 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 607 c] :
    ∀ c ∈ Finset.univ, (alphaQ 607 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 607 i (c.val i) t) =
      ((jwv 607 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 607 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 607 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 607 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 607 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_608 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 608),
        qvalQ (fun t ↦ ∑ i, PE 608 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 608),
        (alphaQ 608 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 608 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 608 = 0 := by decide +kernel
  have hce : certE (608 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 13 else if j.val = 1 then 3 else if j.val = 2 then -4 else -5)) := by decide +kernel
  have hs : (l2At (608 : Fin 1104)).2.2 = 21054407659 := by decide +kernel
  have hp : parent2 (608 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 608 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 608 c] :
    ∀ c ∈ Finset.univ, (alphaQ 608 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 608 i (c.val i) t) =
      ((jwv 608 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 608 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 608 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 608 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 608 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_609 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 609),
        qvalQ (fun t ↦ ∑ i, PE 609 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 609),
        (alphaQ 609 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 609 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 609 = 2 := by decide +kernel
  have hce : certE (609 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (19 : Int) else if j.val = 1 then -5 else if j.val = 2 then -6 else 1) else (if j.val = 0 then 14 else if j.val = 1 then 1 else if j.val = 2 then -2 else -6)) := by decide +kernel
  have hs : (l2At (609 : Fin 1104)).2.2 = 16712605197 := by decide +kernel
  have hp : parent2 (609 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 609 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 609 c] :
    ∀ c ∈ Finset.univ, (alphaQ 609 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 609 i (c.val i) t) =
      ((jwv 609 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 609 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 609 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 609 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 609 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_610 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 610),
        qvalQ (fun t ↦ ∑ i, PE 610 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 610),
        (alphaQ 610 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 610 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 610 = 1 := by decide +kernel
  have hce : certE (610 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (610 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (610 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 610 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 610 c] :
    ∀ c ∈ Finset.univ, (alphaQ 610 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 610 i (c.val i) t) =
      ((jwv 610 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 610 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 610 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 610 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 610 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_611 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 611),
        qvalQ (fun t ↦ ∑ i, PE 611 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 611),
        (alphaQ 611 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 611 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 611 = 0 := by decide +kernel
  have hce : certE (611 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 13 else if j.val = 1 then 3 else if j.val = 2 then -4 else -5)) := by decide +kernel
  have hs : (l2At (611 : Fin 1104)).2.2 = 21054404138 := by decide +kernel
  have hp : parent2 (611 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 611 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 611 c] :
    ∀ c ∈ Finset.univ, (alphaQ 611 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 611 i (c.val i) t) =
      ((jwv 611 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 611 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 611 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 611 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 611 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_612 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 612),
        qvalQ (fun t ↦ ∑ i, PE 612 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 612),
        (alphaQ 612 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 612 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 612 = 2 := by decide +kernel
  have hce : certE (612 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 5 else if j.val = 2 then -1 else -2) else (if j.val = 0 then -11 else if j.val = 1 then -6 else if j.val = 2 then 3 else 2)) := by decide +kernel
  have hs : (l2At (612 : Fin 1104)).2.2 = 4102544872 := by decide +kernel
  have hp : parent2 (612 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 612 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 612 c] :
    ∀ c ∈ Finset.univ, (alphaQ 612 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 612 i (c.val i) t) =
      ((jwv 612 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 612 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 612 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 612 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 612 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_613 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 613),
        qvalQ (fun t ↦ ∑ i, PE 613 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 613),
        (alphaQ 613 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 613 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 613 = 1 := by decide +kernel
  have hce : certE (613 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (613 : Fin 1104)).2.2 = 21076587927 := by decide +kernel
  have hp : parent2 (613 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 613 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 613 c] :
    ∀ c ∈ Finset.univ, (alphaQ 613 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 613 i (c.val i) t) =
      ((jwv 613 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 613 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 613 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 613 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 613 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_614 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 614),
        qvalQ (fun t ↦ ∑ i, PE 614 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 614),
        (alphaQ 614 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 614 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 614 = 0 := by decide +kernel
  have hce : certE (614 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then -40 else if j.val = 1 then 2 else if j.val = 2 then 5 else 7)) := by decide +kernel
  have hs : (l2At (614 : Fin 1104)).2.2 = 21066362335 := by decide +kernel
  have hp : parent2 (614 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 614 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 614 c] :
    ∀ c ∈ Finset.univ, (alphaQ 614 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 614 i (c.val i) t) =
      ((jwv 614 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 614 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 614 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 614 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 614 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_615 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 615),
        qvalQ (fun t ↦ ∑ i, PE 615 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 615),
        (alphaQ 615 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 615 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 615 = 2 := by decide +kernel
  have hce : certE (615 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (19 : Int) else if j.val = 1 then -5 else if j.val = 2 then -6 else 1) else (if j.val = 0 then 15 else if j.val = 1 then 8 else if j.val = 2 then -6 else -7)) := by decide +kernel
  have hs : (l2At (615 : Fin 1104)).2.2 = 16706697919 := by decide +kernel
  have hp : parent2 (615 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 615 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 615 c] :
    ∀ c ∈ Finset.univ, (alphaQ 615 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 615 i (c.val i) t) =
      ((jwv 615 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 615 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 615 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 615 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 615 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_616 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 616),
        qvalQ (fun t ↦ ∑ i, PE 616 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 616),
        (alphaQ 616 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 616 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 616 = 1 := by decide +kernel
  have hce : certE (616 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (616 : Fin 1104)).2.2 = 21076591614 := by decide +kernel
  have hp : parent2 (616 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 616 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 616 c] :
    ∀ c ∈ Finset.univ, (alphaQ 616 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 616 i (c.val i) t) =
      ((jwv 616 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 616 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 616 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 616 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 616 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_617 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 617),
        qvalQ (fun t ↦ ∑ i, PE 617 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 617),
        (alphaQ 617 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 617 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 617 = 0 := by decide +kernel
  have hce : certE (617 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (617 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (617 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 617 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 617 c] :
    ∀ c ∈ Finset.univ, (alphaQ 617 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 617 i (c.val i) t) =
      ((jwv 617 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 617 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 617 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 617 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 617 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_618 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 618),
        qvalQ (fun t ↦ ∑ i, PE 618 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 618),
        (alphaQ 618 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 618 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 618 = 2 := by decide +kernel
  have hce : certE (618 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (4 : Int) else if j.val = 1 then 8 else if j.val = 2 then -6 else -1) else (if j.val = 0 then -28 else if j.val = 1 then -5 else if j.val = 2 then 7 else 5)) := by decide +kernel
  have hs : (l2At (618 : Fin 1104)).2.2 = 20130730373 := by decide +kernel
  have hp : parent2 (618 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 618 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 618 c] :
    ∀ c ∈ Finset.univ, (alphaQ 618 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 618 i (c.val i) t) =
      ((jwv 618 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 618 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 618 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 618 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 618 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_619 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 619),
        qvalQ (fun t ↦ ∑ i, PE 619 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 619),
        (alphaQ 619 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 619 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 619 = 1 := by decide +kernel
  have hce : certE (619 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (619 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (619 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 619 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 619 c] :
    ∀ c ∈ Finset.univ, (alphaQ 619 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 619 i (c.val i) t) =
      ((jwv 619 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 619 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 619 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 619 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 619 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_620 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 620),
        qvalQ (fun t ↦ ∑ i, PE 620 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 620),
        (alphaQ 620 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 620 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 620 = 0 := by decide +kernel
  have hce : certE (620 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -30 else if j.val = 1 then -8 else if j.val = 2 then 0 else 7)) := by decide +kernel
  have hs : (l2At (620 : Fin 1104)).2.2 = 116900 := by decide +kernel
  have hp : parent2 (620 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 620 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 620 c] :
    ∀ c ∈ Finset.univ, (alphaQ 620 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 620 i (c.val i) t) =
      ((jwv 620 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 620 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 620 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 620 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 620 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_621 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 621),
        qvalQ (fun t ↦ ∑ i, PE 621 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 621),
        (alphaQ 621 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 621 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 621 = 2 := by decide +kernel
  have hce : certE (621 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (4 : Int) else if j.val = 1 then 8 else if j.val = 2 then -6 else -1) else (if j.val = 0 then -28 else if j.val = 1 then -5 else if j.val = 2 then 7 else 5)) := by decide +kernel
  have hs : (l2At (621 : Fin 1104)).2.2 = 20130730335 := by decide +kernel
  have hp : parent2 (621 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 621 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 621 c] :
    ∀ c ∈ Finset.univ, (alphaQ 621 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 621 i (c.val i) t) =
      ((jwv 621 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 621 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 621 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 621 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 621 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_622 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 622),
        qvalQ (fun t ↦ ∑ i, PE 622 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 622),
        (alphaQ 622 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 622 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 622 = 1 := by decide +kernel
  have hce : certE (622 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -29 else if j.val = 1 then -4 else if j.val = 2 then 3 else 2)) := by decide +kernel
  have hs : (l2At (622 : Fin 1104)).2.2 = 140846 := by decide +kernel
  have hp : parent2 (622 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 622 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 622 c] :
    ∀ c ∈ Finset.univ, (alphaQ 622 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 622 i (c.val i) t) =
      ((jwv 622 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 622 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 622 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 622 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 622 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_623 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 623),
        qvalQ (fun t ↦ ∑ i, PE 623 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 623),
        (alphaQ 623 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 623 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 623 = 0 := by decide +kernel
  have hce : certE (623 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (623 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (623 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 623 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 623 c] :
    ∀ c ∈ Finset.univ, (alphaQ 623 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 623 i (c.val i) t) =
      ((jwv 623 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 623 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 623 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 623 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 623 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_624 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 624),
        qvalQ (fun t ↦ ∑ i, PE 624 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 624),
        (alphaQ 624 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 624 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 624 = 2 := by decide +kernel
  have hce : certE (624 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (624 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (624 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 624 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 624 c] :
    ∀ c ∈ Finset.univ, (alphaQ 624 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 624 i (c.val i) t) =
      ((jwv 624 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 624 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 624 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 624 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 624 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_625 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 625),
        qvalQ (fun t ↦ ∑ i, PE 625 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 625),
        (alphaQ 625 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 625 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 625 = 1 := by decide +kernel
  have hce : certE (625 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (625 : Fin 1104)).2.2 = 21076599788 := by decide +kernel
  have hp : parent2 (625 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 625 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 625 c] :
    ∀ c ∈ Finset.univ, (alphaQ 625 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 625 i (c.val i) t) =
      ((jwv 625 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 625 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 625 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 625 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 625 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_626 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 626),
        qvalQ (fun t ↦ ∑ i, PE 626 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 626),
        (alphaQ 626 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 626 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 626 = 0 := by decide +kernel
  have hce : certE (626 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-13 : Int) else if j.val = 1 then 2 else if j.val = 2 then 3 else 1) else (if j.val = 0 then 8 else if j.val = 1 then 4 else if j.val = 2 then -5 else -3)) := by decide +kernel
  have hs : (l2At (626 : Fin 1104)).2.2 = 19345402121 := by decide +kernel
  have hp : parent2 (626 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 626 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 626 c] :
    ∀ c ∈ Finset.univ, (alphaQ 626 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 626 i (c.val i) t) =
      ((jwv 626 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 626 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 626 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 626 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 626 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_627 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 627),
        qvalQ (fun t ↦ ∑ i, PE 627 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 627),
        (alphaQ 627 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 627 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 627 = 2 := by decide +kernel
  have hce : certE (627 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-7 : Int) else if j.val = 1 then -5 else if j.val = 2 then 4 else 2) else (if j.val = 0 then -25 else if j.val = 1 then -6 else if j.val = 2 then 7 else 4)) := by decide +kernel
  have hs : (l2At (627 : Fin 1104)).2.2 = 7668411867 := by decide +kernel
  have hp : parent2 (627 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 627 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 627 c] :
    ∀ c ∈ Finset.univ, (alphaQ 627 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 627 i (c.val i) t) =
      ((jwv 627 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 627 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 627 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 627 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 627 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_628 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 628),
        qvalQ (fun t ↦ ∑ i, PE 628 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 628),
        (alphaQ 628 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 628 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 628 = 1 := by decide +kernel
  have hce : certE (628 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (628 : Fin 1104)).2.2 = 21076600723 := by decide +kernel
  have hp : parent2 (628 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 628 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 628 c] :
    ∀ c ∈ Finset.univ, (alphaQ 628 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 628 i (c.val i) t) =
      ((jwv 628 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 628 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 628 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 628 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 628 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_629 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 629),
        qvalQ (fun t ↦ ∑ i, PE 629 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 629),
        (alphaQ 629 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 629 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 629 = 0 := by decide +kernel
  have hce : certE (629 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (7 : Int) else if j.val = 1 then -2 else if j.val = 2 then 8 else -8) else (if j.val = 0 then 7 else if j.val = 1 then -8 else if j.val = 2 then 6 else -5)) := by decide +kernel
  have hs : (l2At (629 : Fin 1104)).2.2 = 18138867453 := by decide +kernel
  have hp : parent2 (629 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 629 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 629 c] :
    ∀ c ∈ Finset.univ, (alphaQ 629 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 629 i (c.val i) t) =
      ((jwv 629 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 629 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 629 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 629 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 629 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_630 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 630),
        qvalQ (fun t ↦ ∑ i, PE 630 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 630),
        (alphaQ 630 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 630 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 630 = 2 := by decide +kernel
  have hce : certE (630 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hs : (l2At (630 : Fin 1104)).2.2 = 20992527710 := by decide +kernel
  have hp : parent2 (630 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 630 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 630 c] :
    ∀ c ∈ Finset.univ, (alphaQ 630 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 630 i (c.val i) t) =
      ((jwv 630 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 630 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 630 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 630 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 630 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_631 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 631),
        qvalQ (fun t ↦ ∑ i, PE 631 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 631),
        (alphaQ 631 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 631 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 631 = 1 := by decide +kernel
  have hce : certE (631 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (631 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (631 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 631 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 631 c] :
    ∀ c ∈ Finset.univ, (alphaQ 631 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 631 i (c.val i) t) =
      ((jwv 631 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 631 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 631 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 631 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 631 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_632 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 632),
        qvalQ (fun t ↦ ∑ i, PE 632 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 632),
        (alphaQ 632 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 632 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 632 = 0 := by decide +kernel
  have hce : certE (632 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-13 : Int) else if j.val = 1 then 2 else if j.val = 2 then 3 else 1) else (if j.val = 0 then 13 else if j.val = 1 then 5 else if j.val = 2 then -3 else -7)) := by decide +kernel
  have hs : (l2At (632 : Fin 1104)).2.2 = 19335000475 := by decide +kernel
  have hp : parent2 (632 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 632 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 632 c] :
    ∀ c ∈ Finset.univ, (alphaQ 632 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 632 i (c.val i) t) =
      ((jwv 632 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 632 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 632 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 632 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 632 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_633 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 633),
        qvalQ (fun t ↦ ∑ i, PE 633 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 633),
        (alphaQ 633 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 633 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 633 = 2 := by decide +kernel
  have hce : certE (633 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 2 else if j.val = 2 then -1 else -3)) := by decide +kernel
  have hs : (l2At (633 : Fin 1104)).2.2 = 20992526893 := by decide +kernel
  have hp : parent2 (633 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 633 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 633 c] :
    ∀ c ∈ Finset.univ, (alphaQ 633 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 633 i (c.val i) t) =
      ((jwv 633 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 633 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 633 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 633 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 633 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_634 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 634),
        qvalQ (fun t ↦ ∑ i, PE 634 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 634),
        (alphaQ 634 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 634 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 634 = 1 := by decide +kernel
  have hce : certE (634 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-6 : Int) else if j.val = 1 then 2 else if j.val = 2 then 0 else 1) else (if j.val = 0 then -54 else if j.val = 1 then 7 else if j.val = 2 then 7 else 7)) := by decide +kernel
  have hs : (l2At (634 : Fin 1104)).2.2 = 7810862219 := by decide +kernel
  have hp : parent2 (634 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 634 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 634 c] :
    ∀ c ∈ Finset.univ, (alphaQ 634 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 634 i (c.val i) t) =
      ((jwv 634 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 634 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 634 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 634 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 634 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_635 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 635),
        qvalQ (fun t ↦ ∑ i, PE 635 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 635),
        (alphaQ 635 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 635 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 635 = 0 := by decide +kernel
  have hce : certE (635 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (3 : Int) else if j.val = 1 then 4 else if j.val = 2 then 2 else -5) else (if j.val = 0 then 25 else if j.val = 1 then 5 else if j.val = 2 then -7 else -8)) := by decide +kernel
  have hs : (l2At (635 : Fin 1104)).2.2 = 18102617206 := by decide +kernel
  have hp : parent2 (635 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 635 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 635 c] :
    ∀ c ∈ Finset.univ, (alphaQ 635 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 635 i (c.val i) t) =
      ((jwv 635 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 635 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 635 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 635 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 635 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_636 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 636),
        qvalQ (fun t ↦ ∑ i, PE 636 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 636),
        (alphaQ 636 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 636 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 636 = 2 := by decide +kernel
  have hce : certE (636 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (636 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (636 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 636 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 636 c] :
    ∀ c ∈ Finset.univ, (alphaQ 636 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 636 i (c.val i) t) =
      ((jwv 636 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 636 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 636 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 636 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 636 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_637 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 637),
        qvalQ (fun t ↦ ∑ i, PE 637 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 637),
        (alphaQ 637 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 637 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 637 = 1 := by decide +kernel
  have hce : certE (637 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-7 : Int) else if j.val = 1 then 2 else if j.val = 2 then -2 else 3) else (if j.val = 0 then 17 else if j.val = 1 then -2 else if j.val = 2 then 0 else -7)) := by decide +kernel
  have hs : (l2At (637 : Fin 1104)).2.2 = 17683794889 := by decide +kernel
  have hp : parent2 (637 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 637 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 637 c] :
    ∀ c ∈ Finset.univ, (alphaQ 637 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 637 i (c.val i) t) =
      ((jwv 637 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 637 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 637 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 637 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 637 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_638 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 638),
        qvalQ (fun t ↦ ∑ i, PE 638 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 638),
        (alphaQ 638 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 638 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 638 = 0 := by decide +kernel
  have hce : certE (638 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 13 else if j.val = 1 then 3 else if j.val = 2 then -4 else -5)) := by decide +kernel
  have hs : (l2At (638 : Fin 1104)).2.2 = 21054405342 := by decide +kernel
  have hp : parent2 (638 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 638 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 638 c] :
    ∀ c ∈ Finset.univ, (alphaQ 638 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 638 i (c.val i) t) =
      ((jwv 638 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 638 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 638 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 638 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 638 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_639 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 639),
        qvalQ (fun t ↦ ∑ i, PE 639 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 639),
        (alphaQ 639 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 639 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 639 = 2 := by decide +kernel
  have hce : certE (639 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then 0 else if j.val = 1 then 0 else if j.val = 2 then 0 else 0)) := by decide +kernel
  have hs : (l2At (639 : Fin 1104)).2.2 = 0 := by decide +kernel
  have hp : parent2 (639 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 639 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 639 c] :
    ∀ c ∈ Finset.univ, (alphaQ 639 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 639 i (c.val i) t) =
      ((jwv 639 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 639 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 639 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 639 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 639 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_640 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 640),
        qvalQ (fun t ↦ ∑ i, PE 640 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 640),
        (alphaQ 640 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 640 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 640 = 1 := by decide +kernel
  have hce : certE (640 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (640 : Fin 1104)).2.2 = 21076605642 := by decide +kernel
  have hp : parent2 (640 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 640 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 640 c] :
    ∀ c ∈ Finset.univ, (alphaQ 640 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 640 i (c.val i) t) =
      ((jwv 640 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 640 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 640 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 640 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 640 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_641 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 641),
        qvalQ (fun t ↦ ∑ i, PE 641 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 641),
        (alphaQ 641 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 641 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 641 = 0 := by decide +kernel
  have hce : certE (641 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -30 else if j.val = 1 then 2 else if j.val = 2 then -7 else 7)) := by decide +kernel
  have hs : (l2At (641 : Fin 1104)).2.2 = 88359 := by decide +kernel
  have hp : parent2 (641 : Fin 1104) = ![2, 1, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_211 641 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 641 c] :
    ∀ c ∈ Finset.univ, (alphaQ 641 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 641 i (c.val i) t) =
      ((jwv 641 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 641 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 641 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 641 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 641 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_642 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 642),
        qvalQ (fun t ↦ ∑ i, PE 642 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 642),
        (alphaQ 642 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 642 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 642 = 2 := by decide +kernel
  have hce : certE (642 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (0 : Int) else if j.val = 1 then 0 else if j.val = 2 then 0 else 0) else (if j.val = 0 then -44 else if j.val = 1 then 6 else if j.val = 2 then 0 else 4)) := by decide +kernel
  have hs : (l2At (642 : Fin 1104)).2.2 = 99492 := by decide +kernel
  have hp : parent2 (642 : Fin 1104) = ![1, 1, 2] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_112 642 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 642 c] :
    ∀ c ∈ Finset.univ, (alphaQ 642 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 642 i (c.val i) t) =
      ((jwv 642 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 642 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 642 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 642 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 642 i (a i) t)),
    sum_triP, sum_triP]
  simp only [PE_sum]
  unfold PE
  rw [hcm, hce, hp]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  rw [j1, j2, j3, j4, hs]
  norm_num [qvalQ, D, Fin.forall_fin_succ, Fin.ext_iff]

theorem pcert_643 :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 643),
        qvalQ (fun t ↦ ∑ i, PE 643 i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 643),
        (alphaQ 643 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 643 i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  have hcm : certMode 643 = 1 := by decide +kernel
  have hce : certE (643 : Fin 1104) = fun (a : Fin 3) (j : Fin 4) => (if a.val = 1 then (if j.val = 0 then (-19 : Int) else if j.val = 1 then 2 else if j.val = 2 then 8 else -1) else (if j.val = 0 then 2 else if j.val = 1 then 5 else if j.val = 2 then 3 else -8)) := by decide +kernel
  have hs : (l2At (643 : Fin 1104)).2.2 = 21076605888 := by decide +kernel
  have hp : parent2 (643 : Fin 1104) = ![1, 2, 1] := by decide +kernel
  obtain ⟨j1, j2, j3, j4⟩ := jwv_121 643 hp
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [alphaQ_jwv 643 c] :
    ∀ c ∈ Finset.univ, (alphaQ 643 c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 643 i (c.val i) t) =
      ((jwv 643 c.val : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 643 i (c.val i) t))]
  rw [mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ qvalQ (fun t ↦ ∑ i, PE 643 i (a i) t)),
    mme_released_recursive_level2_marginals.1
      (fun a : Tri ↦ ((jwv 643 a : ℚ) / (D : ℚ)) ^ 2 / qvalQ (fun t ↦ ∑ i, PE 643 i (a i) t)),
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
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 ⟨598 + j.val, by omega⟩),
        qvalQ (fun t ↦ ∑ i, PE ⟨598 + j.val, by omega⟩ i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 ⟨598 + j.val, by omega⟩),
        (alphaQ ⟨598 + j.val, by omega⟩ c) ^ 2 /
          qvalQ (fun t ↦ ∑ i, PE ⟨598 + j.val, by omega⟩ i (c.val i) t)) ≤
      1/(5 * 10^7) := by
  intro j
  match j with
  | ⟨0, _⟩ => exact MME.L2Cert.pcert_598
  | ⟨1, _⟩ => exact MME.L2Cert.pcert_599
  | ⟨2, _⟩ => exact MME.L2Cert.pcert_600
  | ⟨3, _⟩ => exact MME.L2Cert.pcert_601
  | ⟨4, _⟩ => exact MME.L2Cert.pcert_602
  | ⟨5, _⟩ => exact MME.L2Cert.pcert_603
  | ⟨6, _⟩ => exact MME.L2Cert.pcert_604
  | ⟨7, _⟩ => exact MME.L2Cert.pcert_605
  | ⟨8, _⟩ => exact MME.L2Cert.pcert_606
  | ⟨9, _⟩ => exact MME.L2Cert.pcert_607
  | ⟨10, _⟩ => exact MME.L2Cert.pcert_608
  | ⟨11, _⟩ => exact MME.L2Cert.pcert_609
  | ⟨12, _⟩ => exact MME.L2Cert.pcert_610
  | ⟨13, _⟩ => exact MME.L2Cert.pcert_611
  | ⟨14, _⟩ => exact MME.L2Cert.pcert_612
  | ⟨15, _⟩ => exact MME.L2Cert.pcert_613
  | ⟨16, _⟩ => exact MME.L2Cert.pcert_614
  | ⟨17, _⟩ => exact MME.L2Cert.pcert_615
  | ⟨18, _⟩ => exact MME.L2Cert.pcert_616
  | ⟨19, _⟩ => exact MME.L2Cert.pcert_617
  | ⟨20, _⟩ => exact MME.L2Cert.pcert_618
  | ⟨21, _⟩ => exact MME.L2Cert.pcert_619
  | ⟨22, _⟩ => exact MME.L2Cert.pcert_620
  | ⟨23, _⟩ => exact MME.L2Cert.pcert_621
  | ⟨24, _⟩ => exact MME.L2Cert.pcert_622
  | ⟨25, _⟩ => exact MME.L2Cert.pcert_623
  | ⟨26, _⟩ => exact MME.L2Cert.pcert_624
  | ⟨27, _⟩ => exact MME.L2Cert.pcert_625
  | ⟨28, _⟩ => exact MME.L2Cert.pcert_626
  | ⟨29, _⟩ => exact MME.L2Cert.pcert_627
  | ⟨30, _⟩ => exact MME.L2Cert.pcert_628
  | ⟨31, _⟩ => exact MME.L2Cert.pcert_629
  | ⟨32, _⟩ => exact MME.L2Cert.pcert_630
  | ⟨33, _⟩ => exact MME.L2Cert.pcert_631
  | ⟨34, _⟩ => exact MME.L2Cert.pcert_632
  | ⟨35, _⟩ => exact MME.L2Cert.pcert_633
  | ⟨36, _⟩ => exact MME.L2Cert.pcert_634
  | ⟨37, _⟩ => exact MME.L2Cert.pcert_635
  | ⟨38, _⟩ => exact MME.L2Cert.pcert_636
  | ⟨39, _⟩ => exact MME.L2Cert.pcert_637
  | ⟨40, _⟩ => exact MME.L2Cert.pcert_638
  | ⟨41, _⟩ => exact MME.L2Cert.pcert_639
  | ⟨42, _⟩ => exact MME.L2Cert.pcert_640
  | ⟨43, _⟩ => exact MME.L2Cert.pcert_641
  | ⟨44, _⟩ => exact MME.L2Cert.pcert_642
  | ⟨45, _⟩ => exact MME.L2Cert.pcert_643
  | ⟨n + 46, h⟩ => exact absurd h (by omega)

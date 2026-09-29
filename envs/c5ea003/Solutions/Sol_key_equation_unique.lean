-- Prove2me | solution 1 for key_equation_unique
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:15:18.018807+00:00
-- url     : https://prove2.me/submissions/5e1f90bf-19f3-41ff-b5f3-f04da37b73fa

-- Sol generated from Bridges/ReedSolomonKeyEquation/Basic.lean
import Mathlib
import Definitions.Def_Bridges_ReedSolomonKeyEquation_Basic
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.

# Reed–Solomon Key Equation: Formal Decoding as Linear Algebra and Vanishing Geometry

This file formalizes the core algebraic machinery behind Reed–Solomon decoding,
centering on the **key equation** that transforms the nonlinear problem of
locating errors into a system of linear constraints on polynomial coefficients.

## Main results

* `errorLocator` — the error-locator polynomial ∏_{i ∈ S} (X - C(a_i))
* `keyEquationHolds` — the predicate Q(a_i) = r(i) · E(a_i) for all i
* `key_equation_pointwise` — the pointwise key equation from an error set
* `polynomial_eq_zero_of_natDegree_lt_and_eval_eq_zero_on_finset` — vanishing rigidity
* `key_equation_unique` — uniqueness of key-equation solutions under decoding bounds
* `decoded_polynomial_unique` — uniqueness of the decoded message polynomial

## Mathematical significance

The key equation recasts error correction as a theorem about low-degree polynomials:
corrupted evaluation data, when multiplied by an appropriate annihilating polynomial,
satisfies a global polynomial identity. The uniqueness theorem shows that under the
classical decoding bound 2t + k ≤ n, any two solutions to the key equation must
satisfy Q₁E₂ = Q₂E₁, yielding unique recovery of the transmitted message.
-/


open Polynomial Classical

noncomputable section

variable {F : Type*} [Field F]

/-! ## Definitions -/




/-! ## Evaluation lemmas for the error-locator polynomial -/




/-! ## Degree bound for the error-locator -/


/-! ## Theorem 1: Pointwise key equation from an error set -/


/-! ## Theorem 2: Vanishing-on-many-points forces polynomial to be zero -/


/-! ## Key lemma for uniqueness: the cross-difference vanishes everywhere -/


omit [Field F] in
theorem evalPointsFinset_card {n : ℕ} (a : Fin n → F) (ha : Function.Injective a) :
    (evalPointsFinset a).card = n := by
  unfold evalPointsFinset
  rw [Finset.card_image_of_injective _ ha, Finset.card_univ, Fintype.card_fin]


/-- The cross-difference D = Q₁E₂ - Q₂E₁ vanishes at all evaluation points. -/
theorem cross_diff_eval_eq_zero
    {n : ℕ}
    (a : Fin n → F)
    (r : Fin n → F)
    (Q1 Q2 E1 E2 : F[X])
    (hsol1 : ∀ i : Fin n, Polynomial.eval (a i) Q1 = r i * Polynomial.eval (a i) E1)
    (hsol2 : ∀ i : Fin n, Polynomial.eval (a i) Q2 = r i * Polynomial.eval (a i) E2)
    (i : Fin n) :
    Polynomial.eval (a i) (Q1 * E2 - Q2 * E1) = 0 := by
  simp only [eval_sub, eval_mul, hsol1 i, hsol2 i]
  ring

/-
The natDegree of Q₁E₂ - Q₂E₁ is bounded under the degree constraints.
-/
theorem cross_diff_natDegree_bound
    {k t : ℕ}
    (Q1 Q2 E1 E2 : F[X])
    (hdegQ1 : Q1.natDegree < k + t)
    (hdegQ2 : Q2.natDegree < k + t)
    (hdegE1 : E1.natDegree ≤ t)
    (hdegE2 : E2.natDegree ≤ t) :
    (Q1 * E2 - Q2 * E1).natDegree < k + 2 * t := by
  refine' lt_of_le_of_lt ( Polynomial.natDegree_sub_le _ _ ) _;
  exact max_lt ( lt_of_le_of_lt ( Polynomial.natDegree_mul_le .. ) ( by linarith ) ) ( lt_of_le_of_lt ( Polynomial.natDegree_mul_le .. ) ( by linarith ) )

/-! ## Theorem 3: Uniqueness of the key-equation solution under decoding bounds -/


/-! ## Corollary: Decoded polynomial uniqueness -/

/-
**Decoded polynomial uniqueness.** If two key-equation solutions factor as Q₁ = p₁E₁
and Q₂ = p₂E₂ with deg p₁, deg p₂ < k, then under the decoding bound, p₁ = p₂.

This is the operational consequence of key equation uniqueness: the transmitted
message polynomial is uniquely recoverable from any valid key-equation solution.
-/


theorem solution    {n k t : ℕ}
    (a : Fin n → F)
    (ha : Function.Injective a)
    (r : Fin n → F)
    (Q1 Q2 E1 E2 : F[X])
    (_hE1 : E1 ≠ 0) (_hE2 : E2 ≠ 0)
    (hdegQ1 : Q1.natDegree < k + t)
    (hdegQ2 : Q2.natDegree < k + t)
    (hdegE1 : E1.natDegree ≤ t)
    (hdegE2 : E2.natDegree ≤ t)
    (hbound : k + 2 * t ≤ n)
    (hsol1 : ∀ i : Fin n, Polynomial.eval (a i) Q1 = r i * Polynomial.eval (a i) E1)
    (hsol2 : ∀ i : Fin n, Polynomial.eval (a i) Q2 = r i * Polynomial.eval (a i) E2) :
    Q1 * E2 = Q2 * E1 := by
  set D := Q1 * E2 - Q2 * E1 with hD_def
  have hD_van : ∀ x ∈ evalPointsFinset a, Polynomial.eval x D = 0 := by
    intro x hx
    simp [evalPointsFinset] at hx
    obtain ⟨i, rfl⟩ := hx
    exact cross_diff_eval_eq_zero a r Q1 Q2 E1 E2 hsol1 hsol2 i
  have hD_deg : D.natDegree < (evalPointsFinset a).card := by
    rw [evalPointsFinset_card a ha]
    exact lt_of_lt_of_le
      (cross_diff_natDegree_bound Q1 Q2 E1 E2 hdegQ1 hdegQ2 hdegE1 hdegE2) hbound
  have hD_zero : D = 0 :=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' D _ hD_van hD_deg
  exact sub_eq_zero.mp hD_zero

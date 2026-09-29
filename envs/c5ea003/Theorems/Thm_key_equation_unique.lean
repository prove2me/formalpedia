-- Prove2me | Theorems.Thm_key_equation_unique
-- name    : key_equation_unique
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:33:47.514924+00:00
-- url     : https://prove2.me/theorems/a7cbb77e-502f-4837-bdb6-2cedd5bd1aff
-- title:
--   Key equation uniqueness.
-- statement:
--   **Key equation uniqueness.** Given two solutions (Q₁, E₁) and (Q₂, E₂) to the key equation
--   with the degree bounds deg Q < k + t and deg E ≤ t, under the decoding bound k + 2t ≤ n,
--   we must have Q₁ · E₂ = Q₂ · E₁. This is the algebraic heart of unique decoding.
--
--   The proof proceeds by the "polynomial rigidity" argument:
--   1. Define D = Q₁E₂ - Q₂E₁.
--   2. Show D vanishes at all n evaluation points (from the key equation).
--   3. Bound deg D < k + 2t.
--   4. Since k + 2t ≤ n, D has more roots than its degree, hence D = 0.
--
--   ```lean
--   theorem key_equation_unique    {n k t : ℕ}
--       (a : Fin n → F)
--       (ha : Function.Injective a)
--       (r : Fin n → F)
--       (Q1 Q2 E1 E2 : F[X])
--       (_hE1 : E1 ≠ 0) (_hE2 : E2 ≠ 0)
--       (hdegQ1 : Q1.natDegree < k + t)
--       (hdegQ2 : Q2.natDegree < k + t)
--       (hdegE1 : E1.natDegree ≤ t)
--       (hdegE2 : E2.natDegree ≤ t)
--       (hbound : k + 2 * t ≤ n)
--       (hsol1 : ∀ i : Fin n, Polynomial.eval (a i) Q1 = r i * Polynomial.eval (a i) E1)
--       (hsol2 : ∀ i : Fin n, Polynomial.eval (a i) Q2 = r i * Polynomial.eval (a i) E2) :
--       Q1 * E2 = Q2 * E1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/ReedSolomonKeyEquation/Basic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/ReedSolomonKeyEquation/Basic.lean#L177

-- Thm stub generated from Bridges/ReedSolomonKeyEquation/Basic.lean
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





/-
The natDegree of Q₁E₂ - Q₂E₁ is bounded under the degree constraints.
-/

/-! ## Theorem 3: Uniqueness of the key-equation solution under decoding bounds -/

theorem key_equation_unique    {n k t : ℕ}
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
    Q1 * E2 = Q2 * E1 := by sorry

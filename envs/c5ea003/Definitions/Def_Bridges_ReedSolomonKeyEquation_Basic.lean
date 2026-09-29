-- Prove2me | Definitions.Def_Bridges_ReedSolomonKeyEquation_Basic
-- name    : Bridges_ReedSolomonKeyEquation_Basic
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:37:29.247307+00:00
-- url     : https://prove2.me/theorems/735aad39-ea23-40ff-b08d-926116e938f3
-- title:
--   Aether Catalog definitions — Bridges_ReedSolomonKeyEquation_Basic
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ReedSolomonKeyEquation.Basic`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ReedSolomonKeyEquation/Basic.lean by skeleton subtraction
import Mathlib
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

/-- The error-locator polynomial: the product ∏_{i ∈ S} (X - C(a_i)) over the error set S.
This polynomial vanishes exactly at the evaluation points corresponding to errors. -/
def errorLocator {n : ℕ} (a : Fin n → F) (S : Finset (Fin n)) : F[X] :=
  S.prod (fun i => X - C (a i))



/-! ## Evaluation lemmas for the error-locator polynomial -/




/-! ## Degree bound for the error-locator -/


/-! ## Theorem 1: Pointwise key equation from an error set -/


/-! ## Theorem 2: Vanishing-on-many-points forces polynomial to be zero -/


/-! ## Key lemma for uniqueness: the cross-difference vanishes everywhere -/

/-- The image of injective evaluation points as a finset in F. -/
def evalPointsFinset {n : ℕ} (a : Fin n → F) : Finset F :=
  Finset.univ.image a




/-
The natDegree of Q₁E₂ - Q₂E₁ is bounded under the degree constraints.
-/

/-! ## Theorem 3: Uniqueness of the key-equation solution under decoding bounds -/


/-! ## Corollary: Decoded polynomial uniqueness -/

/-
**Decoded polynomial uniqueness.** If two key-equation solutions factor as Q₁ = p₁E₁
and Q₂ = p₂E₂ with deg p₁, deg p₂ < k, then under the decoding bound, p₁ = p₂.

This is the operational consequence of key equation uniqueness: the transmitted
message polynomial is uniquely recoverable from any valid key-equation solution.
-/

end



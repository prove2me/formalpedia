-- Prove2me | Theorems.Thm_CoeffExtraction_coeff_eq_sum_eval_div_lagrangeDen
-- name    : CoeffExtraction.coeff_eq_sum_eval_div_lagrangeDen
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:41:02.736948+00:00
-- url     : https://prove2.me/theorems/f904773f-5307-40d3-a07d-820d005e23e2
-- title:
--   Coeff eq sum eval div lagrangeDen
-- statement:
--   Formal statement of `CoeffExtraction.coeff_eq_sum_eval_div_lagrangeDen` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem CoeffExtraction.coeff_eq_sum_eval_div_lagrangeDen    (S : Finset K) (hS : S.Nonempty)
--       (p : Polynomial K)
--       (hdeg : p.natDegree < S.card) :
--       p.coeff (S.card - 1) =
--         ∑ s ∈ S, p.eval s * (lagrangeDen S s)⁻¹ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/CoeffExtraction.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/CoeffExtraction.lean#L133

-- Thm stub generated from Bridges/CoeffExtraction.lean
import Mathlib
import Definitions.Def_Bridges_CoeffExtraction
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Coefficient Extraction and the Combinatorial Nullstellensatz

This file formalizes the **coefficient extraction identity** for univariate polynomials
over a field, and derives the Combinatorial Nullstellensatz as a corollary.

## Main results

* `CoeffExtraction.lagrangeDen_ne_zero` : The Lagrange denominator is nonzero for elements
  of a Finset.
* `CoeffExtraction.gridPoly_dvd_of_roots` : The vanishing polynomial divides any polynomial that
  vanishes on the entire set.
* `CoeffExtraction.coeff_eq_sum_eval_div_lagrangeDen` : **The Univariate Coefficient Extraction
  Theorem.** For `p` with `natDegree p < |S|`:
  `p.coeff (|S| - 1) = ∑ s ∈ S, p.eval s * (lagrangeDen S s)⁻¹`
* `CoeffExtraction.exists_eval_ne_zero_of_coeff_ne_zero_univ` : **Univariate Combinatorial
  Nullstellensatz.** Nonzero top coefficient implies a nonzero evaluation in `S`.
* `CoeffExtraction.exists_eval_ne_zero_mv` : **Multivariate Combinatorial Nullstellensatz.**
  Nonzero grid evaluation existence from nonzero top monomial coefficient.

## References

* N. Alon, "Combinatorial Nullstellensatz", Combin. Probab. Comput. 8 (1999), 7–29.

## Tags

combinatorial nullstellensatz, coefficient extraction, Lagrange interpolation, polynomial method
-/


open Polynomial Finset BigOperators

open CoeffExtraction

variable {K : Type*} [Field K] [DecidableEq K]

/-! ## §1. Lagrange denominator -/



/-! ## §2. Grid polynomial (vanishing polynomial) -/



/-
If a polynomial vanishes on all elements of `S`, then `∏_{s ∈ S} (X - s)` divides it.
-/

/-! ## §3. Lagrange basis coefficient -/

/-
The leading coefficient of `Lagrange.basisDivisor a b` is `(a - b)⁻¹`.
-/

/-
The natDegree of `Lagrange.basisDivisor a b` is 1 when `a ≠ b`.
-/

/-
The leading coefficient of `Lagrange.basis S id s` for `s ∈ S` is
  `(lagrangeDen S s)⁻¹ = (∏_{t ∈ S.erase s} (s - t))⁻¹`.
-/

/-
The natDegree of `Lagrange.basis S id s` for `s ∈ S` is `|S| - 1`.
-/


/-! ## §4. Univariate coefficient extraction -/

/-
**Univariate Coefficient Extraction Theorem.**
For a polynomial `p` with `p.natDegree < |S|`, the coefficient of `X^{|S|-1}` equals
the weighted sum of evaluations divided by Lagrange denominators:

  `p.coeff (|S| - 1) = ∑ s ∈ S, p.eval s * (lagrangeDen S s)⁻¹`

This is the algebraic engine behind the Combinatorial Nullstellensatz.
-/

theorem CoeffExtraction.coeff_eq_sum_eval_div_lagrangeDen    (S : Finset K) (hS : S.Nonempty)
    (p : Polynomial K)
    (hdeg : p.natDegree < S.card) :
    p.coeff (S.card - 1) =
      ∑ s ∈ S, p.eval s * (lagrangeDen S s)⁻¹ := by sorry

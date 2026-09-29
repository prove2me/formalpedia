-- Prove2me | Theorems.Thm_CoeffExtraction_exists_eval_ne_zero_mv
-- name    : CoeffExtraction.exists_eval_ne_zero_mv
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:41:03.221428+00:00
-- url     : https://prove2.me/theorems/5043841f-2d73-4d4f-a839-15b16f10e2df
-- title:
--   Exists eval ne zero mv
-- statement:
--   Formal statement of `CoeffExtraction.exists_eval_ne_zero_mv` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem CoeffExtraction.exists_eval_ne_zero_mv    (S : ι → Finset K)
--       (hS : ∀ i, (S i).Nonempty)
--       (f : MvPolynomial ι K)
--       (hdeg : ∀ i, f.degreeOf i ≤ (S i).card - 1)
--       (hcoeff : MvPolynomial.coeff
--         (Finsupp.equivFunOnFinite.invFun (fun i => (S i).card - 1)) f ≠ 0) :
--       ∃ x ∈ grid S, MvPolynomial.eval x f ≠ 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/CoeffExtraction.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/CoeffExtraction.lean#L193

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

/-! ## §5. Univariate Nullstellensatz -/

/-
**Univariate Combinatorial Nullstellensatz.**
If `p` has degree `< |S|` and the coefficient of `X^{|S|-1}` is nonzero,
then `p` has a nonzero evaluation point in `S`.
-/

/-! ## §6. Multivariate definitions and Nullstellensatz -/

variable {ι : Type*} [DecidableEq ι] [Fintype ι]



/-
**Multivariate Combinatorial Nullstellensatz** (Alon's theorem).

If `f` is a multivariate polynomial over a field `K` and `S : ι → Finset K`
assigns a nonempty finite set to each variable, and if the coefficient of the
monomial `∏ i, X_i^{|S i| - 1}` in `f` is nonzero (with each variable degree
bounded by `|S i| - 1`), then there exists an evaluation point `x` in the
Cartesian product `∏ i, S i` where `f(x) ≠ 0`.

This is the key consequence of the coefficient extraction identity.
-/

theorem CoeffExtraction.exists_eval_ne_zero_mv    (S : ι → Finset K)
    (hS : ∀ i, (S i).Nonempty)
    (f : MvPolynomial ι K)
    (hdeg : ∀ i, f.degreeOf i ≤ (S i).card - 1)
    (hcoeff : MvPolynomial.coeff
      (Finsupp.equivFunOnFinite.invFun (fun i => (S i).card - 1)) f ≠ 0) :
    ∃ x ∈ grid S, MvPolynomial.eval x f ≠ 0 := by sorry

-- Prove2me | Theorems.Thm_coeff_restrictToLine_eq_eval_homogeneousComponent
-- name    : coeff_restrictToLine_eq_eval_homogeneousComponent
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T20:01:58.195331+00:00
-- url     : https://prove2.me/theorems/9f74c064-3c8d-4776-92ac-357359616ad7
-- title:
--   Coeff restrictToLine eq eval homogeneousComponent
-- statement:
--   Formal statement of `coeff_restrictToLine_eq_eval_homogeneousComponent` from the Aether Catalog (MachineLearning). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem coeff_restrictToLine_eq_eval_homogeneousComponent    (P : MvPolynomial σ F) (x v : σ → F) (d : ℕ)
--       (hP : P.totalDegree ≤ d) :
--       Polynomial.coeff (restrictToLine P x v) d =
--       MvPolynomial.eval v (MvPolynomial.homogeneousComponent d P) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/NumberTheory/CoeffRestriction.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/NumberTheory/CoeffRestriction.lean#L193

-- Thm stub generated from MachineLearning/NumberTheory/CoeffRestriction.lean
import Mathlib
import Definitions.Def_MachineLearning_NumberTheory_CoeffRestriction
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Leading-Coefficient Rigidity for Line Restrictions of Multivariate Polynomials

This file proves the key coefficient-extraction identity for the polynomial method
in finite-field Kakeya theory:

The d-th coefficient of a multivariate polynomial P restricted to an affine line
x + t*v equals the evaluation of the degree-d homogeneous component of P at the
direction vector v, provided P has total degree ≤ d.

This is the formal bridge between:
1. Multivariate degree filtration (homogeneous components)
2. Affine-line restriction (eval₂ substitution)
3. Directional evaluation of the top homogeneous form

## Main results

* `coeff_restrictToLine_eq_eval_homogeneousComponent` — the main coefficient identity
* `leading_coeff_restrictToLine` — specialization when totalDegree = d
* `eval_homogeneousComponent_eq_zero_of_line_vanishing` — vanishing corollary for Dvir's argument
-/


open MvPolynomial Polynomial Finset BigOperators

noncomputable section

variable {σ F : Type*} [Fintype σ] [DecidableEq σ] [CommSemiring F]


/-! ## Helper lemmas for univariate polynomial coefficients -/

/-
The natDegree of `C(a) + X * C(b)` is at most 1.
-/

/-
The coefficient of degree 1 in `C(a) + X * C(b)` is `b`.
-/

/-! ## Key coefficient extraction via sigma-product rewriting -/

/-
Rewrite `∏ i, f i ^ s i` as a product over the sigma finset.
-/

/-
The card of `univ.sigma (fun i => range (s i))` equals `∑ i, s i`.
-/

/-
The natDegree of the product `∏ i, (C(x i) + X * C(v i)) ^ s i` is at most `∑ i, s i`.
-/

/-
**Key coefficient lemma**: The coefficient of `X^(∑ s i)` in the product
    `∏ i, (C(x i) + X * C(v i)) ^ s i` is `∏ i, v i ^ s i`.

    Proof idea: Rewrite the product as a product over the sigma finset where each factor
    is `C(x j.1) + X * C(v j.1)` with natDegree ≤ 1. Apply `Polynomial.coeff_prod_of_natDegree_le`
    with `n = 1` to extract the coefficient at `card * 1 = ∑ s i`. The coefficient of degree 1
    in each factor is `v j.1`, and the sigma product of these gives `∏ i, v i ^ s i`.
-/

/-! ## Monomial restriction and homogeneous component -/

/-
The restriction of a monomial to a line.
-/

/-
For a monomial of total degree d, the d-th coefficient of its line restriction
    equals the evaluation of the monomial at v.

    Uses `coeff_prod_linear_pow_eq_prod` to extract the top coefficient
    and `MvPolynomial.eval_monomial` to identify the evaluation.
-/

/-
For a monomial of total degree < d, the d-th coefficient of its line restriction is 0.
-/

/-! ## The main theorems -/

/-
The restriction to a line distributes over finite sums.
-/

/-
`Finsupp.degree` on `σ →₀ ℕ` equals the univ sum for a `Fintype`.
-/

/-
**Main Theorem**: The d-th coefficient of a polynomial restricted to a line
    equals the evaluation of its degree-d homogeneous component at the direction vector,
    provided the polynomial has total degree at most d.

    This is the exact coefficient-extraction principle behind Dvir's argument:
    the top t-coefficient of the polynomial restricted to a line depends only on
    the degree-d homogeneous part of P, and is obtained by evaluating that
    homogeneous piece at the direction vector.

    Proof strategy: Decompose P into its monomial support. For each monomial of
    degree d, the d-th coefficient of its restriction equals its evaluation at v
    (by `coeff_restrictToLine_monomial_eq_eval_of_degree_eq`). For monomials of
    degree < d, the coefficient is 0 (by `coeff_restrictToLine_monomial_eq_zero_of_degree_lt`).
    The totalDegree ≤ d hypothesis ensures no monomials of degree > d exist.
    Reassembling gives the evaluation of `homogeneousComponent d P` at v.
-/
omit [DecidableEq σ] in

theorem coeff_restrictToLine_eq_eval_homogeneousComponent    (P : MvPolynomial σ F) (x v : σ → F) (d : ℕ)
    (hP : P.totalDegree ≤ d) :
    Polynomial.coeff (restrictToLine P x v) d =
    MvPolynomial.eval v (MvPolynomial.homogeneousComponent d P) := by sorry

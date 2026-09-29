-- Prove2me | solution 1 for coeff_restrictToLine_eq_eval_homogeneousComponent
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T03:50:35.174581+00:00
-- url     : https://prove2.me/submissions/91af9369-0086-407e-bce5-40b1b029d1c0

-- Sol generated from MachineLearning/NumberTheory/CoeffRestriction.lean
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
lemma natDegree_C_add_X_mul_C_le (a b : F) :
    (Polynomial.C a + Polynomial.X * Polynomial.C b : Polynomial F).natDegree ≤ 1 := by
  refine' le_trans ( Polynomial.natDegree_add_le _ _ ) _ ; by_cases h : b = 0 <;> simp +decide [ h ]

/-
The coefficient of degree 1 in `C(a) + X * C(b)` is `b`.
-/

/-! ## Key coefficient extraction via sigma-product rewriting -/

/-
Rewrite `∏ i, f i ^ s i` as a product over the sigma finset.
-/
omit [DecidableEq σ] in
lemma prod_pow_eq_prod_sigma_range {M : Type*} [CommMonoid M]
    (f : σ → M) (s : σ → ℕ) :
    ∏ i : σ, f i ^ s i =
    ∏ p ∈ Finset.univ.sigma (fun i => Finset.range (s i)), f p.1 := by
  rw [ Finset.prod_sigma ];
  simp +decide

/-
The card of `univ.sigma (fun i => range (s i))` equals `∑ i, s i`.
-/

/-
The natDegree of the product `∏ i, (C(x i) + X * C(v i)) ^ s i` is at most `∑ i, s i`.
-/
omit [DecidableEq σ] in
lemma natDegree_prod_linear_pow_le (x v : σ → F) (s : σ → ℕ) :
    (∏ i : σ, (Polynomial.C (x i) + Polynomial.X * Polynomial.C (v i)) ^ s i).natDegree
    ≤ ∑ i : σ, s i := by
  refine' le_trans ( Polynomial.natDegree_prod_le _ _ ) _;
  gcongr;
  refine' le_trans ( Polynomial.natDegree_pow_le ) _;
  exact mul_le_of_le_one_right' ( natDegree_C_add_X_mul_C_le _ _ )

/-
**Key coefficient lemma**: The coefficient of `X^(∑ s i)` in the product
    `∏ i, (C(x i) + X * C(v i)) ^ s i` is `∏ i, v i ^ s i`.

    Proof idea: Rewrite the product as a product over the sigma finset where each factor
    is `C(x j.1) + X * C(v j.1)` with natDegree ≤ 1. Apply `Polynomial.coeff_prod_of_natDegree_le`
    with `n = 1` to extract the coefficient at `card * 1 = ∑ s i`. The coefficient of degree 1
    in each factor is `v j.1`, and the sigma product of these gives `∏ i, v i ^ s i`.
-/
omit [DecidableEq σ] in
theorem coeff_prod_linear_pow_eq_prod
    (x v : σ → F) (s : σ → ℕ) :
    (∏ i : σ, (Polynomial.C (x i) + Polynomial.X * Polynomial.C (v i)) ^ s i).coeff
      (∑ i : σ, s i) =
    ∏ i : σ, v i ^ s i := by
  convert Polynomial.coeff_prod_of_natDegree_le ( Finset.univ.sigma fun i => Finset.range ( s i ) ) ( fun p => Polynomial.C ( x p.1 ) + Polynomial.X * Polynomial.C ( v p.1 ) ) 1 _ using 1;
  · simp +decide [ prod_pow_eq_prod_sigma_range ];
  · rw [ Finset.prod_sigma ];
    simp +decide;
  · intro p _; exact natDegree_C_add_X_mul_C_le _ _

/-! ## Monomial restriction and homogeneous component -/

/-
The restriction of a monomial to a line.
-/
omit [DecidableEq σ] in
lemma restrictToLine_monomial (x v : σ → F) (s : σ →₀ ℕ) (a : F) :
    restrictToLine ((MvPolynomial.monomial s) a) x v =
    Polynomial.C a * ∏ i : σ, (Polynomial.C (x i) + Polynomial.X * Polynomial.C (v i)) ^ s i := by
  -- By definition of restrictToLine, we have:
  simp [restrictToLine]

/-
For a monomial of total degree d, the d-th coefficient of its line restriction
    equals the evaluation of the monomial at v.

    Uses `coeff_prod_linear_pow_eq_prod` to extract the top coefficient
    and `MvPolynomial.eval_monomial` to identify the evaluation.
-/
omit [DecidableEq σ] in
lemma coeff_restrictToLine_monomial_eq_eval_of_degree_eq
    (x v : σ → F) (s : σ →₀ ℕ) (a : F) (d : ℕ)
    (hs : (Finsupp.degree s : ℕ) = d) :
    (restrictToLine ((MvPolynomial.monomial s) a) x v).coeff d =
    MvPolynomial.eval v ((MvPolynomial.monomial s) a) := by
  convert congr_arg ( fun x : F => a * x ) ( coeff_prod_linear_pow_eq_prod x v ( s : σ → ℕ ) ) using 1;
  · rw [ Finsupp.degree ] at hs;
    rw [ ← hs, restrictToLine_monomial ];
    simp +decide [ Polynomial.coeff_C_mul ];
    rw [ Finset.sum_subset ( Finset.subset_univ s.support ) ] ; aesop;
  · simp +decide [ MvPolynomial.eval_monomial ]

/-
For a monomial of total degree < d, the d-th coefficient of its line restriction is 0.
-/
omit [DecidableEq σ] in
lemma coeff_restrictToLine_monomial_eq_zero_of_degree_lt
    (x v : σ → F) (s : σ →₀ ℕ) (a : F) (d : ℕ)
    (hs : (Finsupp.degree s : ℕ) < d) :
    (restrictToLine ((MvPolynomial.monomial s) a) x v).coeff d = 0 := by
  rw [ restrictToLine_monomial ];
  refine' Polynomial.coeff_eq_zero_of_natDegree_lt _;
  refine' lt_of_le_of_lt ( Polynomial.natDegree_C_mul_le _ _ ) _;
  refine' lt_of_le_of_lt ( natDegree_prod_linear_pow_le x v s ) _;
  convert hs using 1;
  exact (Finsupp.degree_eq_sum s).symm

/-! ## The main theorems -/

/-
The restriction to a line distributes over finite sums.
-/
omit [Fintype σ] [DecidableEq σ] in
lemma restrictToLine_sum {ι : Type*} (x v : σ → F) (s : Finset ι) (f : ι → MvPolynomial σ F) :
    restrictToLine (∑ i ∈ s, f i) x v = ∑ i ∈ s, restrictToLine (f i) x v := by
  convert MvPolynomial.eval₂_sum _ _ _ _

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


/-! ## Vanishing corollary for Dvir's Kakeya argument -/


variable {F' : Type*}
  [CommRing F'] [IsDomain F'] [Fintype F'] [DecidableEq F']

/-
Evaluating the restriction at t gives the original polynomial at x + t * v.
-/

/-
The natDegree of the line restriction is at most the total degree.
-/

/-
**Dvir corollary**: If P has total degree ≤ d, vanishes on every point of the line
    `{x + t * v | t ∈ F}`, and d < |F|, then the degree-d homogeneous component
    evaluated at the direction v is zero.

    This converts line-vanishing into directional vanishing of the top homogeneous form,
    which is the core of Dvir's proof of the finite-field Kakeya lower bound |K| ≥ q^n/n!.

    Proof: The restricted polynomial has degree ≤ d and vanishes at all |F| > d
    field elements, so it is the zero polynomial. Its d-th coefficient is therefore 0.
    By the main theorem, this coefficient equals eval v (homogeneousComponent d P).
-/



omit [DecidableEq σ] in
theorem solution    (P : MvPolynomial σ F) (x v : σ → F) (d : ℕ)
    (hP : P.totalDegree ≤ d) :
    Polynomial.coeff (restrictToLine P x v) d =
    MvPolynomial.eval v (MvPolynomial.homogeneousComponent d P) := by
  -- Decompose P as ∑ s ∈ P.support, (monomial s) (P.coeff s) using MvPolynomial.as_sum or MvPolynomial.support_sum_monomial_coeff.
  have h_decomp : P = ∑ s ∈ P.support, (MvPolynomial.monomial s) (P.coeff s) := by
    exact as_sum P;
  conv_lhs => rw [ h_decomp, restrictToLine_sum ];
  rw [ Polynomial.finset_sum_coeff, MvPolynomial.homogeneousComponent_apply ];
  rw [ Finset.sum_filter, MvPolynomial.eval_sum ];
  refine' Finset.sum_congr rfl fun s hs => _;
  split_ifs with h;
  · convert coeff_restrictToLine_monomial_eq_eval_of_degree_eq x v s ( P.coeff s ) d h using 1;
  · convert coeff_restrictToLine_monomial_eq_zero_of_degree_lt x v s ( MvPolynomial.coeff s P ) d _;
    exact lt_of_le_of_ne ( le_trans ( MvPolynomial.le_totalDegree hs ) hP ) h

-- Prove2me | solution 1 for CoeffExtraction.coeff_eq_sum_eval_div_lagrangeDen
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:12:49.754214+00:00
-- url     : https://prove2.me/submissions/e0a891ae-ddee-40ba-8d92-c277883f846e

-- Sol generated from Bridges/CoeffExtraction.lean
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
theorem natDegree_basisDivisor {a b : K} (h : a ≠ b) :
    (Lagrange.basisDivisor a b).natDegree = 1 := by
  unfold Lagrange.basisDivisor;
  rw [ Polynomial.natDegree_C_mul, Polynomial.natDegree_X_sub_C ] ; simp +decide [ sub_ne_zero.mpr h ]

/-
The leading coefficient of `Lagrange.basis S id s` for `s ∈ S` is
  `(lagrangeDen S s)⁻¹ = (∏_{t ∈ S.erase s} (s - t))⁻¹`.
-/
theorem leadingCoeff_basis {S : Finset K} {s : K} (hs : s ∈ S) :
    (Lagrange.basis S id s).leadingCoeff = (lagrangeDen S s)⁻¹ := by
  unfold Lagrange.basis;
  simp +decide [ Finset.prod_apply, Polynomial.leadingCoeff_prod, Lagrange.basisDivisor ];
  rfl

/-
The natDegree of `Lagrange.basis S id s` for `s ∈ S` is `|S| - 1`.
-/
theorem natDegree_basis {S : Finset K} {s : K} (hs : s ∈ S) :
    (Lagrange.basis S id s).natDegree = S.card - 1 := by
  simp +decide [ Lagrange.basis, Polynomial.natDegree_prod', hs ];
  rw [ Polynomial.natDegree_prod, Finset.sum_congr rfl fun x hx => natDegree_basisDivisor ( by aesop ) ];
  · aesop;
  · exact fun x hx => mul_ne_zero ( Polynomial.C_ne_zero.mpr <| inv_ne_zero <| sub_ne_zero.mpr <| by aesop ) <| Polynomial.X_sub_C_ne_zero _

/-- For `s ∈ S`, the coefficient of `X^{|S|-1}` in `Lagrange.basis S id s`
  is `(lagrangeDen S s)⁻¹`. -/
theorem coeff_top_basis {S : Finset K} {s : K} (hs : s ∈ S) :
    (Lagrange.basis S id s).coeff (S.card - 1) = (lagrangeDen S s)⁻¹ := by
  rw [← natDegree_basis hs, ← Polynomial.leadingCoeff, leadingCoeff_basis hs]

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


open CoeffExtraction in
theorem solution    (S : Finset K) (hS : S.Nonempty)
    (p : Polynomial K)
    (hdeg : p.natDegree < S.card) :
    p.coeff (S.card - 1) =
      ∑ s ∈ S, p.eval s * (lagrangeDen S s)⁻¹ := by
  -- By Lagrange interpolation uniqueness (Lagrange.eq_interpolate_of_eval_eq), since p has degree < |S| (from hdeg : p.natDegree < S.card, use Polynomial.degree_lt_iff or natDegree_lt_iff) and evaluates to p.eval s at each s ∈ S, we get p = Lagrange.interpolate S id (fun s => p.eval s).
  have h_interpolate : p = Lagrange.interpolate S id (fun s => p.eval s) := by
    convert Lagrange.eq_interpolate_of_eval_eq _ _ _;
    any_goals assumption;
    rotate_left;
    exact id;
    exact fun s => p.eval s;
    · exact Set.injOn_id _;
    · exact lt_of_le_of_lt ( Polynomial.degree_le_natDegree ) ( WithBot.coe_lt_coe.mpr hdeg );
    · aesop;
  conv_lhs => rw [ h_interpolate, Lagrange.interpolate_apply ];
  rw [ Polynomial.finset_sum_coeff, Finset.sum_congr rfl ];
  intro x hx;
  rw [ Polynomial.coeff_C_mul, ← coeff_top_basis hx ]

-- Prove2me | solution 1 for CoeffExtraction.exists_eval_ne_zero_mv
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:16:42.17129+00:00
-- url     : https://prove2.me/submissions/e9bbcd5e-9bdf-4e5c-9f84-0a8d03549118

-- Sol generated from Bridges/CoeffExtraction.lean
import Mathlib
import Definitions.Def_Bridges_CoeffExtraction
import Theorems.Thm_CoeffExtraction_coeff_eq_sum_eval_div_lagrangeDen
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


open CoeffExtraction in
theorem solution    (S : ι → Finset K)
    (hS : ∀ i, (S i).Nonempty)
    (f : MvPolynomial ι K)
    (hdeg : ∀ i, f.degreeOf i ≤ (S i).card - 1)
    (hcoeff : MvPolynomial.coeff
      (Finsupp.equivFunOnFinite.invFun (fun i => (S i).card - 1)) f ≠ 0) :
    ∃ x ∈ grid S, MvPolynomial.eval x f ≠ 0 := by
  revert hcoeff;
  simp +decide [ MvPolynomial.degreeOf_eq_sup ] at hdeg ⊢;
  -- By definition of polynomial evaluation, we can write
  have h_eval : ∀ x : ι → K, (MvPolynomial.eval x) f = ∑ b ∈ f.support, (MvPolynomial.coeff b f) * (∏ i, x i ^ (b i)) := by
    simp +decide [ MvPolynomial.eval_eq' ];
  -- By definition of polynomial evaluation, we can write the sum as
  have h_sum : ∑ x ∈ grid S, (∏ i, (lagrangeDen (S i) (x i))⁻¹) * (MvPolynomial.eval x) f = ∑ b ∈ f.support, (MvPolynomial.coeff b f) * (∏ i, (∑ x ∈ S i, (lagrangeDen (S i) x)⁻¹ * x ^ (b i))) := by
    simp +decide only [grid, h_eval, Finset.mul_sum _ _ _, prod_sum];
    rw [ Finset.sum_comm ];
    refine' Finset.sum_congr rfl fun b hb => _;
    refine' Finset.sum_bij ( fun x hx => fun i _ => x i ) _ _ _ _ <;> simp +decide [ Finset.prod_mul_distrib ];
    · simp +contextual [ funext_iff ];
    · exact fun b hb => ⟨ fun i => b i ( Finset.mem_univ i ), hb, rfl ⟩;
    · exact fun _ _ => by ring;
  -- By definition of polynomial evaluation, we know that
  have h_eval : ∀ i, ∀ b : ℕ, b ≤ (S i).card - 1 → (∑ x ∈ S i, (lagrangeDen (S i) x)⁻¹ * x ^ b) = if b = (S i).card - 1 then 1 else 0 := by
    intro i b hb
    have h_eval : ∀ p : Polynomial K, p.natDegree < (S i).card → (∑ x ∈ S i, (lagrangeDen (S i) x)⁻¹ * p.eval x) = p.coeff ((S i).card - 1) := by
      grind +suggestions;
    convert h_eval ( Polynomial.X ^ b ) _ using 1 <;> simp +decide [ Polynomial.natDegree_X_pow ];
    · simp +decide only [eq_comm];
    · exact lt_of_le_of_lt hb ( Nat.pred_lt ( ne_bot_of_gt ( Finset.card_pos.mpr ( hS i ) ) ) );
  -- Apply the evaluation result to each term in the sum.
  have h_sum_eval : ∑ x ∈ grid S, (∏ i, (lagrangeDen (S i) (x i))⁻¹) * (MvPolynomial.eval x) f = (MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm fun i => (S i).card - 1) f) := by
    rw [ h_sum, Finset.sum_eq_single ( Finsupp.equivFunOnFinite.symm fun i => ( S i |> Finset.card ) - 1 ) ];
    · simp +decide [ h_eval ];
    · intro b hb hb';
      rw [ Finset.prod_eq_zero_iff.mpr ];
      · ring;
      · contrapose! hb';
        ext i; specialize hb' i; specialize h_eval i ( b i ) ( hdeg i b ( by aesop ) ) ; aesop;
    · simp +contextual [ MvPolynomial.coeff ];
  contrapose! h_sum_eval;
  rw [ Finset.sum_eq_zero fun x hx => by rw [ h_sum_eval.2 x hx, MulZeroClass.mul_zero ] ] ; simp +decide [ h_sum_eval.1 ];
  exact Ne.symm h_sum_eval.1

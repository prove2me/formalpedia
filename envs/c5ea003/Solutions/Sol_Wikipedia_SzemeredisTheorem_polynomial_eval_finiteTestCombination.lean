-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.polynomial_eval_finiteTestCombination
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:26:06.532222+00:00
-- url     : https://prove2.me/submissions/2862d45a-9506-4eda-9114-d9c8605a2aac

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_DenseModel
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_PolynomialApproximation
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Weierstrass

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section



/-!
# Polynomial approximation in the finite dense-model argument

This file formalizes the polynomial part of the dense-model theorem.  A
normalized linear combination of `[0,1]`-valued tests takes values in
`[-1,1]`.  Weierstrass therefore approximates its positive part by a fixed
real polynomial.  Expanding that polynomial reduces correlation with the
majorant to correlations with finite products of the original tests.

The resulting estimates are quantitative and finite.  In particular, the
degree and coefficient loss of the approximating polynomial remain visible;
no asymptotic assertion about a particular pseudorandom majorant is hidden here.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators Polynomial

/-! ## Finite products and polynomial expansions -/









@[simp]
theorem finiteTestCombination_apply
    {Ω τ : Type*} [Fintype τ]
    (q : τ → Ω → ℝ) (c : τ → ℝ) (x : Ω) :
    finiteTestCombination q c x = ∑ t, c t * q t x := by
  classical
  simp [finiteTestCombination]





/-- Exact ordered expansion of a power of a finite test combination. -/
theorem finiteTestCombination_pow_eq_sum_monomials
    {Ω τ : Type*} [Fintype τ]
    (q : τ → Ω → ℝ) (c : τ → ℝ)
    (n : ℕ) (x : Ω) :
    (finiteTestCombination q c x) ^ n =
      ∑ s : Fin n → τ,
        (∏ i, c (s i)) * testMonomial q s x := by
  classical
  rw [finiteTestCombination_apply, Fintype.sum_pow]
  apply Fintype.sum_congr
  intro s
  rw [Finset.prod_mul_distrib]
  rfl











/-! ## Bounded combinations and approximation of positive part -/













/-! ## Quantitative positive-part correlation -/













end Wikipedia.SzemeredisTheorem

end
/-!
# Polynomial approximation in the finite dense-model argument

This file formalizes the polynomial part of the dense-model theorem.  A
normalized linear combination of `[0,1]`-valued tests takes values in
`[-1,1]`.  Weierstrass therefore approximates its positive part by a fixed
real polynomial.  Expanding that polynomial reduces correlation with the
majorant to correlations with finite products of the original tests.

The resulting estimates are quantitative and finite.  In particular, the
degree and coefficient loss of the approximating polynomial remain visible;
no asymptotic assertion about a particular pseudorandom majorant is hidden here.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators Polynomial
/-! ## Finite products and polynomial expansions -/

open Wikipedia.SzemeredisTheorem in
/-- Exact pointwise expansion of a polynomial evaluated on a finite test
combination. -/
theorem solution
    {Ω τ : Type*} [Fintype τ]
    (p : ℝ[X]) (q : τ → Ω → ℝ) (c : τ → ℝ) (x : Ω) :
    p.eval (finiteTestCombination q c x) =
      ∑ n ∈ p.support,
        ∑ s : Fin n → τ,
          (p.coeff n * ∏ i, c (s i)) *
            testMonomial q s x := by
  classical
  rw [Polynomial.eval_eq_sum]
  change
    (∑ n ∈ p.support,
      p.coeff n * (finiteTestCombination q c x) ^ n) = _
  apply Finset.sum_congr rfl
  intro n hn
  rw [finiteTestCombination_pow_eq_sum_monomials,
    Finset.mul_sum]
  apply Fintype.sum_congr
  intro s
  ring

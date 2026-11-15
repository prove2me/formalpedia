-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.abs_finitePairing_polynomial_eval_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:27:52.686992+00:00
-- url     : https://prove2.me/submissions/4dbd07af-c852-43cd-99f5-84a9382ca2aa

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_DenseModel
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_PolynomialApproximation
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Weierstrass
import Theorems.Thm_Wikipedia_SzemeredisTheorem_finitePairing_polynomial_eval_finiteTestCombination

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





















/-- The sum of absolute ordered monomial coefficients is the corresponding
power of the coefficient `ℓ¹`-norm. -/
theorem sum_abs_coefficientMonomial
    {τ : Type*} [Fintype τ]
    (c : τ → ℝ) (n : ℕ) :
    ∑ s : Fin n → τ, |∏ i, c (s i)| =
      coefficientL1 c ^ n := by
  classical
  unfold coefficientL1
  rw [Fintype.sum_pow]
  apply Fintype.sum_congr
  intro s
  rw [Finset.abs_prod]





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
/-- Expanding a polynomial loses at most the coefficient `ℓ¹`-norm when the
coefficient vector of the test combination is normalized. -/
theorem solution
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    {q : τ → Ω → ℝ} {ν : Ω → ℝ}
    {η : ℝ} (p : ℝ[X]) (c : τ → ℝ)
    (hc : coefficientL1 c = 1)
    (hmono :
      HasMonomialCorrelationBound q ν p.natDegree η) :
    |finitePairing (ν - fun _ => 1)
        (fun x => p.eval (finiteTestCombination q c x))| ≤
      polynomialCoefficientL1 p * η := by
  classical
  rw [finitePairing_polynomial_eval_finiteTestCombination]
  calc
    |∑ n ∈ p.support,
        ∑ s : Fin n → τ,
          (p.coeff n * ∏ i, c (s i)) *
            finitePairing (ν - fun _ => 1)
              (testMonomial q s)| ≤
        ∑ n ∈ p.support,
          |∑ s : Fin n → τ,
            (p.coeff n * ∏ i, c (s i)) *
              finitePairing (ν - fun _ => 1)
                (testMonomial q s)| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ p.support, |p.coeff n| * η := by
      apply Finset.sum_le_sum
      intro n hn
      calc
        |∑ s : Fin n → τ,
            (p.coeff n * ∏ i, c (s i)) *
              finitePairing (ν - fun _ => 1)
                (testMonomial q s)| ≤
            ∑ s : Fin n → τ,
              |(p.coeff n * ∏ i, c (s i)) *
                finitePairing (ν - fun _ => 1)
                  (testMonomial q s)| := by
          exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ s : Fin n → τ,
              |p.coeff n| * |∏ i, c (s i)| * η := by
          apply Finset.sum_le_sum
          intro s hs
          rw [abs_mul, abs_mul]
          exact mul_le_mul_of_nonneg_left
            (hmono n
              (Polynomial.le_natDegree_of_mem_supp n hn) s)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        _ = |p.coeff n| *
              (∑ s : Fin n → τ, |∏ i, c (s i)|) * η := by
          rw [Finset.mul_sum, Finset.sum_mul]
        _ = |p.coeff n| * η := by
          rw [sum_abs_coefficientMonomial, hc, one_pow, mul_one]
    _ = polynomialCoefficientL1 p * η := by
      rw [polynomialCoefficientL1, Finset.sum_mul]

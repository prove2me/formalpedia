-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.norm_complexProductHigherOrderRemainder_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:16:29.564399+00:00
-- url     : https://prove2.me/submissions/7c912b64-a2ac-44c5-bd68-e7f0f4ddc4bb

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexLocalFactorControl
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexZetaModelComparison
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CongruenceAverage
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ExceptionalPrimes
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_FourierZetaParameters
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeAffineRank
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeLocalFactorBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LinearFormsExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedDivisibilityCRT
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedLocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourier
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ZetaNearOne
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Nat.GCD.Prime
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section


/-!
# Quantitative good-prime local-factor remainder

This file turns the rank-two common-zero estimate into the finite
inclusion--exclusion bound used by the local Euler-factor calculation.

We allow an arbitrary real coefficient `a q` on the zero indicator of each
form.  The empty support contributes exactly `1`, the singleton supports
contribute exactly `-(∑ q, a q) / p`, and every support of cardinality at
least two has density at most `1 / p²` at a rank-two good prime.  Hence the
remaining contribution is bounded by

`(∑ S, 2 ≤ S.card, ∏ q ∈ S, |a q|) / p²`.

This finite coefficient mass is also bounded by `∏ q, (1 + |a q|)`.  Taking
all coefficients equal to one recovers the unweighted avoidance product from
`LocalEulerFactors` and gives an explicit `2 ^ card κ / p²` error.  No
infinite Euler product or convergence statement is made here.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Weighted finite inclusion--exclusion -/







/-! ## Separating empty and singleton supports -/



@[simp]
theorem mem_higherOrderSelectedSupports
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (s : Finset κ) :
    s ∈ higherOrderSelectedSupports κ ↔ 2 ≤ s.card := by
  simp [higherOrderSelectedSupports]







/-! ## Quantitative remainder bounds -/



















/-! ## The existing unweighted local Euler factor -/







/-! ## CFZ specialization -/





end Wikipedia.SzemeredisTheorem

end
/-!
# Comparing Fourier local factors with zeta Euler models

For one pair of Fourier phases `z, w` and `r = 1 / p`, the first-order
arithmetic model is

`1 - r * (z + w - z * w)`.

The corresponding local factor of the zeta quotient is

`((1 - r * z) * (1 - r * w)) / (1 - r * z * w)`.

Their difference has the exact factorization

`r² z w (1 - z) (1 - w) / (1 - r z w)`.

At a prime, the Fourier phases have norm at most one.  The denominator is
therefore bounded below by `1/2`, and the difference is at most `8 / p²`,
uniformly in both Fourier parameters.

For a finite system of `m` forms, expanding the product separates the sum
of the singleton errors from supports of size at least two.  Above `p ≥ 7`,
the latter are bounded by `49 * 2^m / p²`.  This gives an explicit
finite-system comparison with the combined first-order model, and hence a
ratio comparison above the additional stability cutoff `p ≥ 6m`.

The final section combines this result with the affine rank-two calculation
from `ComplexLocalFactorControl`.  It remains entirely local: no infinite
prime-product identity and no multivariate Fourier integration is asserted.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## A generic finite-product second-order remainder -/

open Wikipedia.SzemeredisTheorem in
/-- If every `e q` has norm at most `B ≤ 1`, the supports of size at least
two contribute at most `2^m B²`. -/
theorem solution
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {e : κ → ℂ} {B : ℝ}
    (hB0 : 0 ≤ B) (hB1 : B ≤ 1)
    (he : ∀ q, ‖e q‖ ≤ B) :
    ‖complexProductHigherOrderRemainder e‖ ≤
      (2 : ℝ) ^ Fintype.card κ * B ^ 2 := by
  have hcard :
      (higherOrderSelectedSupports κ).card ≤
        2 ^ Fintype.card κ := by
    calc
      (higherOrderSelectedSupports κ).card ≤
          ((Finset.univ : Finset κ).powerset).card := by
        apply Finset.card_le_card
        intro s hs
        exact Finset.mem_powerset.mpr
          ((Finset.mem_filter.mp hs).1 |>
            Finset.mem_powerset.mp)
      _ = 2 ^ Fintype.card κ := by
        rw [Finset.card_powerset]
        simp
  unfold complexProductHigherOrderRemainder
  calc
    ‖∑ s ∈ higherOrderSelectedSupports κ,
        ∏ q ∈ s, e q‖ ≤
        ∑ s ∈ higherOrderSelectedSupports κ,
          ‖∏ q ∈ s, e q‖ :=
      norm_sum_le
        (higherOrderSelectedSupports κ)
        (fun s => ∏ q ∈ s, e q)
    _ ≤
        ∑ _s ∈ higherOrderSelectedSupports κ,
          B ^ 2 := by
      apply Finset.sum_le_sum
      intro s hs
      have hs2 : 2 ≤ s.card :=
        (mem_higherOrderSelectedSupports s).mp hs
      rw [norm_prod]
      calc
        (∏ q ∈ s, ‖e q‖) ≤ B ^ s.card :=
          (Finset.prod_le_prod
            (fun q _hq => norm_nonneg (e q))
            (fun q _hq => he q)).trans_eq (by
              simp)
        _ ≤ B ^ 2 :=
          pow_le_pow_of_le_one hB0 hB1 hs2
    _ =
        ((higherOrderSelectedSupports κ).card : ℝ) *
          B ^ 2 := by
      simp
    _ ≤
        (2 : ℝ) ^ Fintype.card κ * B ^ 2 := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hcard
      · positivity

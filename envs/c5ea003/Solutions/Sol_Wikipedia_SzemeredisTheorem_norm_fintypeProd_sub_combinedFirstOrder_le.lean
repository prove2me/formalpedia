-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.norm_fintypeProd_sub_combinedFirstOrder_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:50:06.126114+00:00
-- url     : https://prove2.me/submissions/8347d9bc-32d5-4d0f-89dc-6beed35d3770

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_fintype_prod_one_add_eq_firstOrder_add_remainder
import Theorems.Thm_Wikipedia_SzemeredisTheorem_norm_complexProductHigherOrderRemainder_le

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
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
/-- Abstract finite-product comparison.  Each factor is allowed a
first-order error `D`; the products of two or more factor errors are
controlled by `B²`. -/
theorem solution
    {κ : Type*} [Fintype κ]
    (Q a : κ → ℂ) (r : ℂ)
    {B D : ℝ}
    (hB0 : 0 ≤ B) (hB1 : B ≤ 1)
    (hQ : ∀ q, ‖Q q - 1‖ ≤ B)
    (hlinear :
      ∀ q, ‖Q q - (1 - r * a q)‖ ≤ D) :
    ‖(∏ q, Q q) -
        (1 - r * ∑ q, a q)‖ ≤
      Fintype.card κ * D +
        (2 : ℝ) ^ Fintype.card κ * B ^ 2 := by
  classical
  let e : κ → ℂ := fun q => Q q - 1
  have hprod :
      (∏ q, Q q) =
        1 + ∑ q, e q +
          complexProductHigherOrderRemainder e := by
    rw [show Q = fun q => 1 + e q by
      funext q
      simp [e]]
    exact fintype_prod_one_add_eq_firstOrder_add_remainder e
  have hsum :
      ‖∑ q, (e q + r * a q)‖ ≤
        Fintype.card κ * D := by
    calc
      ‖∑ q, (e q + r * a q)‖ ≤
          ∑ q, ‖e q + r * a q‖ :=
        norm_sum_le Finset.univ
          (fun q => e q + r * a q)
      _ ≤ ∑ _q : κ, D := by
        apply Finset.sum_le_sum
        intro q _hq
        have hrewrite :
            e q + r * a q =
              Q q - (1 - r * a q) := by
          simp [e]
          ring
        rw [hrewrite]
        exact hlinear q
      _ = Fintype.card κ * D := by
        simp
  have hrem :
      ‖complexProductHigherOrderRemainder e‖ ≤
        (2 : ℝ) ^ Fintype.card κ * B ^ 2 :=
    norm_complexProductHigherOrderRemainder_le
      hB0 hB1 (fun q => by simpa [e] using hQ q)
  rw [hprod]
  have hrearrange :
      (1 + ∑ q, e q +
          complexProductHigherOrderRemainder e) -
          (1 - r * ∑ q, a q) =
        (∑ q, (e q + r * a q)) +
          complexProductHigherOrderRemainder e := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  rw [hrearrange]
  exact
    (norm_add_le _ _).trans
      (add_le_add hsum hrem)

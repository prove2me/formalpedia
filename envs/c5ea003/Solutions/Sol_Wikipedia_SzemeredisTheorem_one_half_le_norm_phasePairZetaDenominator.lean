-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.one_half_le_norm_phasePairZetaDenominator
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:24:25.456576+00:00
-- url     : https://prove2.me/submissions/b3e53d1f-e06a-472d-8c18-2d16fbc50ba8

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
/-! ## One paired phase -/

open Wikipedia.SzemeredisTheorem in
/-- The zeta-model denominator has norm at least one half at a prime when
both phases lie in the unit ball. -/
theorem solution
    {p : ℕ} (hp : p.Prime)
    {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    (1 : ℝ) / 2 ≤
      ‖1 - (p : ℂ)⁻¹ * z * w‖ := by
  have hpR : 0 < (p : ℝ) := by
    exact_mod_cast hp.pos
  have hinv :
      ‖(p : ℂ)⁻¹ * z * w‖ ≤
        (1 : ℝ) / 2 := by
    calc
      ‖(p : ℂ)⁻¹ * z * w‖ =
          (1 / (p : ℝ)) * ‖z‖ * ‖w‖ := by
        rw [norm_mul, norm_mul, norm_inv,
          Complex.norm_natCast]
        ring
      _ ≤ (1 / (p : ℝ)) * 1 * 1 := by
        gcongr
      _ ≤ (1 : ℝ) / 2 := by
        simp only [mul_one]
        rw [div_le_iff₀ hpR]
        have hp2R : (2 : ℝ) ≤ (p : ℝ) := by
          exact_mod_cast hp.two_le
        nlinarith
  calc
    (1 : ℝ) / 2 ≤
        1 - ‖(p : ℂ)⁻¹ * z * w‖ := by
      linarith
    _ =
        ‖(1 : ℂ)‖ -
          ‖(p : ℂ)⁻¹ * z * w‖ := by
      rw [norm_one]
    _ ≤
        ‖1 - (p : ℂ)⁻¹ * z * w‖ :=
      norm_sub_norm_le _ _

-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.norm_fourierZetaSystemEulerLocalFactor_sub_firstOrder_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:54:46.655852+00:00
-- url     : https://prove2.me/submissions/2edd4994-7892-4fba-9ecd-969397936efd

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_norm_divisorMultiplicativePhase_le_one
import Theorems.Thm_Wikipedia_SzemeredisTheorem_divisorMultiplicativePhase_eq_cpow
import Theorems.Thm_Wikipedia_SzemeredisTheorem_norm_phaseZetaSystemEulerLocalFactor_sub_firstOrder_le

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section



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

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## A generic finite-product second-order remainder -/









/-! ## One paired phase -/















/-! ## Exact cpow coordinates -/



/-- Pull the `p⁻¹` term out of a shifted negative complex power. -/
theorem natCast_cpow_neg_one_add
    {p : ℕ} (hp : p ≠ 0) (u : ℂ) :
    (p : ℂ) ^ (-((1 : ℂ) + u)) =
      (p : ℂ)⁻¹ * (p : ℂ) ^ (-u) := by
  have hpC : (p : ℂ) ≠ 0 := by
    exact_mod_cast hp
  rw [show -((1 : ℂ) + u) =
      (-1 : ℂ) + (-u) by ring,
    Complex.cpow_add _ _ hpC,
    Complex.cpow_neg_one]

/-- The analogous identity for the denominator shift `1 + u + v`. -/
theorem natCast_cpow_neg_one_add_add
    {p : ℕ} (hp : p ≠ 0) (u v : ℂ) :
    (p : ℂ) ^ (-((1 : ℂ) + u + v)) =
      (p : ℂ)⁻¹ *
        (p : ℂ) ^ (-u) *
          (p : ℂ) ^ (-v) := by
  have hpC : (p : ℂ) ≠ 0 := by
    exact_mod_cast hp
  rw [show -((1 : ℂ) + u + v) =
      (-1 : ℂ) + ((-u) + (-v)) by ring,
    Complex.cpow_add _ _ hpC,
    Complex.cpow_neg_one,
    Complex.cpow_add _ _ hpC]
  ring

/-- The cpow zeta factor is exactly the elementary phase-coordinate
factor. -/
theorem pairedZetaEulerLocalFactor_eq_phase
    {p : ℕ} (hp : p ≠ 0) (u v : ℂ) :
    pairedZetaEulerLocalFactor p u v =
      phasePairZetaEulerLocalModel p
        ((p : ℂ) ^ (-u))
        ((p : ℂ) ^ (-v)) := by
  rw [pairedZetaEulerLocalFactor,
    phasePairZetaEulerLocalModel,
    natCast_cpow_neg_one_add hp,
    natCast_cpow_neg_one_add hp,
    natCast_cpow_neg_one_add_add hp]



/-- Exact identification of the cpow factor with the two divisor phases.
This is where the sign and `2π` normalization enter. -/
theorem fourierPairZetaEulerLocalFactor_eq_phase
    {R p : ℕ} (hR : 1 < R) (hp : p.Prime)
    (t u : ℝ) :
    fourierPairZetaEulerLocalFactor R p t u =
      phasePairZetaEulerLocalModel p
        (SmoothSieveCutoff.divisorMultiplicativePhase
          R p t)
        (SmoothSieveCutoff.divisorMultiplicativePhase
          R p u) := by
  rw [fourierPairZetaEulerLocalFactor,
    pairedZetaEulerLocalFactor_eq_phase hp.ne_zero,
    ← divisorMultiplicativePhase_eq_cpow hR hp.pos t,
    ← divisorMultiplicativePhase_eq_cpow hR hp.pos u]

/-! ## Finite systems -/





/-- Exact conversion of the system cpow model to phase coordinates. -/
theorem fourierZetaSystemEulerLocalFactor_eq_phase
    {κ : Type*} [Fintype κ]
    {R p : ℕ} (hR : 1 < R) (hp : p.Prime)
    (t u : κ → ℝ) :
    fourierZetaSystemEulerLocalFactor R p t u =
      phaseZetaSystemEulerLocalFactor p
        (fun q =>
          SmoothSieveCutoff.divisorMultiplicativePhase
            R p (t q))
        (fun q =>
          SmoothSieveCutoff.divisorMultiplicativePhase
            R p (u q)) := by
  apply Finset.prod_congr rfl
  intro q _hq
  exact fourierPairZetaEulerLocalFactor_eq_phase
    hR hp (t q) (u q)





















/-! ## Direct arithmetic/zeta comparison -/























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
/-! ## One paired phase -/
/-! ## Exact cpow coordinates -/
/-! ## Finite systems -/

open Wikipedia.SzemeredisTheorem in
/-- Fourier-uniform version of the finite-system difference estimate. -/
theorem solution
    {κ : Type*} [Fintype κ]
    {R p : ℕ} (hR : 2 ≤ R) (hp : p.Prime)
    (hseven : 7 ≤ p)
    (t u : κ → ℝ) :
    ‖fourierZetaSystemEulerLocalFactor R p t u -
        pairedFourierFirstOrderLocalModel R p t u‖ ≤
      complexZetaModelDifferenceConstant
          (Fintype.card κ) /
        (p : ℝ) ^ 2 := by
  classical
  rw [fourierZetaSystemEulerLocalFactor_eq_phase
    (by omega) hp]
  exact norm_phaseZetaSystemEulerLocalFactor_sub_firstOrder_le
    hp hseven _ _
    (fun q =>
      SmoothSieveCutoff.norm_divisorMultiplicativePhase_le_one
        hR hp (t q))
    (fun q =>
      SmoothSieveCutoff.norm_divisorMultiplicativePhase_le_one
        hR hp (u q))

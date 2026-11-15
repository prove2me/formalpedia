-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.norm_phasePairZetaEulerLocalModel_sub_unshifted_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:25:45.899891+00:00
-- url     : https://prove2.me/submissions/02d8fe65-bd18-4625-8835-422074550bb8

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexEulerProductComparison
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
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedEulerCorrection
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedEulerCorrectionLimit
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedLocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ZetaEulerProductIdentification
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
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_one_half_le_norm_phasePairZetaDenominator

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







theorem phasePairZetaDenominator_ne_zero
    {p : ℕ} (hp : p.Prime)
    {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    1 - (p : ℂ)⁻¹ * z * w ≠ 0 := by
  exact norm_pos_iff.mp
    ((by norm_num : (0 : ℝ) < 1 / 2).trans_le
      (one_half_le_norm_phasePairZetaDenominator
        hp hz hw))







/-! ## Exact cpow coordinates -/













/-! ## Finite systems -/



























/-! ## Direct arithmetic/zeta comparison -/























end Wikipedia.SzemeredisTheorem

end

section


/-!
# Quantitative convergence of the W-tricked Euler correction

`WTrickedEulerCorrection` writes the normalized finite small-prime
correction as

`∏_{p ≤ w} ((1 - p⁻¹)^m * Z_p(z, v)⁻¹)`.

This file controls that product when every phase is close to one.  The
important cancellation is

`z + v - z v - 1 = -(1-z)(1-v)`,

so the perturbation is quadratic in the phase error.  We first prove a
one-pair bound valid at every prime, then accumulate it over the finite
form system and over all primes at most `w`.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter
open scoped BigOperators Topology

/-! ## One paired phase -/





/-- Exact quadratic cancellation before dividing by the shifted pair
factor. -/
theorem phasePairZetaEulerLocalModel_sub_unshifted_eq
    {p : ℕ} (hp : p.Prime)
    {z v : ℂ} (hz : ‖z‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    phasePairZetaEulerLocalModel p z v -
        (1 - (p : ℂ)⁻¹) =
      ((p : ℂ)⁻¹ * (1 - z) * (1 - v)) /
        (1 - (p : ℂ)⁻¹ * z * v) := by
  have hd0 :
      1 - (p : ℂ)⁻¹ * z * v ≠ 0 :=
    phasePairZetaDenominator_ne_zero hp hz hv
  rw [phasePairZetaEulerLocalModel]
  apply (eq_div_iff hd0).2
  rw [sub_mul, div_mul_cancel₀ _ hd0]
  ring







/-! ## A finite system at one prime -/







/-! ## Accumulation over the small primes -/









/-! ## The actual cutoff phases -/











/-! ## Linearized control and joint convergence -/







end Wikipedia.SzemeredisTheorem

end
/-!
# Quantitative convergence of the W-tricked Euler correction

`WTrickedEulerCorrection` writes the normalized finite small-prime
correction as

`∏_{p ≤ w} ((1 - p⁻¹)^m * Z_p(z, v)⁻¹)`.

This file controls that product when every phase is close to one.  The
important cancellation is

`z + v - z v - 1 = -(1-z)(1-v)`,

so the perturbation is quadratic in the phase error.  We first prove a
one-pair bound valid at every prime, then accumulate it over the finite
form system and over all primes at most `w`.
-/
open Wikipedia.SzemeredisTheorem
open Filter
open scoped BigOperators Topology
/-! ## One paired phase -/

open Wikipedia.SzemeredisTheorem in
/-- Quadratic difference bound before normalizing by the pair factor. -/
theorem solution
    {p : ℕ} (hp : p.Prime)
    {z v : ℂ} (hz : ‖z‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hzclose : ‖z - 1‖ ≤ δ)
    (hvclose : ‖v - 1‖ ≤ δ) :
    ‖phasePairZetaEulerLocalModel p z v -
        (1 - (p : ℂ)⁻¹)‖ ≤
      2 * δ ^ 2 / (p : ℝ) := by
  have hpR : 0 < (p : ℝ) := by
    exact_mod_cast hp.pos
  have hdhalf :=
    one_half_le_norm_phasePairZetaDenominator hp hz hv
  have hdPos :
      0 < ‖1 - (p : ℂ)⁻¹ * z * v‖ :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le
      hdhalf
  have hzclose' : ‖1 - z‖ ≤ δ := by
    rw [norm_sub_rev]
    exact hzclose
  have hvclose' : ‖1 - v‖ ≤ δ := by
    rw [norm_sub_rev]
    exact hvclose
  rw [phasePairZetaEulerLocalModel_sub_unshifted_eq
    hp hz hv, Complex.norm_div, norm_mul, norm_mul,
    norm_inv, Complex.norm_natCast]
  rw [div_le_iff₀ hdPos]
  have hnum :
      (p : ℝ)⁻¹ * ‖1 - z‖ * ‖1 - v‖ ≤
        (1 / (p : ℝ)) * δ ^ 2 := by
    calc
      (p : ℝ)⁻¹ * ‖1 - z‖ * ‖1 - v‖ ≤
          (p : ℝ)⁻¹ * δ * δ := by
        gcongr
      _ = (1 / (p : ℝ)) * δ ^ 2 := by
        rw [one_div]
        ring
  calc
    (p : ℝ)⁻¹ * ‖1 - z‖ * ‖1 - v‖ ≤
        (1 / (p : ℝ)) * δ ^ 2 :=
      hnum
    _ ≤
        (2 * δ ^ 2 / (p : ℝ)) *
          ‖1 - (p : ℂ)⁻¹ * z * v‖ := by
      calc
        (1 / (p : ℝ)) * δ ^ 2 =
            (2 * δ ^ 2 / (p : ℝ)) *
              ((1 : ℝ) / 2) := by
          field_simp
        _ ≤
            (2 * δ ^ 2 / (p : ℝ)) *
              ‖1 - (p : ℂ)⁻¹ * z * v‖ :=
          mul_le_mul_of_nonneg_left hdhalf
            (div_nonneg
              (mul_nonneg (by norm_num) (sq_nonneg δ))
              hpR.le)

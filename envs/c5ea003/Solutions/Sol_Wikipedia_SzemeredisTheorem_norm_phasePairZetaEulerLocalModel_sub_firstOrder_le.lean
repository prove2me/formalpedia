-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.norm_phasePairZetaEulerLocalModel_sub_firstOrder_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:25:45.795436+00:00
-- url     : https://prove2.me/submissions/b836a7ed-4dad-480f-9d22-64fefc4ea840

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

/-- Exact second-order cancellation between the zeta Euler factor and its
first-order truncation. -/
theorem phasePairZetaEulerLocalModel_sub_firstOrder_eq
    {p : ℕ} {z w : ℂ}
    (hden : 1 - (p : ℂ)⁻¹ * z * w ≠ 0) :
    phasePairZetaEulerLocalModel p z w -
        phasePairFirstOrderLocalModel p z w =
      ((p : ℂ)⁻¹ ^ 2 * z * w *
          (1 - z) * (1 - w)) /
        (1 - (p : ℂ)⁻¹ * z * w) := by
  rw [phasePairZetaEulerLocalModel,
    phasePairFirstOrderLocalModel]
  apply (eq_div_iff hden).2
  rw [sub_mul, div_mul_cancel₀ _ hden]
  ring





/-! ## Exact cpow coordinates -/













/-! ## Finite systems -/



























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

open Wikipedia.SzemeredisTheorem in
/-- Uniform one-pair difference estimate. -/
theorem solution
    {p : ℕ} (hp : p.Prime)
    {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖phasePairZetaEulerLocalModel p z w -
        phasePairFirstOrderLocalModel p z w‖ ≤
      (8 : ℝ) / (p : ℝ) ^ 2 := by
  have hpR : 0 < (p : ℝ) := by
    exact_mod_cast hp.pos
  have hdenHalf :=
    one_half_le_norm_phasePairZetaDenominator hp hz hw
  have hdenPos :
      0 < ‖1 - (p : ℂ)⁻¹ * z * w‖ :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le
      hdenHalf
  have hzsub : ‖1 - z‖ ≤ 2 := by
    calc
      ‖1 - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ :=
        norm_sub_le _ _
      _ ≤ 2 := by
        rw [norm_one]
        linarith
  have hwsub : ‖1 - w‖ ≤ 2 := by
    calc
      ‖1 - w‖ ≤ ‖(1 : ℂ)‖ + ‖w‖ :=
        norm_sub_le _ _
      _ ≤ 2 := by
        rw [norm_one]
        linarith
  have hnum :
      ‖(p : ℂ)⁻¹ ^ 2 * z * w *
          (1 - z) * (1 - w)‖ ≤
        (4 : ℝ) / (p : ℝ) ^ 2 := by
    rw [norm_mul, norm_mul, norm_mul, norm_mul,
      norm_pow, norm_inv, Complex.norm_natCast]
    have hinv0 : 0 ≤ ((p : ℝ)⁻¹) ^ 2 := by
      positivity
    calc
      ((p : ℝ)⁻¹) ^ 2 * ‖z‖ * ‖w‖ *
          ‖1 - z‖ * ‖1 - w‖ ≤
          ((p : ℝ)⁻¹) ^ 2 * 1 * 1 * 2 * 2 := by
        gcongr
      _ = (4 : ℝ) / (p : ℝ) ^ 2 := by
        field_simp
        ring
  rw [phasePairZetaEulerLocalModel_sub_firstOrder_eq
    (phasePairZetaDenominator_ne_zero hp hz hw),
    Complex.norm_div]
  calc
    ‖(p : ℂ)⁻¹ ^ 2 * z * w *
          (1 - z) * (1 - w)‖ /
          ‖1 - (p : ℂ)⁻¹ * z * w‖ ≤
        2 *
          ‖(p : ℂ)⁻¹ ^ 2 * z * w *
            (1 - z) * (1 - w)‖ := by
      rw [div_le_iff₀ hdenPos]
      have hnonneg :
          0 ≤
            ‖(p : ℂ)⁻¹ ^ 2 * z * w *
              (1 - z) * (1 - w)‖ :=
        norm_nonneg _
      nlinarith
    _ ≤ 2 * ((4 : ℝ) / (p : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hnum (by norm_num)
    _ = (8 : ℝ) / (p : ℝ) ^ 2 := by
      ring

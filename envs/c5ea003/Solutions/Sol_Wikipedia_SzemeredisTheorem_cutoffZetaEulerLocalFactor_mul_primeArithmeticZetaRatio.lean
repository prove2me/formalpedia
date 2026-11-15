-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.cutoffZetaEulerLocalFactor_mul_primeArithmeticZetaRatio
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:31:12.131204+00:00
-- url     : https://prove2.me/submissions/98fe3aa2-ead7-41b5-b9a0-8f834fcf3521

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
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_norm_divisorMultiplicativePhase_le_one
import Theorems.Thm_Wikipedia_SzemeredisTheorem_divisorMultiplicativePhase_eq_cpow
import Theorems.Thm_Wikipedia_SzemeredisTheorem_one_half_le_norm_phasePairZetaDenominator
import Theorems.Thm_Wikipedia_SzemeredisTheorem_phaseZetaNumerator_ne_zero

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



























/-! ## Direct arithmetic/zeta comparison -/























end Wikipedia.SzemeredisTheorem

end

section



/-!
# The complex arithmetic Euler product as zeta model times correction

`ComplexZetaModelComparison` proves, at every sufficiently large prime, that
the exact affine-system local factor divided by its zeta Euler model is
`1 + O_m(p⁻²)`.  This file promotes that local estimate to an unordered
Euler product.

There are three small points which are made explicit here.

* The exceptional cutoff contains both the finite affine-rank exceptional
  set and the quantitative nonvanishing range for the zeta model.
* The zeta model is in fact nonzero at every prime.  Consequently the
  arithmetic/zeta ratio is defined by honest cancellation at all primes.
* Replacing the finitely many uncontrolled ratios by one gives a globally
  square-decaying family.  The cutoff also makes every remaining ratio
  lie in the radius-`1/2` ball around one, so the masked family is
  pointwise nonzero.  Mathlib's finite-change theorem for products in a
  commutative group-with-zero then restores the exceptional factors.

Combining the resulting correction product with
`cutoffZetaEulerLocalFactor_hasProd` identifies the exact arithmetic prime
product as

`(elementary singular factor) * (completed zeta factor) *
  (convergent arithmetic correction)`.

No nonvanishing assertion is made for the correction without an explicit
nonvanishing hypothesis on the arithmetic local factors: a complex finite
average can in principle vanish.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter
open scoped BigOperators

/-! ## Prime-indexed local factors and the common cutoff -/













/-- The zeta Euler factor from `ZetaEulerProductIdentification` is exactly
the finite-system zeta factor used in the local comparison file. -/
theorem cutoffZetaEulerLocalFactor_eq_fourierZetaSystemEulerLocalFactor
    {κ : Type*} [Fintype κ]
    (R : ℕ) (t u : κ → ℝ) (p : Nat.Primes) :
    cutoffZetaEulerLocalFactor R t u p =
      fourierZetaSystemEulerLocalFactor R (p : ℕ) t u := by
  classical
  simp only [cutoffZetaEulerLocalFactor,
    zetaSystemEulerLocalFactor,
    zetaPairEulerLocalFactor,
    fourierZetaSystemEulerLocalFactor,
    fourierPairZetaEulerLocalFactor,
    pairedZetaEulerLocalFactor,
    div_eq_mul_inv]

/-! ## Pointwise nonvanishing of the zeta model -/



/-- A one-pair phase-coordinate zeta Euler factor is nonzero. -/
theorem phasePairZetaEulerLocalModel_ne_zero
    {p : ℕ} (hp : p.Prime)
    {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    phasePairZetaEulerLocalModel p z w ≠ 0 := by
  rw [phasePairZetaEulerLocalModel]
  exact div_ne_zero
    (mul_ne_zero
      (phaseZetaNumerator_ne_zero hp hz)
      (phaseZetaNumerator_ne_zero hp hw))
    (phasePairZetaDenominator_ne_zero hp hz hw)

/-- Every one-pair zeta factor at the exact Fourier shifts is nonzero. -/
theorem fourierPairZetaEulerLocalFactor_ne_zero
    {R : ℕ} (hR : 2 ≤ R)
    (p : Nat.Primes) (t u : ℝ) :
    fourierPairZetaEulerLocalFactor R (p : ℕ) t u ≠ 0 := by
  rw [fourierPairZetaEulerLocalFactor_eq_phase
    (by omega) p.prop]
  exact phasePairZetaEulerLocalModel_ne_zero
    p.prop
    (SmoothSieveCutoff.norm_divisorMultiplicativePhase_le_one
      hR p.prop t)
    (SmoothSieveCutoff.norm_divisorMultiplicativePhase_le_one
      hR p.prop u)

/-- The finite-system zeta model is nonzero at every prime. -/
theorem fourierZetaSystemEulerLocalFactor_ne_zero
    {κ : Type*} [Fintype κ]
    {R : ℕ} (hR : 2 ≤ R)
    (p : Nat.Primes) (t u : κ → ℝ) :
    fourierZetaSystemEulerLocalFactor
      R (p : ℕ) t u ≠ 0 := by
  classical
  rw [fourierZetaSystemEulerLocalFactor]
  apply Finset.prod_ne_zero_iff.mpr
  intro q _hq
  exact fourierPairZetaEulerLocalFactor_ne_zero
    hR p (t q) (u q)



/-! ## Square decay and the convergent correction product -/





















/-! ## Exact global Euler-product identification -/









end Wikipedia.SzemeredisTheorem

end
/-!
# The complex arithmetic Euler product as zeta model times correction

`ComplexZetaModelComparison` proves, at every sufficiently large prime, that
the exact affine-system local factor divided by its zeta Euler model is
`1 + O_m(p⁻²)`.  This file promotes that local estimate to an unordered
Euler product.

There are three small points which are made explicit here.

* The exceptional cutoff contains both the finite affine-rank exceptional
  set and the quantitative nonvanishing range for the zeta model.
* The zeta model is in fact nonzero at every prime.  Consequently the
  arithmetic/zeta ratio is defined by honest cancellation at all primes.
* Replacing the finitely many uncontrolled ratios by one gives a globally
  square-decaying family.  The cutoff also makes every remaining ratio
  lie in the radius-`1/2` ball around one, so the masked family is
  pointwise nonzero.  Mathlib's finite-change theorem for products in a
  commutative group-with-zero then restores the exceptional factors.

Combining the resulting correction product with
`cutoffZetaEulerLocalFactor_hasProd` identifies the exact arithmetic prime
product as

`(elementary singular factor) * (completed zeta factor) *
  (convergent arithmetic correction)`.

No nonvanishing assertion is made for the correction without an explicit
nonvanishing hypothesis on the arithmetic local factors: a complex finite
average can in principle vanish.
-/
open Wikipedia.SzemeredisTheorem
open Filter
open scoped BigOperators
/-! ## Prime-indexed local factors and the common cutoff -/
/-! ## Pointwise nonvanishing of the zeta model -/
/-! ## Square decay and the convergent correction product -/
/-! ## Exact global Euler-product identification -/

open Wikipedia.SzemeredisTheorem in
/-- At every prime, the zeta factor times the arithmetic/zeta ratio is
the exact arithmetic local factor. -/
theorem solution
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {R : ℕ} (hR : 2 ≤ R)
    (forms : κ → AffineForm ι ℤ)
    (t u : κ → ℝ) (p : Nat.Primes) :
    cutoffZetaEulerLocalFactor R t u p *
        primePairedFourierArithmeticToZetaLocalRatio
          R forms t u p =
      pairedFourierPrimeLocalFactor
        R forms t u p := by
  let : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
  have hzeta :
      fourierZetaSystemEulerLocalFactor
          R (p : ℕ) t u ≠ 0 :=
    fourierZetaSystemEulerLocalFactor_ne_zero
      hR p t u
  rw [cutoffZetaEulerLocalFactor_eq_fourierZetaSystemEulerLocalFactor,
    primePairedFourierArithmeticToZetaLocalRatio,
    pairedFourierPrimeLocalFactor,
    pairedFourierArithmeticToZetaLocalRatio,
    mul_comm,
    div_mul_cancel₀ _ hzeta]

-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.norm_normalizedSmallPrimeZetaCorrection_sub_one_le_exp_sum
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:41:56.388086+00:00
-- url     : https://prove2.me/submissions/45adb04a-dc7b-49a4-a05b-f15dc88dcf74

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_norm_divisorMultiplicativePhase_le_one
import Theorems.Thm_Wikipedia_SzemeredisTheorem_divisorMultiplicativePhase_eq_cpow
import Theorems.Thm_Wikipedia_SzemeredisTheorem_norm_phaseSystemNormalizationResidual_sub_one_le
import Theorems.Thm_Wikipedia_SzemeredisTheorem_primorialReducedResidueDensity_eq_prod

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











/-! ## Square decay and the convergent correction product -/





















/-! ## Exact global Euler-product identification -/









end Wikipedia.SzemeredisTheorem

end

section




/-!
# The finite Euler correction at W-tricked primes

For `W = primorial w`, every arithmetic local factor at a prime `p ≤ w`
is one.  Relative to the universal zeta Euler model, its arithmetic/zeta
ratio is therefore the inverse zeta factor.  This file packages the exact
finite product of those inverses and compares it with the Selberg
normalization `(φ(W) / W)^m`.

The comparison is exact: the normalized correction is a finite product of
the ratios between the unshifted local model `(1 - p⁻¹)^m` and the shifted
Fourier-zeta local model.  Thus the only remaining small-prime asymptotic is
to show that these finitely many shifted model factors approach their
unshifted values in the chosen joint `w, R` regime.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators



















/-! ## The parallel first-order correction -/









/-! ## Exact comparison with the totient normalization -/







/-- The `m`th power of the primorial reduced-residue density is exactly the
product of the unshifted system local factors. -/
theorem primorialReducedResidueDensity_pow_eq_prod
    (w m : ℕ) :
    primorialReducedResidueDensity w ^ m =
      ∏ p ∈ smallPrimeFinset w,
        unshiftedZetaSystemLocalFactor m p := by
  rw [primorialReducedResidueDensity_eq_prod]
  exact
    (Finset.prod_pow (smallPrimeFinset w) m
      (fun p : Nat.Primes =>
        1 - (p : ℂ)⁻¹)).symm







/-! ## The unshifted phase model -/









/-- At the actual cutoff shifts, the universal zeta factor is the phase
system evaluated at the divisor multiplicative phases. -/
theorem cutoffZetaEulerLocalFactor_eq_phaseSystem
    {κ : Type*} [Fintype κ]
    {R : ℕ} (hR : 2 ≤ R)
    (t u : κ → ℝ) (p : Nat.Primes) :
    cutoffZetaEulerLocalFactor R t u p =
      phaseZetaSystemEulerLocalFactor (p : ℕ)
        (fun q =>
          SmoothSieveCutoff.divisorMultiplicativePhase
            R (p : ℕ) (t q))
        (fun q =>
          SmoothSieveCutoff.divisorMultiplicativePhase
            R (p : ℕ) (u q)) := by
  rw [cutoffZetaEulerLocalFactor_eq_fourierZetaSystemEulerLocalFactor]
  exact fourierZetaSystemEulerLocalFactor_eq_phase
    (by omega) p.prop t u



/-- Exact residual identity: the normalized small-prime correction is a
finite product of unshifted model factors divided by the exact shifted
zeta factors. -/
theorem normalizedSmallPrimeZetaCorrection_eq_prod_residual
    {κ : Type*} [Fintype κ]
    (R w : ℕ) (t u : κ → ℝ) :
    normalizedSmallPrimeZetaCorrection R w t u =
      ∏ p ∈ smallPrimeFinset w,
        (unshiftedZetaSystemLocalFactor
            (Fintype.card κ) p *
          (cutoffZetaEulerLocalFactor R t u p)⁻¹) := by
  rw [normalizedSmallPrimeZetaCorrection,
    primorialReducedResidueDensity_pow_eq_prod,
    smallPrimeZetaCorrection,
    ← Finset.prod_mul_distrib]

/-- Phase-coordinate form of the exact residual.  Together with
`prod_unshifted_mul_inv_phaseUnit_eq_one`, this isolates the remaining
asymptotic as convergence of the displayed cutoff phases to one. -/
theorem normalizedSmallPrimeZetaCorrection_eq_phaseResidual
    {κ : Type*} [Fintype κ]
    {R : ℕ} (hR : 2 ≤ R)
    (w : ℕ) (t u : κ → ℝ) :
    normalizedSmallPrimeZetaCorrection R w t u =
      ∏ p ∈ smallPrimeFinset w,
        (unshiftedZetaSystemLocalFactor
            (Fintype.card κ) p *
          (phaseZetaSystemEulerLocalFactor (p : ℕ)
            (fun q =>
              SmoothSieveCutoff.divisorMultiplicativePhase
                R (p : ℕ) (t q))
            (fun q =>
              SmoothSieveCutoff.divisorMultiplicativePhase
                R (p : ℕ) (u q)))⁻¹) := by
  rw [normalizedSmallPrimeZetaCorrection_eq_prod_residual]
  apply Finset.prod_congr rfl
  intro p _hp
  rw [cutoffZetaEulerLocalFactor_eq_phaseSystem hR]



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













/-! ## A finite system at one prime -/







/-! ## Accumulation over the small primes -/



/-- The normalized correction is the product of the one-prime normalized
phase-system residuals. -/
theorem normalizedSmallPrimeZetaCorrection_eq_prod_phaseSystemResidual
    {κ : Type*} [Fintype κ]
    {R : ℕ} (hR : 2 ≤ R)
    (w : ℕ) (t u : κ → ℝ) :
    normalizedSmallPrimeZetaCorrection R w t u =
      ∏ p ∈ smallPrimeFinset w,
        phaseSystemNormalizationResidual (p : ℕ)
          (fun q =>
            SmoothSieveCutoff.divisorMultiplicativePhase
              R (p : ℕ) (t q))
          (fun q =>
            SmoothSieveCutoff.divisorMultiplicativePhase
              R (p : ℕ) (u q)) := by
  rw [normalizedSmallPrimeZetaCorrection_eq_phaseResidual
    hR]
  apply Finset.prod_congr rfl
  intro p _hp
  rfl





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
/-! ## A finite system at one prime -/
/-! ## Accumulation over the small primes -/

open Wikipedia.SzemeredisTheorem in
/-- Fully explicit finite-product estimate.  It retains the saving from
each individual prime instead of replacing `p` by the worst case `2`. -/
theorem solution
    {κ : Type*} [Fintype κ]
    {R : ℕ} (hR : 2 ≤ R)
    (w : ℕ) (t u : κ → ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (htclose :
      ∀ p ∈ smallPrimeFinset w, ∀ q,
        ‖SmoothSieveCutoff.divisorMultiplicativePhase
            R (p : ℕ) (t q) - 1‖ ≤ δ)
    (huclose :
      ∀ p ∈ smallPrimeFinset w, ∀ q,
        ‖SmoothSieveCutoff.divisorMultiplicativePhase
            R (p : ℕ) (u q) - 1‖ ≤ δ) :
    ‖normalizedSmallPrimeZetaCorrection R w t u - 1‖ ≤
      Real.exp
          (∑ p ∈ smallPrimeFinset w,
            (Real.exp
                ((Fintype.card κ : ℝ) *
                  (12 * δ ^ 2 / (p : ℝ))) -
              1)) -
        1 := by
  rw [normalizedSmallPrimeZetaCorrection_eq_prod_phaseSystemResidual
    hR]
  let localResidual : Nat.Primes → ℂ :=
    fun p =>
      phaseSystemNormalizationResidual (p : ℕ)
        (fun q =>
          SmoothSieveCutoff.divisorMultiplicativePhase
            R (p : ℕ) (t q))
        (fun q =>
          SmoothSieveCutoff.divisorMultiplicativePhase
            R (p : ℕ) (u q))
  have hbase :=
    (smallPrimeFinset w).norm_prod_one_add_sub_one_le
      (fun p => localResidual p - 1)
  have heq :
      (fun p : Nat.Primes =>
        1 + (localResidual p - 1)) =
        localResidual := by
    funext p
    ring
  rw [heq] at hbase
  have hsum :
      (∑ p ∈ smallPrimeFinset w,
          ‖localResidual p - 1‖) ≤
        ∑ p ∈ smallPrimeFinset w,
          (Real.exp
              ((Fintype.card κ : ℝ) *
                (12 * δ ^ 2 / (p : ℝ))) -
            1) := by
    apply Finset.sum_le_sum
    intro p hp
    exact
      norm_phaseSystemNormalizationResidual_sub_one_le
        p.prop
        (fun q =>
          SmoothSieveCutoff.divisorMultiplicativePhase
            R (p : ℕ) (t q))
        (fun q =>
          SmoothSieveCutoff.divisorMultiplicativePhase
            R (p : ℕ) (u q))
        (fun q =>
          SmoothSieveCutoff.norm_divisorMultiplicativePhase_le_one
            hR p.prop (t q))
        (fun q =>
          SmoothSieveCutoff.norm_divisorMultiplicativePhase_le_one
            hR p.prop (u q))
        hδ (htclose p hp) (huclose p hp)
  exact hbase.trans
    (sub_le_sub_right
      (Real.exp_le_exp.mpr hsum) 1)

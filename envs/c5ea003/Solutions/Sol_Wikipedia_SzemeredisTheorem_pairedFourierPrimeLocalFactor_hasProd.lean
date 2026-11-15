-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.pairedFourierPrimeLocalFactor_hasProd
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T12:04:25.002005+00:00
-- url     : https://prove2.me/submissions/69c4b37e-c3e3-4d5d-b5b0-14fa1f53418a

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_cutoffZetaEulerLocalFactor_mul_primeArithmeticZetaRatio
import Theorems.Thm_Wikipedia_SzemeredisTheorem_cutoffZetaSingularFactor_mul_systemFactor
import Theorems.Thm_Wikipedia_SzemeredisTheorem_multipliable_primePairedFourierArithmeticToZetaLocalRatio
import Theorems.Thm_Wikipedia_SzemeredisTheorem_zetaPairEulerLocalFactor_hasProd

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section





/-!
# Fourier parameters for the zeta comparison

`SmoothCutoffFourier` fixes Mathlib's analyst normalization.  Its divisor
phase is

`exp (-x + 2 π i t x)`, where `x = log d / log R`.

Thus the exact complex shift occurring in the Euler and zeta factors is

`(1 - 2 π i t) / log R`.

This file records that conversion, its positivity and elementary norm
bounds, and the resulting access to the completed zeta estimates.  Keeping
this bridge explicit prevents a hidden `2π` or sign error when the
multivariate Fourier integral is assembled.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter
open scoped BigOperators Topology



theorem cutoffZetaShift_re
    (R : ℕ) (t : ℝ) :
    (cutoffZetaShift R t).re =
      1 / Real.log R := by
  change
    (Complex.ofReal ((Real.log (R : ℝ))⁻¹) *
      ((1 : ℂ) -
        Complex.ofReal (2 * Real.pi * t) *
          Complex.I)).re =
      1 / Real.log R
  simp only [Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.sub_re, Complex.one_re,
    Complex.I_re, Complex.I_im, zero_mul, mul_zero,
    sub_zero]
  rw [one_div]
  simp

theorem cutoffZetaShift_re_pos
    {R : ℕ} (hR : 1 < R) (t : ℝ) :
    0 < (cutoffZetaShift R t).re := by
  rw [cutoffZetaShift_re R]
  exact one_div_pos.mpr
    (Real.log_pos (by exact_mod_cast hR))















/-! ## Finite Fourier systems -/









/-! ## The standard growing truncation box -/







end Wikipedia.SzemeredisTheorem

end

section



/-!
# Identifying the zeta-model Euler product

The model local factor attached to one pair of Fourier shifts `u,v` is

`(1 - p^(-1-u)) (1 - p^(-1-v)) / (1 - p^(-1-u-v))`.

Mathlib's Euler product for `riemannZeta` identifies its prime product with

`ζ(1+u+v) / (ζ(1+u) ζ(1+v))`

whenever the real parts of `u` and `v` are positive.  This file proves that
identity first for one pair and then for an arbitrary finite system.  It
then specializes to the exact Mathlib Fourier shifts and splits the answer
into the elementary singular factor and the removable completed factor from
`ZetaNearOne`.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators









/-- The prime product and finite pair product commute. -/
theorem zetaSystemEulerLocalFactor_hasProd
    {κ : Type*} [Fintype κ]
    {u v : κ → ℂ}
    (hu : ∀ i, 0 < (u i).re)
    (hv : ∀ i, 0 < (v i).re) :
    HasProd
      (zetaSystemEulerLocalFactor u v)
      (∏ i,
        riemannZeta (1 + u i + v i) /
          (riemannZeta (1 + u i) *
            riemannZeta (1 + v i))) := by
  classical
  change HasProd
    (fun p : Nat.Primes =>
      ∏ i, zetaPairEulerLocalFactor (u i) (v i) p) _
  simpa only using
    (hasProd_prod
      (s := (Finset.univ : Finset κ))
      (fun i _ =>
        zetaPairEulerLocalFactor_hasProd
          (hu i) (hv i)))







/-- Full Euler-product identification at the exact Fourier parameters. -/
theorem cutoffZetaEulerLocalFactor_hasProd
    {κ : Type*} [Fintype κ]
    {R : ℕ} (hR : 1 < R)
    (t u : κ → ℝ) :
    HasProd
      (cutoffZetaEulerLocalFactor R t u)
      (cutoffZetaSingularFactor R t u *
        cutoffZetaSystemFactor R t u) := by
  have h :=
    zetaSystemEulerLocalFactor_hasProd
      (u := fun i => cutoffZetaShift R (t i))
      (v := fun i => cutoffZetaShift R (u i))
      (fun i => cutoffZetaShift_re_pos hR (t i))
      (fun i => cutoffZetaShift_re_pos hR (u i))
  rw [cutoffZetaSingularFactor_mul_systemFactor
    hR t u]
  exact h

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















/-! ## Pointwise nonvanishing of the zeta model -/











/-! ## Square decay and the convergent correction product -/



















/-- Canonical `HasProd` statement for the convergent arithmetic
correction. -/
theorem primePairedFourierArithmeticToZetaLocalRatio_hasProd
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : NonzeroCoefficientVectors forms)
    (hindependent : PairwiseIndependentCoefficients forms)
    {R : ℕ} (hR : 2 ≤ R)
    (t u : κ → ℝ) :
    HasProd
      (primePairedFourierArithmeticToZetaLocalRatio
        R forms t u)
      (∏' p : Nat.Primes,
        primePairedFourierArithmeticToZetaLocalRatio
          R forms t u p) :=
  (multipliable_primePairedFourierArithmeticToZetaLocalRatio
    hnonzero hindependent hR t u).hasProd

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
/-- The exact affine-system local factors have an unordered Euler product,
identified as the finite zeta quotient times the convergent arithmetic
correction. -/
theorem solution
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : NonzeroCoefficientVectors forms)
    (hindependent : PairwiseIndependentCoefficients forms)
    {R : ℕ} (hR : 2 ≤ R)
    (t u : κ → ℝ) :
    HasProd
      (pairedFourierPrimeLocalFactor
        R forms t u)
      ((cutoffZetaSingularFactor R t u *
          cutoffZetaSystemFactor R t u) *
        ∏' p : Nat.Primes,
          primePairedFourierArithmeticToZetaLocalRatio
            R forms t u p) := by
  have hzeta :=
    cutoffZetaEulerLocalFactor_hasProd
      (show 1 < R by omega) t u
  have hratio :=
    primePairedFourierArithmeticToZetaLocalRatio_hasProd
      hnonzero hindependent hR t u
  refine (hzeta.mul hratio).congr_fun ?_
  intro p
  exact
    (cutoffZetaEulerLocalFactor_mul_primeArithmeticZetaRatio
      hR forms t u p).symm

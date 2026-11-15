-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryAverageInterior
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryAverageInterior
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:26:58.823015+00:00
-- url     : https://prove2.me/theorems/3a454a6d-1484-4e55-9d4e-3be30852ee1f
-- title:
--   Common Fourier correction and averaging over canonical carry vectors
-- statement:
--   At fixed sieve and primorial parameters and fixed paired Fourier frequencies, the common finite correction is the product of the normalized small-prime correction and the completed zeta-system factor.
--
--   The bundle packages a selected CFZ family together with any integer carry vector, positive cyclic modulus, residue shift, and Fourier frequencies into the canonical Fourier-data structure. It then averages the large-prime Euler corrections over the finite uniform range of carry vectors, weighting each by the normalized density of its canonical carry cell. The common finite factor is independent of the carry vector; the large-prime correction is allowed to vary between cells.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/CFZCanonicalCarryAverageInterior.lean#L29-L68

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCompleteMainTermBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryFourierNormalization
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Normed.Ring.InfiniteProd
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
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
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Field

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Interior comparison for the canonical carry average

The complete canonical Euler integrand is a probability-weighted average
over the canonical carry vectors.  Exact normalization of each arbitrary
carry vector separates its contribution into three factors:

* the normalized archimedean baseline;
* a finite correction common to every carry vector;
* the carry-dependent large-prime Euler correction.

This file factors the complete scaled integrand accordingly.  Since the
canonical carry densities are nonnegative and sum to one, a uniform bound
for every arbitrary-carry large-prime correction passes directly to their
weighted average.  No realizability split is needed for zero-density carry
vectors.
-/

namespace Wikipedia.SzemeredisTheorem

open MeasureTheory
open scoped BigOperators

/-! ## The common correction and the carry-weighted large-prime average -/

/-- The normalized finite correction shared by every canonical carry
vector at fixed Fourier frequencies. -/
noncomputable def selectedCFZCanonicalCommonFiniteCorrection
    {κ : Type*} [Fintype κ]
    (R w : ℕ) (t u : κ → ℝ) : ℂ :=
  normalizedSmallPrimeZetaCorrection R w t u *
    cutoffZetaSystemFactor R t u

/-- Package an arbitrary canonical carry vector at the displayed
parameters. -/
def selectedCFZCanonicalCarryFourierDataAt
    {k N : ℕ} [NeZero N]
    (w b R : ℕ) (e : LinearFormsExponent k)
    (carry : SelectedCFZFormIndex e → ℤ)
    (t u : SelectedCFZFormIndex e → ℝ) :
    SelectedCFZCanonicalCarryFourierData k where
  N := N
  N_neZero := inferInstance
  R := R
  w := w
  b := b
  e := e
  carry := carry
  t := t
  u := u

/-- Probability-weighted average of the arbitrary-carry large-prime
corrections. -/
noncomputable def selectedCFZCanonicalCarryLargePrimeCorrectionAverage
    {k N : ℕ} [NeZero N]
    (w b R : ℕ) (e : LinearFormsExponent k)
    (t u : SelectedCFZFormIndex e → ℝ) : ℂ :=
  ∑ carry ∈ cfzCanonicalCarryVectorChoices
      (SelectedCFZFormIndex e) k,
    (cfzCanonicalCarryCellDensity
        (N := N)
        (fun q : SelectedCFZFormIndex e => q.1)
        carry : ℂ) *
      (selectedCFZCanonicalCarryFourierDataAt
        (N := N) w b R e carry t u).largePrimeEulerCorrection

/-! ## Exact factorization -/





/-! ## Probability-average and product estimates -/









/-! ## The baseline-relative interior comparison -/



end Wikipedia.SzemeredisTheorem



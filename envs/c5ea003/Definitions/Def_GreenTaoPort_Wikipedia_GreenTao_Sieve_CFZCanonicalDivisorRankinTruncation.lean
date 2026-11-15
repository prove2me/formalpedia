-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalDivisorRankinTruncation
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalDivisorRankinTruncation
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:18:50.223526+00:00
-- url     : https://prove2.me/theorems/2db4855c-e8ea-4e94-b7e4-8df24a490ad5
-- title:
--   Rankin masses for coordinatewise divisor truncation
-- statement:
--   For a support assignment, the actual coefficient mass multiplies the norms of its paired prime Fourier coefficients. Its frequency-independent Rankin majorant replaces each supported prime incidence by $3p^{-a}$, where $a=1/\log R$ in the intended range $R>1$.
--
--   A paired divisor family's Rankin weight is $\prod_q d_q^{-a}e_q^{-a}$. Summing this weight over an exact coordinatewise-truncated support fiber gives its truncated mass. The full fixed-family mass sums the truncated and primewise majorant pieces against the norm of the support-density product.
--
--   The canonical carry mass averages these fixed-family masses using absolute carry-cell densities. All formulas are total real-valued definitions; positivity and sieve-level restrictions are supplied when they are used to bound the Fourier truncation discrepancy.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/CFZCanonicalDivisorRankinTruncation.lean#L108-L446

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalDivisorTruncation
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierTailPolylog
import Lean
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
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
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
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Field

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Rankin bounds for canonical coordinatewise divisor truncation

The pointwise cardinality majorant for the canonical divisor-cutoff
discrepancy is much too large.  This file retains the actual norms of all
divisor phases and paired Fourier prime coefficients.

There is an important scale distinction.  The norm of a divisor phase is

`d ^ (-1 / log R)`.

Consequently a Rankin exponent compatible with prime summability is itself
of order `1 / log R`; its threshold gain is only a fixed exponential
constant.  Thus absolute values do not imply raw pointwise decay, even on a
growing Fourier box (the phase norm is frequency-independent).  The usable
result is instead a sharp arithmetic mass multiplying the common Schwartz
density.  Arbitrarily high Fourier moments then control the complementary
integral.  Cancellation of the full integral, coming from Fourier inversion
and compact support of the cutoff, is the separate interior step.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter MeasureTheory Set
open scoped ArithmeticFunction.Moebius BigOperators Topology

/-! ## Exact phase scale and the critical Rankin obstruction -/









/-! ## Actual coefficient and phase masses -/

/-- The product of the actual paired-prime coefficient norms in one
support fiber. -/
noncomputable def fixedFamilyPrimeSupportActualCoefficientMass
    {κ : Type*} [Fintype κ]
    (R : ℕ) (t u : κ → ℝ)
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P) : ℝ :=
  ∏ p : {p // p ∈ P},
    ∏ q ∈ support p,
      ‖pairedFourierPrimeCoefficient
        R (p : ℕ) (t q) (u q)‖



/-- Frequency-independent Rankin majorant for the actual support
coefficient. -/
noncomputable def fixedFamilyPrimeSupportRpowCoefficientMass
    {κ : Type*} [Fintype κ]
    (R : ℕ)
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P) : ℝ :=
  ∏ p : {p // p ∈ P},
    (3 * (p : ℝ) ^ (-(Real.log (R : ℝ))⁻¹)) ^
      (support p).card



/-- Exact phase norm of one squarefree paired divisor family, with the
common cutoff Fourier density removed. -/
noncomputable def pairedDivisorRankinWeight
    {κ : Type*} [Fintype κ]
    (R : ℕ) (z : κ → ℕ × ℕ) : ℝ :=
  ∏ q,
    ((z q).1 : ℝ) ^ (-(Real.log (R : ℝ))⁻¹) *
      ((z q).2 : ℝ) ^ (-(Real.log (R : ℝ))⁻¹)

/-- Sum of the exact divisor-phase norms in one coordinatewise support
fiber. -/
noncomputable def coordinatewiseTruncatedSupportRankinMass
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (R : ℕ) (P : Finset Nat.Primes)
    (support : FixedFamilyPrimeSupportAssignment κ P) : ℝ :=
  ∑ z ∈ coordinatewiseTruncatedSupportFiber R P support,
    pairedDivisorRankinWeight R z







/-- Arithmetic Rankin mass of the complete fixed-family discrepancy.  The
actual phase decay is retained in both its truncated and unrestricted
pieces. -/
noncomputable def fixedFamilyCoordinatewiseTruncationRankinMass
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (R : ℕ) (forms : κ → AffineForm ι ℤ)
    (P : Finset Nat.Primes) : ℝ :=
  ∑ support ∈ fixedFamilyPrimeSupportAssignmentChoices κ P,
    (coordinatewiseTruncatedSupportRankinMass R P support +
      fixedFamilyPrimeSupportRpowCoefficientMass R support) *
      ‖fixedFamilyPrimeSupportDensity forms support‖





/-! ## Canonical carry Rankin mass -/

/-- The sharp arithmetic Rankin mass after summing the canonical carry
cells. -/
noncomputable def cfzCanonicalCarryTruncationRankinMass
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (W b R : ℕ) (forms : κ → CFZFormIndex k) : ℝ :=
  ∑ carry ∈ cfzCanonicalCarryVectorChoices κ k,
    |cfzCanonicalCarryCellDensity
        (N := N) forms carry| *
      fixedFamilyCoordinatewiseTruncationRankinMass
        R
        (cfzCarryAdjustedFamilyAtVector N W b forms carry)
        (primesLEAsPrimes R)









/-! ## Growing-box complementary integral -/





/-! ## Selberg-scaled complementary discrepancy -/

namespace SmoothSieveCutoff





















end SmoothSieveCutoff

end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.cfzCanonicalCarryTruncationRankinMass.congr_simp,
    `Wikipedia.SzemeredisTheorem.coordinatewiseTruncatedSupportRankinMass.congr_simp,
    `Wikipedia.SzemeredisTheorem.fixedFamilyCoordinatewiseTruncationRankinMass.congr_simp
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"



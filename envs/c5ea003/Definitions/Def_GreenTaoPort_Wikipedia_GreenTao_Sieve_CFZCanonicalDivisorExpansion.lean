-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalDivisorExpansion
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalDivisorExpansion
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:15:40.033219+00:00
-- url     : https://prove2.me/theorems/da538a3c-e855-4940-be83-85afc685ea15
-- title:
--   Prime-support assignments and exact coordinatewise truncation discrepancies
-- statement:
--   For a finite prime set $P$ and a finite form index type, a support assignment chooses a subset of form indices at every prime. A paired-divisor family induces such an assignment through the primes dividing its paired local LCMs.
--
--   Each assignment has a product of affine common-zero densities and a signed Fourier coefficient, with local sign $(-1)^{|S_p|}$ and one paired prime coefficient per supported form. Their products give the finite prime-support Euler terms. The cutoff Fourier envelope is common to every divisor term.
--
--   The coordinatewise-truncated coefficient sums the actual transformed squarefree divisor families in a support fiber. Subtracting the envelope times the unrestricted primewise coefficient defines its discrepancy. The bundle supplies the fixed-family divisor Euler product, its canonical carry specializations, and the carry-density-weighted sums of both the finite prime-support expansion and its truncation discrepancy. A total natural-modulus density wrapper equals one away from primes solely for index bookkeeping.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/CFZCanonicalDivisorExpansion.lean#L26-L748

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryEulerBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_UnrestrictedPrimeSupportEulerSeries
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryHarmonicLcmEulerBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PrimeHarmonicProductBound
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
# Canonical fixed-carry divisor expansions

On a canonical CFZ carry cell the affine family is fixed before the
divisor variables are chosen.  This file reorganizes the coordinatewise
truncated, squarefree paired-divisor sum by its prime-to-form supports.

The reorganization is exact.  The corresponding unrestricted support
sum factors into the existing paired Fourier local factors, and hence into
the finite-prime-support Euler series.  The difference between these two
finite sums is recorded explicitly; it is precisely the remaining
coordinatewise-truncation splice, with no divisor-dependent affine family.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped ArithmeticFunction.Moebius BigOperators

/-! ## Generic finite prime-support assignments -/

/-- A form-support chosen independently at every prime in `P`. -/
abbrev FixedFamilyPrimeSupportAssignment
    (κ : Type*) [Fintype κ] (P : Finset Nat.Primes) :=
  (p : {p // p ∈ P}) → Finset κ

/-- The complete finite space of form-support assignments on `P`. -/
def fixedFamilyPrimeSupportAssignmentChoices
    (κ : Type*) [Fintype κ] [DecidableEq κ]
    (P : Finset Nat.Primes) :
    Finset (FixedFamilyPrimeSupportAssignment κ P) :=
  Fintype.piFinset fun _p : {p // p ∈ P} =>
    (Finset.univ : Finset κ).powerset

/-- The support assignment carried by a paired divisor family. -/
def fixedFamilyPrimeSupportAssignmentOf
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (P : Finset Nat.Primes) (z : κ → ℕ × ℕ) :
    FixedFamilyPrimeSupportAssignment κ P :=
  fun p => pairedPrimeSupport z (p : ℕ)



/-- Total complex common-zero density, equal to one away from natural
primes.  It is only a bookkeeping device for changing between the
`Nat.Primes` and `Nat.primesLE` index types. -/
noncomputable def primeAffineFamilyZeroDensity
    {κ ι : Type*} [Fintype ι] [DecidableEq ι]
    (forms : κ → AffineForm ι ℤ)
    (p : ℕ) (s : Finset κ) : ℂ :=
  if hp : p.Prime then by
    letI : NeZero p := ⟨hp.ne_zero⟩
    exact (affineFamilyZeroDensity p forms s : ℂ)
  else 1



/-- The common-zero-density product attached to one support assignment. -/
noncomputable def fixedFamilyPrimeSupportDensity
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (forms : κ → AffineForm ι ℤ)
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P) : ℂ :=
  ∏ p : {p // p ∈ P},
    primeAffineFamilyZeroDensity forms (p : ℕ) (support p)

/-- The signed Fourier coefficient of one form-support at one prime. -/
noncomputable def fixedFamilyPrimeLocalCoefficient
    {κ : Type*} [Fintype κ]
    (R : ℕ) (t u : κ → ℝ)
    (p : Nat.Primes) (s : Finset κ) : ℂ :=
  (-1 : ℂ) ^ s.card *
    ∏ q ∈ s,
      pairedFourierPrimeCoefficient
        R (p : ℕ) (t q) (u q)

/-- The exact inclusion--exclusion summand at one prime. -/
noncomputable def fixedFamilyPrimeLocalSupportTerm
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (R : ℕ) (forms : κ → AffineForm ι ℤ)
    (t u : κ → ℝ)
    (p : Nat.Primes) (s : Finset κ) : ℂ := by
  letI : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
  exact
    fixedFamilyPrimeLocalCoefficient R t u p s *
      (affineFamilyZeroDensity (p : ℕ) forms s : ℂ)

/-- Product of the signed Fourier coefficients over a finite assignment. -/
noncomputable def fixedFamilyPrimeSupportCoefficient
    {κ : Type*} [Fintype κ]
    (R : ℕ) (t u : κ → ℝ)
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P) : ℂ :=
  ∏ p : {p // p ∈ P},
    fixedFamilyPrimeLocalCoefficient R t u p.1 (support p)

/-- One term in the unrestricted finite support-assignment expansion. -/
noncomputable def fixedFamilyPrimeSupportEulerTerm
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (R : ℕ) (forms : κ → AffineForm ι ℤ)
    (P : Finset Nat.Primes) (t u : κ → ℝ)
    (support : FixedFamilyPrimeSupportAssignment κ P) : ℂ :=
  ∏ p : {p // p ∈ P},
    fixedFamilyPrimeLocalSupportTerm
      R forms t u p.1 (support p)



/-! ## Exact unrestricted finite Euler factorization -/







/-! ## The exact coordinatewise-truncated support fibers -/

/-- The Fourier transforms common to every paired divisor term at fixed
frequencies. -/
noncomputable def pairedCutoffFourierEnvelope
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) (t u : κ → ℝ) : ℂ :=
  (∏ q, χ.cutoffFourierTransform (t q)) *
    ∏ q, χ.cutoffFourierTransform (u q)





/-- The exact transformed coefficient of one support fiber inside the
coordinatewise box `1 ≤ d_q,e_q ≤ R`. -/
noncomputable def coordinatewiseTruncatedSupportCoefficient
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (P : Finset Nat.Primes) (t u : κ → ℝ)
    (support : FixedFamilyPrimeSupportAssignment κ P) : ℂ :=
  ∑ z ∈ SmoothSieveCutoff.squarefreeSmoothPairedDivisorChoices κ R with
      fixedFamilyPrimeSupportAssignmentOf P z = support,
    χ.transformedPairedDivisorFamily R z (t, u)



/-! ## Replacing the supported prime range by the CRT Euler product -/





/-! ## The exact truncated-to-unrestricted splice -/

/-- The finite CRT Euler product attached to one paired divisor family and
one fixed affine family. -/
noncomputable def fixedFamilyDivisorEulerProduct
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (forms : κ → AffineForm ι ℤ)
    (z : κ → ℕ × ℕ) : ℂ :=
  ∏ p : (pairedDivisorLcm z).primeFactors, by
    letI : NeZero (p : ℕ) :=
      ⟨(Nat.prime_of_mem_primeFactors p.2).ne_zero⟩
    exact
      (affineFamilyZeroDensity (p : ℕ) forms
        (pairedPrimeSupport z p) : ℂ)



/-- Difference, at one support assignment, between the actual
coordinatewise-truncated Fourier coefficient and its unrestricted
primewise coefficient. -/
noncomputable def coordinatewiseTruncationSupportDiscrepancy
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (P : Finset Nat.Primes) (t u : κ → ℝ)
    (support : FixedFamilyPrimeSupportAssignment κ P) : ℂ :=
  coordinatewiseTruncatedSupportCoefficient χ R P t u support -
    pairedCutoffFourierEnvelope χ t u *
      fixedFamilyPrimeSupportCoefficient R t u support





/-! ## Canonical fixed-carry specialization -/

/-- The fixed-family CRT product on one canonical carry cell, viewed in
`ℂ` for Fourier expansion. -/
noncomputable def cfzCanonicalCarryFixedDivisorEulerProduct
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k : ℕ}
    (N W b : ℕ) (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ) (z : κ → ℕ × ℕ) : ℂ :=
  fixedFamilyDivisorEulerProduct
    (cfzCarryAdjustedFamilyAtVector N W b forms carry) z

/-- Prime-support density on one canonical fixed-carry family. -/
noncomputable def cfzCanonicalCarryPrimeSupportDensity
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k : ℕ}
    (N W b : ℕ) (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P) : ℂ :=
  fixedFamilyPrimeSupportDensity
    (cfzCarryAdjustedFamilyAtVector N W b forms carry) support

/-- Paired Fourier local factor on one canonical fixed-carry family. -/
noncomputable def cfzCanonicalCarryPairedFourierPrimeLocalFactor
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k : ℕ}
    (N W b R : ℕ) (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ) (t u : κ → ℝ)
    (p : Nat.Primes) : ℂ :=
  pairedFourierPrimeLocalFactor R
    (cfzCarryAdjustedFamilyAtVector N W b forms carry) t u p





/-! ## The carry-weighted canonical endpoint -/

/-- The canonical carry average of the finite unrestricted prime-support
series at fixed Fourier frequencies. -/
noncomputable def cfzCanonicalCarryUnrestrictedFourierAverage
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (W b R : ℕ) (forms : κ → CFZFormIndex k)
    (t u : κ → ℝ) : ℂ :=
  ∑ carry ∈ cfzCanonicalCarryVectorChoices κ k,
    (cfzCanonicalCarryCellDensity
        (N := N) forms carry : ℂ) *
      ∑ S ∈ (primesLEAsPrimes R).powerset,
        unrestrictedPrimeSupportTerm
          (cfzCanonicalCarryPairedFourierPrimeLocalFactor
            N W b R forms carry t u) S

/-- The complete carry-weighted coordinatewise-truncation discrepancy. -/
noncomputable def cfzCanonicalCarryTruncationDiscrepancy
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (W b R : ℕ) (forms : κ → CFZFormIndex k)
    (t u : κ → ℝ) : ℂ :=
  ∑ carry ∈ cfzCanonicalCarryVectorChoices κ k,
    (cfzCanonicalCarryCellDensity
        (N := N) forms carry : ℂ) *
      ∑ support ∈
          fixedFamilyPrimeSupportAssignmentChoices
            κ (primesLEAsPrimes R),
        coordinatewiseTruncationSupportDiscrepancy
            χ R (primesLEAsPrimes R) t u support *
          cfzCanonicalCarryPrimeSupportDensity
            N W b forms carry support







end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.cfzCanonicalCarryFixedDivisorEulerProduct.congr_simp,
    `Wikipedia.SzemeredisTheorem.coordinatewiseTruncatedSupportCoefficient.congr_simp,
    `Wikipedia.SzemeredisTheorem.coordinatewiseTruncationSupportDiscrepancy.congr_simp,
    `Wikipedia.SzemeredisTheorem.fixedFamilyDivisorEulerProduct.eq_1,
    `Wikipedia.SzemeredisTheorem.fixedFamilyPrimeLocalSupportTerm.congr_simp,
    `Wikipedia.SzemeredisTheorem.fixedFamilyPrimeLocalSupportTerm.eq_1,
    `Wikipedia.SzemeredisTheorem.fixedFamilyPrimeSupportAssignmentChoices.eq_1,
    `Wikipedia.SzemeredisTheorem.fixedFamilyPrimeSupportCoefficient.eq_1,
    `Wikipedia.SzemeredisTheorem.fixedFamilyPrimeSupportDensity.congr_simp,
    `Wikipedia.SzemeredisTheorem.fixedFamilyPrimeSupportDensity.eq_1,
    `Wikipedia.SzemeredisTheorem.fixedFamilyPrimeSupportEulerTerm.congr_simp,
    `Wikipedia.SzemeredisTheorem.fixedFamilyPrimeSupportEulerTerm.eq_1,
    `Wikipedia.SzemeredisTheorem.primeAffineFamilyZeroDensity.congr_simp,
    `Wikipedia.SzemeredisTheorem.primeAffineFamilyZeroDensity.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"



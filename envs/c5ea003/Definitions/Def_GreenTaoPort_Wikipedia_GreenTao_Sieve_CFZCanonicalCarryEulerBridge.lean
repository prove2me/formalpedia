-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryEulerBridge
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryEulerBridge
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:11:35.102838+00:00
-- url     : https://prove2.me/theorems/771c52bc-3bd0-4799-acd5-93e6ed2a91b3
-- title:
--   Fixed affine residue models on canonical carry cells
-- statement:
--   For a finite CFZ family and a specified integer carry vector, the carry-adjusted affine family is fixed directly from the cyclic modulus and $W$-trick parameters. Its natural residue evaluations and paired divisibility indicator are taken modulo the least common multiple of a chosen paired-divisor family, when that modulus is nonzero.
--
--   The canonical cell density is the normalized box average of its exact carry indicator. Two cell contributions retain either the original cyclic divisibility conditions or the fixed residue model inside that cell; a separate residue density averages the fixed model over a complete residue box.
--
--   The Euler average sums, over the uniform finite carry range, the cell density times the product of the affine common-zero densities at primes dividing the divisor LCM. The explicit cell-boundary error combines the relative outer trimming loss with the relative number of trimmed carry-transition bad points. These are definitions of the finite comparison quantities, before any small-error estimate is asserted.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/CFZCanonicalCarryEulerBridge.lean#L25-L757

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCongruenceBoundary
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedLocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedGoodPrime
import Lean
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
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Fixed-family Euler products on canonical CFZ carry cells

The canonical carry vector is chosen before the paired divisor variables.
On one of its fibers, every cyclic CFZ value is represented by one fixed
carry-adjusted affine family.  This file defines its residue model, proves
periodicity and the exact CRT Euler product, and inserts it into the
canonical-cell discrepancy theorem.

Unlike the quotient-block Euler average, the affine family in this file
does not depend on the divisor LCM.  This is the structural feature needed
to compare the coordinatewise-truncated divisor expansion with one
unrestricted prime-support Euler series.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## A fixed family attached to one canonical carry vector -/

/-- Carry-adjusted affine family attached directly to a complete carry
vector, rather than to a divisor-dependent quotient block. -/
def cfzCarryAdjustedFamilyAtVector
    {κ : Type*} {k : ℕ}
    (N W b : ℕ)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (q : κ) : AffineForm (CFZVariable k) ℤ :=
  cfzCarryAdjustedAffineForm N W b (forms q) (carry q)

/-- Natural representative modulo `D` of the fixed carry-adjusted affine
family. -/
def cfzCarryAdjustedResidueValueAtVector
    {κ : Type*} {k D : ℕ} [NeZero D]
    (N W b : ℕ)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (q : κ)
    (x : CFZVariable k → ZMod D) : ℕ :=
  affineFormResidueValue
    (cfzCarryAdjustedFamilyAtVector N W b forms carry q) x



/-! ## Periodicity -/





/-! ## Agreement with the cyclic value on one canonical cell -/







/-! ## Exact residue mean and CRT product -/





/-! ## Per-cell cyclic-to-Euler comparison -/

/-- The periodic paired indicator of one fixed carry-adjusted family. -/
noncomputable def cfzCarryVectorResiduePairedIndicator
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k : ℕ}
    (N W b : ℕ)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (z : κ → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)]
    (x : CFZVariable k → ℕ) : ℝ :=
  pairedDivisibilityIndicator
    (fun q y =>
      cfzCarryAdjustedResidueValueAtVector
        (D := pairedDivisorLcm z)
        N W b forms carry q
        (fun v =>
          (y v : ZMod (pairedDivisorLcm z))))
    z x

/-- Density of one canonical carry cell in the standard box. -/
noncomputable def cfzCanonicalCarryCellDensity
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ) : ℝ :=
  boxMean (fun _ : CFZVariable k => N)
    (cfzCanonicalCarryIndicator (N := N) forms carry)

/-- Contribution of one canonical carry cell to the original cyclic paired
divisibility density. -/
noncomputable def cfzCanonicalCarryCellCyclicContribution
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (W b : ℕ)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (z : κ → ℕ × ℕ) : ℝ :=
  boxMean (fun _ : CFZVariable k => N) fun x =>
    cfzCanonicalCarryIndicator (N := N) forms carry x *
      pairedDivisibilityIndicator
        (fun q y =>
          cfzWTrickedLinearValue W b (forms q)
            (cubePointOfNat (N := N) y))
        z x

/-- Exact finite residue density of the fixed family attached to a carry
vector. -/
noncomputable def cfzCarryVectorPairedDivisibilityDensity
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k : ℕ}
    (N W b : ℕ)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (z : κ → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)] : ℝ :=
  pairedDivisibilityDensity
    (fun q =>
      cfzCarryAdjustedResidueValueAtVector
        (D := pairedDivisorLcm z)
        N W b forms carry q)
    z

/-- Explicit per-cell error: outer incomplete blocks plus carry-transition
blocks. -/
noncomputable def cfzCanonicalCarryCellBoundaryError
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (D : ℕ)
    (forms : κ → CFZFormIndex k) : ℝ :=
  4 *
      (((∏ _v : CFZVariable k, N) -
          ∏ _v : CFZVariable k,
            trimToMultiple D N : ℕ) : ℝ) /
        ∏ _v : CFZVariable k, (N : ℝ) +
    2 *
      (((cfzTrimmedFamilyCarryBadPoints
          (N := N) D forms).card : ℝ) /
        ∏ _v : CFZVariable k,
          (trimToMultiple D N : ℝ))

/-- Contribution of the fixed residue model on one canonical cell. -/
noncomputable def cfzCanonicalCarryCellResidueContribution
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (W b : ℕ)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (z : κ → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)] : ℝ :=
  boxMean (fun _ : CFZVariable k => N) fun x =>
    cfzCanonicalCarryIndicator (N := N) forms carry x *
      cfzCarryVectorResiduePairedIndicator
        N W b forms carry z x















/-! ## Summing the canonical carry cells -/





/-- Weighted canonical-cell Euler model for one paired divisor choice.  Each
summand uses a fixed affine family independent of the divisor LCM. -/
noncomputable def cfzCanonicalCarryEulerAverage
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (W b : ℕ)
    (forms : κ → CFZFormIndex k)
    (z : κ → ℕ × ℕ) : ℝ :=
  ∑ carry ∈ cfzCanonicalCarryVectorChoices κ k,
    cfzCanonicalCarryCellDensity
        (N := N) forms carry *
      ∏ p : (pairedDivisorLcm z).primeFactors,
        affineFamilyZeroDensity (p : ℕ)
          (cfzCarryAdjustedFamilyAtVector
            N W b forms carry)
          (pairedPrimeSupport z p)



end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.cfzCanonicalCarryCellBoundaryError.congr_simp,
    `Wikipedia.SzemeredisTheorem.cfzCanonicalCarryCellBoundaryError.eq_1,
    `Wikipedia.SzemeredisTheorem.cfzCanonicalCarryCellDensity.eq_1,
    `Wikipedia.SzemeredisTheorem.cfzCanonicalCarryCellResidueContribution.eq_1,
    `Wikipedia.SzemeredisTheorem.cfzCarryAdjustedFamilyAtVector.eq_1,
    `Wikipedia.SzemeredisTheorem.cfzCarryAdjustedResidueValueAtVector.congr_simp,
    `Wikipedia.SzemeredisTheorem.cfzCarryVectorPairedDivisibilityDensity.congr_simp,
    `Wikipedia.SzemeredisTheorem.cfzCarryVectorResiduePairedIndicator.congr_simp
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"



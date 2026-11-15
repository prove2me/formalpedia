-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCyclicBoundaryLimit
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCyclicBoundaryLimit
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:17:41.927564+00:00
-- url     : https://prove2.me/theorems/5b9e7e84-352c-4952-92c2-d1f4b907d1a8
-- title:
--   Canonical Euler divisor main terms and cyclic-boundary constants
-- statement:
--   For a selected CFZ family, the canonical Euler divisor sum is the finite sum of smooth paired-divisor coefficients times their canonical carry-Euler averages. Its normalized main term multiplies this sum by the selected-family powers of the normalized Selberg scale and $(\log R)^2$. The same expression is also supplied as a complex Fourier-integral main term.
--
--   The boundary constant is the number of canonical carry vectors times the uniform cell-error coefficient, and the scaled version additionally divides by the corresponding power of the cutoff normalizer. The fixed boundary exponent is five times the cardinality of the full ambient CFZ form family. These choices keep the combinatorial constants separate from the varying cyclic modulus and sieve level.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/CFZCanonicalCyclicBoundaryLimit.lean#L22-L519

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryBoundaryBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalDivisorExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryDivisorExpansion
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
# Summed canonical cyclic-to-Euler boundary

The canonical carry partition compares the cyclic paired-divisibility
density with a divisor-independent affine Euler model.  Its pointwise error
is proportional to the paired-divisor LCM divided by the cyclic modulus.
This file sums that estimate over every divisor family selected by a
Boolean CFZ exponent, restores the Selberg normalization, and records a
joint power-scale limit.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter MeasureTheory Topology
open scoped ArithmeticFunction.Moebius BigOperators

/-- The canonical Euler divisor sum for one Boolean-selected CFZ family. -/
noncomputable def selectedCFZCanonicalEulerDivisorSum
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff) (R W b : ℕ)
    (e : LinearFormsExponent k) : ℝ :=
  ∑ z ∈ smoothDivisorFamilyChoices
        (SelectedCFZFormIndex e) R,
    smoothDivisorFamilyCoefficient χ.toFun R z *
      cfzCanonicalCarryEulerAverage
        (N := N) W b
        (fun q : SelectedCFZFormIndex e => q.1) z

/-- The finite constant contributed by the number of canonical carry
vectors and the uniform boundary estimate for one carry cell. -/
noncomputable def selectedCFZCanonicalCyclicBoundaryConstant
    {k : ℕ} (e : LinearFormsExponent k) : ℕ :=
  (cfzCanonicalCarryVectorChoices
      (SelectedCFZFormIndex e) k).card *
    cfzCanonicalCarryCellErrorConstant
      (SelectedCFZFormIndex e) k









/-! ## Selberg-scaled canonical main terms -/

/-- The canonical Euler approximation to a cyclic-majorant selected
subproduct mean. -/
noncomputable def SmoothSieveCutoff.selectedCFZCanonicalEulerMainTerm
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff) (R W b : ℕ)
    (e : LinearFormsExponent k) : ℝ :=
  normalizedSelbergScale χ.normalizer R W ^
        Fintype.card (SelectedCFZFormIndex e) *
    ((Real.log R ^ 2) ^
        Fintype.card (SelectedCFZFormIndex e) *
      selectedCFZCanonicalEulerDivisorSum
        (N := N) χ R W b e)

/-- The same canonical main term written as one complex Fourier integral. -/
noncomputable def
    SmoothSieveCutoff.selectedCFZCanonicalEulerFourierMainTerm
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff) (R W b : ℕ)
    (e : LinearFormsExponent k) : ℂ :=
  (normalizedSelbergScale χ.normalizer R W : ℂ) ^
        Fintype.card (SelectedCFZFormIndex e) *
    (((Real.log R ^ 2 : ℝ) : ℂ) ^
        Fintype.card (SelectedCFZFormIndex e) *
      ∫ tu :
          (SelectedCFZFormIndex e → ℝ) ×
            (SelectedCFZFormIndex e → ℝ),
        χ.divisorExpansionFourierIntegrand R
          (fun z =>
            cfzCanonicalCarryEulerAverage
              (N := N) W b
              (fun q : SelectedCFZFormIndex e => q.1) z)
          tu ∂(volume.prod volume))











/-! ## A single polynomial joint scale -/

/-- Uniform power exponent for the canonical cyclic boundary.  Five powers
per ambient CFZ form absorb four divisor-box powers and one Selberg
normalization power. -/
def cfzCanonicalCyclicBoundaryExponent (k : ℕ) : ℕ :=
  5 * Fintype.card (CFZFormIndex k)

/-- The fixed scaled constant in the canonical cyclic boundary estimate. -/
noncomputable def
    SmoothSieveCutoff.selectedCFZCanonicalScaledCyclicBoundaryConstant
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) : ℝ :=
  χ.normalizer⁻¹ ^
      Fintype.card (SelectedCFZFormIndex e) *
    (selectedCFZCanonicalCyclicBoundaryConstant e : ℝ)



















end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.selectedCFZCanonicalEulerMainTerm.congr_simp,
    `Wikipedia.SzemeredisTheorem.selectedCFZCanonicalEulerDivisorSum.congr_simp
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"



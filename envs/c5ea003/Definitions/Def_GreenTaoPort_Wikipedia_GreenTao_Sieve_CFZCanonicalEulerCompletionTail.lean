-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalEulerCompletionTail
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalEulerCompletionTail
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:22:15.620544+00:00
-- url     : https://prove2.me/theorems/8eaa5c44-adea-457c-9786-3d38f23957ab
-- title:
--   Constants and norms for the canonical Euler-completion tail
-- statement:
--   For a selected CFZ pattern $e$ with $m$ forms, the unscaled polylogarithmic exponent is $3m$ and its radius-independent constant is $2^{4^m}$. With a smooth cutoff $\chi$, primorial parameter $w$, and sieve radius $R$, the scaled support mass multiplies the complete support mass by the absolute Selberg-scale factor to the power $m$ and $|\log(R)^2|^m$. The scaled exponent is $m+3m$, and the scaled constant is $c_\chi^{-m}2^{4^m}$.
--
--   For $N
--   e0$, residue parameter $b$, and real box radius $T$, the scaled tail norm is the norm of the similarly scaled complete Euler integral over the complement of the selected paired Fourier box. These definitions separate the finite-dimensional Fourier tail from the scalar support-mass bound.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/CFZCanonicalEulerCompletionTail.lean#L141-L1038

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalEulerCompletion
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
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Field

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Polylogarithmic control of the canonical Euler-completion tail

The complete-support majorant has local factor

`1 + 3m p^(-1-1/log R) + 4^m p^(-2)`,

where `m` is the number of selected CFZ forms.  We compare its two
nonconstant pieces with the Euler products for
`ζ(1 + 1 / log R)` and `ζ(2)`.  The elementary bound
`‖ζ(1 + 1 / log R)‖ ≤ 1 + log R` then gives an explicit
polylogarithmic bound for the whole infinite support mass, and hence for
the genuinely missing completion tail.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter MeasureTheory Topology
open scoped BigOperators

/-! ## A two-factor Euler comparison -/





/-! ## The infinite support mass -/

/-- Polylogarithmic exponent supplied by the shifted zeta factor. -/
def selectedCFZCanonicalCompleteSupportPolylogExponent
    {k : ℕ} (e : LinearFormsExponent k) : ℕ :=
  3 * Fintype.card (SelectedCFZFormIndex e)

/-- Radius-independent cost of the absolutely convergent reciprocal-square
Euler factor. -/
noncomputable def selectedCFZCanonicalCompleteSupportPolylogConstant
    {k : ℕ} (e : LinearFormsExponent k) : ℝ :=
  (2 : ℝ) ^ (4 ^ Fintype.card (SelectedCFZFormIndex e))











/-! ## Pointwise and complementary-box bounds -/











/-! ## The completed Euler model on the complementary box -/







/-! ## Selberg-scaled complementary contributions -/

/-- The two Selberg prefactors times the full complete-support mass. -/
noncomputable def
    SmoothSieveCutoff.selectedCFZCanonicalCompleteEulerScaledSupportMass
    {k : ℕ} (χ : SmoothSieveCutoff)
    (w R : ℕ) (e : LinearFormsExponent k) : ℝ :=
  |normalizedSelbergScale χ.normalizer R (primorial w)| ^
      Fintype.card (SelectedCFZFormIndex e) *
    |Real.log R ^ 2| ^
      Fintype.card (SelectedCFZFormIndex e) *
    selectedCFZCanonicalCompleteSupportMass e R



/-- Exponent after including the two Selberg prefactors. -/
def selectedCFZCanonicalCompleteEulerScaledPolylogExponent
    {k : ℕ} (e : LinearFormsExponent k) : ℕ :=
  Fintype.card (SelectedCFZFormIndex e) +
    selectedCFZCanonicalCompleteSupportPolylogExponent e

/-- Constant after including the two Selberg prefactors. -/
noncomputable def
    SmoothSieveCutoff.selectedCFZCanonicalCompleteEulerScaledPolylogConstant
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) : ℝ :=
  χ.normalizer⁻¹ ^ Fintype.card (SelectedCFZFormIndex e) *
    selectedCFZCanonicalCompleteSupportPolylogConstant e









/-- Selberg-scaled norm of the completed Euler model on the
complementary Fourier box. -/
noncomputable def
    SmoothSieveCutoff.selectedCFZCanonicalCompleteEulerScaledTailNorm
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (w b R : ℕ) (e : LinearFormsExponent k) (T : ℝ) : ℝ :=
  ‖(normalizedSelbergScale
        χ.normalizer R (primorial w) : ℂ) ^
        Fintype.card (SelectedCFZFormIndex e) *
      (((Real.log R ^ 2 : ℝ) : ℂ) ^
          Fintype.card (SelectedCFZFormIndex e) *
        ∫ tu in (selectedCFZPairedFourierBox e T)ᶜ,
          χ.cfzCanonicalCarryCompleteEulerIntegrand
            (N := N) (primorial w) b R
            (fun q : SelectedCFZFormIndex e => q.1) tu
          ∂(volume.prod volume))‖







/-! ## High moments and schedule-uniform decay -/











end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.selectedCFZCanonicalCompleteEulerScaledTailNorm.congr_simp,
    `Wikipedia.SzemeredisTheorem.selectedCFZCanonicalCompleteSupportPolylogExponent.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"



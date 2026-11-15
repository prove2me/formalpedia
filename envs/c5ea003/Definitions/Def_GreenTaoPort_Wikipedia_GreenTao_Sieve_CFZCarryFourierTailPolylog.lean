-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierTailPolylog
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierTailPolylog
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:15:09.918462+00:00
-- url     : https://prove2.me/theorems/672a5c2d-9dc5-4435-a069-37433d987faa
-- title:
--   Coordinate moment majorants for paired Fourier tails
-- statement:
--   A single-coordinate moment exponent places a natural order $q$ at one selected frequency coordinate and zero at all others. Summing the associated weighted absolute Fourier densities over the distinguished coordinate gives the one-side moment density.
--
--   The paired density allows the high moment on either Fourier side: the moment-weighted first side times the unweighted second side, plus the unweighted first side times the moment-weighted second side. Its full product-Lebesgue integral is the paired absolute moment. All index sums are finite, and the construction also handles an empty selected family.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/CFZCarryFourierTailPolylog.lean#L29-L144

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryHarmonicLcmEulerBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PrimeHarmonicProductBound
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
# Polylogarithmic closure of the carry Fourier tail

The harmonic LCM mass is bounded by a finite prime product.  The latter is
polylogarithmic, while the cutoff Fourier transform is Schwartz.  This file
makes the quantitative comparison explicit.

For every natural `q`, a finite constant controls

`T ^ q * selectedCFZPairedFourierAbsoluteTail e T`.

Choosing `q` larger than twice the exponent of the prime-product bound makes
the complementary carry Fourier integral vanish at
`T = sqrt (log R)`, without an eventual bounded-mass hypothesis.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace SmoothSieveCutoff

/-! ## Arbitrarily high paired Fourier moments -/

/-- Put the moment `q` on one distinguished Fourier coordinate. -/
def singleCoordinateMomentExponent
    {κ : Type*} [DecidableEq κ]
    (i : κ) (q : ℕ) : κ → ℕ :=
  fun j => if j = i then q else 0



/-- Sum of the `q`-th moments obtained by placing the weight on one
coordinate at a time. -/
noncomputable def selectedCFZOneSideFourierMomentDensity
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) (q : ℕ)
    (t : SelectedCFZFormIndex e → ℝ) : ℝ :=
  ∑ i,
    χ.fourierProductMomentDensity
      (singleCoordinateMomentExponent i q) t





/-- A paired moment majorant: the high moment may lie on either Fourier
side. -/
noncomputable def selectedCFZPairedFourierMomentDensity
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) (q : ℕ)
    (tu :
      (SelectedCFZFormIndex e → ℝ) ×
        (SelectedCFZFormIndex e → ℝ)) : ℝ :=
  χ.selectedCFZOneSideFourierMomentDensity e q tu.1 *
      χ.fourierProductMomentDensity (fun _ => 0) tu.2 +
    χ.fourierProductMomentDensity (fun _ => 0) tu.1 *
      χ.selectedCFZOneSideFourierMomentDensity e q tu.2





/-- The finite total paired `q`-th moment. -/
noncomputable def selectedCFZPairedFourierAbsoluteMoment
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) (q : ℕ) : ℝ :=
  ∫ tu,
    χ.selectedCFZPairedFourierMomentDensity e q tu
    ∂(volume.prod volume)













/-! ## Polylogarithmic arithmetic growth -/











/-! ## Cancellation of arithmetic growth by a higher Fourier moment -/









end SmoothSieveCutoff

end Wikipedia.SzemeredisTheorem



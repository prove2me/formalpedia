-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCompleteMainTermBridge
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCompleteMainTermBridge
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:24:35.786299+00:00
-- url     : https://prove2.me/theorems/e551edac-9e56-482a-b11a-94d918d54c6d
-- title:
--   Scaled canonical Euler integrands and their archimedean baseline
-- statement:
--   Fix a smooth cutoff $\chi$, a selected CFZ family of size $m$, a positive cyclic modulus, and sieve, primorial, and residue parameters. The scaled complete-Euler integrand places the two scalar prefactors inside the Fourier integral: the $m$th power of the normalized Selberg scale and the $m$th power of $(\log R)^2$.
--
--   The archimedean baseline is the product of the one-pair cutoff-normalizer factors over the selected family, multiplied by $c_\chi^{-m}$. These are complex-valued functions of the paired real frequency families. The first retains the full canonical Euler integrand, while the second is its normalized archimedean comparison term.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/CFZCanonicalCompleteMainTermBridge.lean#L373-L403

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalEulerCompletionTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCyclicBoundaryLimit
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierEulerNormalization
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
# Canonical complete-Euler main-term bridge

This file joins the two exact full-space cancellations in the canonical
CFZ expansion.

* Coordinatewise divisor truncation has zero full-space Fourier integral.
* Completing the finite prime support to the honest Euler support has zero
  full-space Fourier integral in the primorial exceptional-prime regime.

Consequently the canonical cyclic-boundary main term is exactly the
Selberg-scaled full-space integral of the complete Euler integrand.

The second half separates this integral into the standard growing Fourier
box and its complement.  The completed complement is already uniformly
controlled by `CFZCanonicalEulerCompletionTail`; the sole remaining input
is an interior pointwise comparison with the normalized archimedean
baseline.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter MeasureTheory Topology
open scoped BigOperators

/-! ## Integrability of the complete canonical Euler model -/





/-! ## Exact finite-to-complete main term -/







/-! ## Scaled integrand and normalized archimedean baseline -/

/-- The complete canonical Euler integrand with both Selberg prefactors
placed pointwise inside the Fourier integral. -/
noncomputable def
    SmoothSieveCutoff.selectedCFZCanonicalCompleteEulerScaledIntegrand
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (w b R : ℕ) (e : LinearFormsExponent k)
    (tu :
      (SelectedCFZFormIndex e → ℝ) ×
        (SelectedCFZFormIndex e → ℝ)) : ℂ :=
  (normalizedSelbergScale
      χ.normalizer R (primorial w) : ℂ) ^
        Fintype.card (SelectedCFZFormIndex e) *
    (((Real.log R ^ 2 : ℝ) : ℂ) ^
        Fintype.card (SelectedCFZFormIndex e) *
      χ.cfzCanonicalCarryCompleteEulerIntegrand
        (N := N) (primorial w) b R
        (fun q : SelectedCFZFormIndex e => q.1) tu)

/-- The normalized archimedean product which remains after exact
Selberg/zeta normalization. -/
noncomputable def
    SmoothSieveCutoff.selectedCFZCanonicalArchimedeanBaseline
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k)
    (tu :
      (SelectedCFZFormIndex e → ℝ) ×
        (SelectedCFZFormIndex e → ℝ)) : ℂ :=
  ((χ.normalizer : ℂ)⁻¹) ^
      Fintype.card (SelectedCFZFormIndex e) *
    χ.cutoffNormalizerSeparatedProduct tu



















/-! ## Interior comparison and the complete integration estimate -/





end Wikipedia.SzemeredisTheorem



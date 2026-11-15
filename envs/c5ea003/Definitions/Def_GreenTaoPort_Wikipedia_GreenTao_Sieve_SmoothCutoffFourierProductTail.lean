-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierProductTail
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierProductTail
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T08:52:37.372681+00:00
-- url     : https://prove2.me/theorems/ebe3bb00-aa4a-4142-a25a-ac644d91d50e
-- title:
--   Finite Fourier products, weighted moment densities, and truncation boxes
-- statement:
--   Let $K$ be a finite coordinate type and let $F_\chi$ be the Fourier transform of $x\mapsto e^x\chi(x)$. For a real frequency vector $t:K\to\mathbb R$, the product transform is
--
--   $$
--   \prod_{q\in K}F_\chi(t_q).
--   $$
--
--   For coordinate moment orders $k_q\in\mathbb N$, the associated nonnegative density is $\prod_q |t_q|^{k_q}|F_\chi(t_q)|$. The frequency truncation box of radius $T$ is the closed ball about zero in the finite product's sup norm, equivalently the coordinatewise region $|t_q|\le T$ when $T\ge0$. Empty coordinate families use the usual empty-product convention.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/SmoothCutoffFourierProductTail.lean#L26-L84

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierTail
import Mathlib.MeasureTheory.Integral.Pi
import Lean
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Nat.Totient
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Finite-product Fourier tails

This file lifts the one-dimensional Schwartz tail estimates for a smooth
sieve cutoff to an arbitrary finite family of Fourier variables.  The
ambient product uses Mathlib's canonical volume measure on `κ → ℝ`, which
is definitionally identified with the finite product of one-dimensional
Lebesgue measures.

The main output is that every coordinatewise polynomially weighted product
of absolute Fourier transforms is integrable and has vanishing mass outside
the sup-norm box of radius `T`, including the standard radius
`sqrt (log R)`.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace SmoothSieveCutoff

/-- Product of the cutoff Fourier transforms over a finite coordinate
family. -/
noncomputable def fourierProductTransform
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) (t : κ → ℝ) : ℂ :=
  ∏ i, χ.cutoffFourierTransform (t i)

/-- A coordinatewise polynomially weighted absolute Fourier density. -/
noncomputable def fourierProductMomentDensity
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) (k : κ → ℕ)
    (t : κ → ℝ) : ℝ :=
  ∏ i, χ.fourierMomentDensity (k i) (t i)









/-- The sup-norm Fourier box of radius `T`. -/
def fourierProductBox
    {κ : Type*} [Fintype κ] (T : ℝ) : Set (κ → ℝ) :=
  Metric.closedBall 0 T













end SmoothSieveCutoff

end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.fourierProductBox.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"



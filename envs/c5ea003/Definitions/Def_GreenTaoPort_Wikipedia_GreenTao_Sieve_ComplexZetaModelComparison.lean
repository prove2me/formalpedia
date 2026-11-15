-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexZetaModelComparison
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexZetaModelComparison
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:04:20.900005+00:00
-- url     : https://prove2.me/theorems/7b70fd10-dd3a-4deb-a36e-eb62ef229bc8
-- title:
--   Exact zeta local models and arithmetic-to-zeta ratios
-- statement:
--   This bundle defines the higher-order part of a finite complex product and the paired phase models $1-p^{-1}(z+w-zw)$ and $((1-p^{-1}z)(1-p^{-1}w))/(1-p^{-1}zw)$. It also provides their complex-power and exact Fourier-shift versions and the products of these factors over a finite form family.
--
--   For a system of $m$ forms, explicit comparison constants and natural cutoffs control the difference and nonvanishing estimates. For finite affine-form families over a nonzero modulus $p$, the arithmetic-to-zeta local ratio is the paired arithmetic local factor divided by the exact finite-system zeta Euler factor. The ratio-error constant is four times the combined arithmetic-zeta difference constant.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/ComplexZetaModelComparison.lean#L41-L907

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexLocalFactorControl
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_FourierZetaParameters
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
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Comparing Fourier local factors with zeta Euler models

For one pair of Fourier phases `z, w` and `r = 1 / p`, the first-order
arithmetic model is

`1 - r * (z + w - z * w)`.

The corresponding local factor of the zeta quotient is

`((1 - r * z) * (1 - r * w)) / (1 - r * z * w)`.

Their difference has the exact factorization

`r² z w (1 - z) (1 - w) / (1 - r z w)`.

At a prime, the Fourier phases have norm at most one.  The denominator is
therefore bounded below by `1/2`, and the difference is at most `8 / p²`,
uniformly in both Fourier parameters.

For a finite system of `m` forms, expanding the product separates the sum
of the singleton errors from supports of size at least two.  Above `p ≥ 7`,
the latter are bounded by `49 * 2^m / p²`.  This gives an explicit
finite-system comparison with the combined first-order model, and hence a
ratio comparison above the additional stability cutoff `p ≥ 6m`.

The final section combines this result with the affine rank-two calculation
from `ComplexLocalFactorControl`.  It remains entirely local: no infinite
prime-product identity and no multivariate Fourier integration is asserted.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## A generic finite-product second-order remainder -/

/-- The part of `∏ q, (1 + e q)` supported on subsets of cardinality at
least two. -/
noncomputable def complexProductHigherOrderRemainder
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (e : κ → ℂ) : ℂ :=
  ∑ s ∈ higherOrderSelectedSupports κ,
    ∏ q ∈ s, e q







/-! ## One paired phase -/

/-- First-order local model for one pair of phases. -/
noncomputable def phasePairFirstOrderLocalModel
    (p : ℕ) (z w : ℂ) : ℂ :=
  1 - (p : ℂ)⁻¹ * (z + w - z * w)

/-- Exact local Euler factor of one zeta quotient, written in its
phase coordinates. -/
noncomputable def phasePairZetaEulerLocalModel
    (p : ℕ) (z w : ℂ) : ℂ :=
  ((1 - (p : ℂ)⁻¹ * z) *
      (1 - (p : ℂ)⁻¹ * w)) /
    (1 - (p : ℂ)⁻¹ * z * w)











/-! ## Exact cpow coordinates -/

/-- The per-form local Euler factor of the zeta quotient in complex-power
coordinates. -/
noncomputable def pairedZetaEulerLocalFactor
    (p : ℕ) (u v : ℂ) : ℂ :=
  ((1 - (p : ℂ) ^ (-((1 : ℂ) + u))) *
      (1 - (p : ℂ) ^ (-((1 : ℂ) + v)))) /
    (1 - (p : ℂ) ^
      (-((1 : ℂ) + u + v)))







/-- Per-form zeta Euler factor at the exact Fourier shifts fixed by
`FourierZetaParameters`. -/
noncomputable def fourierPairZetaEulerLocalFactor
    (R p : ℕ) (t u : ℝ) : ℂ :=
  pairedZetaEulerLocalFactor p
    (cutoffZetaShift R t)
    (cutoffZetaShift R u)



/-! ## Finite systems -/

/-- Product of the elementary phase-coordinate zeta Euler factors for a
finite system. -/
noncomputable def phaseZetaSystemEulerLocalFactor
    {κ : Type*} [Fintype κ]
    (p : ℕ) (z w : κ → ℂ) : ℂ :=
  ∏ q, phasePairZetaEulerLocalModel p (z q) (w q)

/-- Product of the exact cpow zeta Euler factors for all paired Fourier
parameters. -/
noncomputable def fourierZetaSystemEulerLocalFactor
    {κ : Type*} [Fintype κ]
    (R p : ℕ) (t u : κ → ℝ) : ℂ :=
  ∏ q, fourierPairZetaEulerLocalFactor
    R p (t q) (u q)



/-- Explicit finite-system difference constant. -/
noncomputable def complexZetaModelDifferenceConstant
    (m : ℕ) : ℝ :=
  8 * m + 49 * (2 : ℝ) ^ m















/-- Single explicit numerical cutoff for the system comparison. -/
def complexZetaModelComparisonCutoff (m : ℕ) : ℕ :=
  max 7 (6 * m)



/-! ## Direct arithmetic/zeta comparison -/

/-- Difference constant after combining the affine local calculation with
the zeta-model comparison. -/
noncomputable def complexArithmeticZetaDifferenceConstant
    (m : ℕ) : ℝ :=
  (4 : ℝ) ^ m +
    complexZetaModelDifferenceConstant m





/-- A natural-valued copy of the zeta-model difference constant, used only
to state a numerical stability cutoff. -/
def complexZetaModelDifferenceNat (m : ℕ) : ℕ :=
  8 * m + 49 * 2 ^ m



/-- A cutoff large enough both for the first-order stability estimates and
to keep the exact zeta model at norm at least `1/4`. -/
def complexZetaModelNonzeroCutoff (m : ℕ) : ℕ :=
  max
    (complexZetaModelComparisonCutoff m)
    (4 * complexZetaModelDifferenceNat m)



/-- Direct ratio of the arithmetic affine local factor to the exact zeta
Euler model. -/
noncomputable def pairedFourierArithmeticToZetaLocalRatio
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (R p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    (t u : κ → ℝ) : ℂ :=
  pairedFourierLocalFactor R p forms t u /
    fourierZetaSystemEulerLocalFactor R p t u

/-- Error constant for the direct arithmetic/zeta ratio. -/
noncomputable def complexArithmeticZetaRatioErrorConstant
    (m : ℕ) : ℝ :=
  4 * complexArithmeticZetaDifferenceConstant m





end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.complexArithmeticZetaDifferenceConstant.eq_1,
    `Wikipedia.SzemeredisTheorem.complexArithmeticZetaRatioErrorConstant.eq_1,
    `Wikipedia.SzemeredisTheorem.complexZetaModelDifferenceConstant.eq_1,
    `Wikipedia.SzemeredisTheorem.complexZetaModelDifferenceNat.eq_1,
    `Wikipedia.SzemeredisTheorem.fourierPairZetaEulerLocalFactor.eq_1,
    `Wikipedia.SzemeredisTheorem.pairedFourierArithmeticToZetaLocalRatio.eq_1,
    `Wikipedia.SzemeredisTheorem.pairedZetaEulerLocalFactor.eq_1,
    `Wikipedia.SzemeredisTheorem.phasePairFirstOrderLocalModel.eq_1,
    `Wikipedia.SzemeredisTheorem.phasePairZetaEulerLocalModel.eq_1,
    `Wikipedia.SzemeredisTheorem.phaseZetaSystemEulerLocalFactor.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"



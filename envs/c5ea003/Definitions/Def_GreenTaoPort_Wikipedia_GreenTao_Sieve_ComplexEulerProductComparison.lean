-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexEulerProductComparison
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexEulerProductComparison
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:05:42.358628+00:00
-- url     : https://prove2.me/theorems/18b7d559-c140-4a57-ae7d-ccddf78852bc
-- title:
--   Quantitative cutoffs and prime-indexed arithmetic-to-zeta ratios
-- statement:
--   For a system size $m$, the natural ratio-error bound is four times the sum of $4^m$ and the existing zeta-model difference bound. The nonvanishing cutoff is the maximum of the zeta-model cutoff and twice this ratio-error bound. For a finite integer affine family, the full exceptional bound also includes its explicit coefficient-and-minor bound.
--
--   The bundle reindexes the exact paired Fourier arithmetic factor and its arithmetic-to-zeta ratio by the subtype of natural primes, supplying the prime's nonzero modulus instance. These are the local factors used in unordered complex Euler products; no extra convergence premise is inserted into their definitions.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/ComplexEulerProductComparison.lean#L43-L93

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexZetaModelComparison
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ZetaEulerProductIdentification
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
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# The complex arithmetic Euler product as zeta model times correction

`ComplexZetaModelComparison` proves, at every sufficiently large prime, that
the exact affine-system local factor divided by its zeta Euler model is
`1 + O_m(p⁻²)`.  This file promotes that local estimate to an unordered
Euler product.

There are three small points which are made explicit here.

* The exceptional cutoff contains both the finite affine-rank exceptional
  set and the quantitative nonvanishing range for the zeta model.
* The zeta model is in fact nonzero at every prime.  Consequently the
  arithmetic/zeta ratio is defined by honest cancellation at all primes.
* Replacing the finitely many uncontrolled ratios by one gives a globally
  square-decaying family.  The cutoff also makes every remaining ratio
  lie in the radius-`1/2` ball around one, so the masked family is
  pointwise nonzero.  Mathlib's finite-change theorem for products in a
  commutative group-with-zero then restores the exceptional factors.

Combining the resulting correction product with
`cutoffZetaEulerLocalFactor_hasProd` identifies the exact arithmetic prime
product as

`(elementary singular factor) * (completed zeta factor) *
  (convergent arithmetic correction)`.

No nonvanishing assertion is made for the correction without an explicit
nonvanishing hypothesis on the arithmetic local factors: a complex finite
average can in principle vanish.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter
open scoped BigOperators

/-! ## Prime-indexed local factors and the common cutoff -/

/-- Natural-valued copy of the arithmetic/zeta ratio error constant. -/
def complexArithmeticZetaRatioErrorNat (m : ℕ) : ℕ :=
  4 * (4 ^ m + complexZetaModelDifferenceNat m)



/-- A cutoff which both makes the zeta denominator nonzero and makes the
arithmetic/zeta ratio lie in the radius-`1/2` ball around one. -/
def complexArithmeticZetaRatioNonzeroCutoff (m : ℕ) : ℕ :=
  max
    (complexZetaModelNonzeroCutoff m)
    (2 * complexArithmeticZetaRatioErrorNat m)

/-- A cutoff containing both the affine rank exceptions and the
quantitative nonvanishing range used in the local ratio estimate. -/
def complexArithmeticZetaExceptionalBound
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (forms : κ → AffineForm ι ℤ) : ℕ :=
  max
    (exceptionalPrimeBound forms)
    (complexArithmeticZetaRatioNonzeroCutoff
      (Fintype.card κ))

/-- The exact paired Fourier local factor, indexed by the subtype of
natural primes. -/
noncomputable def pairedFourierPrimeLocalFactor
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (R : ℕ) (forms : κ → AffineForm ι ℤ)
    (t u : κ → ℝ) (p : Nat.Primes) : ℂ := by
  letI : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
  exact pairedFourierLocalFactor R (p : ℕ) forms t u

/-- The exact arithmetic/zeta local ratio, indexed by natural primes. -/
noncomputable def primePairedFourierArithmeticToZetaLocalRatio
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (R : ℕ) (forms : κ → AffineForm ι ℤ)
    (t u : κ → ℝ) (p : Nat.Primes) : ℂ := by
  letI : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
  exact pairedFourierArithmeticToZetaLocalRatio
    R (p : ℕ) forms t u



/-! ## Pointwise nonvanishing of the zeta model -/











/-! ## Square decay and the convergent correction product -/





















/-! ## Exact global Euler-product identification -/









end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.complexArithmeticZetaRatioErrorNat.eq_1,
    `Wikipedia.SzemeredisTheorem.pairedFourierPrimeLocalFactor.eq_1,
    `Wikipedia.SzemeredisTheorem.primePairedFourierArithmeticToZetaLocalRatio.congr_simp,
    `Wikipedia.SzemeredisTheorem.primePairedFourierArithmeticToZetaLocalRatio.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"



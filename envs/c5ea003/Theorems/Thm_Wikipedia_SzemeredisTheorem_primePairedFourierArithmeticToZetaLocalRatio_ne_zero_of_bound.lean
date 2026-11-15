-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_primePairedFourierArithmeticToZetaLocalRatio_ne_zero_of_bound
-- name    : Wikipedia.SzemeredisTheorem.primePairedFourierArithmeticToZetaLocalRatio_ne_zero_of_bound
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:26:15.952601+00:00
-- url     : https://prove2.me/theorems/41677bbb-7d18-47d3-b502-1406a902a1a3
-- title:
--   Large-prime arithmetic-to-zeta ratios are nonzero
-- statement:
--   For a finite integer affine-form family with nonzero coefficient vectors and pairwise independent coefficients, let $R\ge2$ and choose any Fourier vectors $t,u$. If a prime $p$ exceeds the explicit complex arithmetic-zeta exceptional bound for the family, its paired Fourier arithmetic-to-zeta local ratio is nonzero.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/ComplexEulerProductComparison.lean#L241-L296

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexEulerProductComparison
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexLocalFactorControl
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexZetaModelComparison
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CongruenceAverage
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ExceptionalPrimes
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_FourierZetaParameters
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeAffineRank
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeLocalFactorBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LinearFormsExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedDivisibilityCRT
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedLocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourier
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ZetaEulerProductIdentification
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ZetaNearOne
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
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
open Wikipedia.SzemeredisTheorem
open Filter
open scoped BigOperators
/-! ## Prime-indexed local factors and the common cutoff -/
/-! ## Pointwise nonvanishing of the zeta model -/
/-! ## Square decay and the convergent correction product -/

theorem Wikipedia.SzemeredisTheorem.primePairedFourierArithmeticToZetaLocalRatio_ne_zero_of_bound
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : NonzeroCoefficientVectors forms)
    (hindependent : PairwiseIndependentCoefficients forms)
    {R : ℕ} (hR : 2 ≤ R)
    (t u : κ → ℝ) (p : Nat.Primes)
    (hlarge :
      complexArithmeticZetaExceptionalBound forms <
        (p : ℕ)) :
    primePairedFourierArithmeticToZetaLocalRatio
      R forms t u p ≠ 0 := by sorry

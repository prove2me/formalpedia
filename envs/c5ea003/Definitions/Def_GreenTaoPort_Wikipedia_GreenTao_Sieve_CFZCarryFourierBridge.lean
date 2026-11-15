-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierBridge
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierBridge
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:10:26.903393+00:00
-- url     : https://prove2.me/theorems/3f5d59fc-bec8-4c56-9ea2-ed10ca3d39d2
-- title:
--   Paired Fourier truncation boxes for selected CFZ families
-- statement:
--   For a Boolean-selected family of CFZ forms and a real radius $T$, the paired Fourier box is the Cartesian product of two copies of the finite-coordinate sup-norm closed ball of radius $T$ about zero. A point consists of two real frequency families $(t_q,u_q)$ indexed by the selected forms. For $T\ge0$, membership requires $|t_q|\le T$ and $|u_q|\le T$ at every selected coordinate. This is the domain used to truncate the paired Fourier divisor integral.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/CFZCarryFourierBridge.lean#L207-L214

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryDivisorExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCongruenceBoundary
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedLocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedGoodPrime
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_MultivariateFourierExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexEulerProductComparison
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
# Fourier inversion with the CFZ carry-block average retained

The carry decomposition does not produce one common arithmetic Euler
product.  For a paired divisor family `z`, both the quotient-block box and
the local prime product depend on `pairedDivisorLcm z`.  This file keeps
that dependence inside the finite divisor sum and applies Fourier inversion
only to the smooth coefficient of each individual family.

Thus the exact integrand below has the honest shape

`∑ z, (mean over the quotient blocks belonging to z) *
  (transformed coefficient belonging to z)`.

No multiplicative closure of the truncated choices `d ≤ R` is used.  The
last results also split the exact integral into a finite Fourier box and its
complement, providing the interface needed for a subsequent uniform
Fourier-box comparison and tail estimate.
-/

namespace Wikipedia.SzemeredisTheorem

open MeasureTheory
open scoped ArithmeticFunction.Moebius BigOperators

namespace SmoothSieveCutoff

/-! ## The blockwise arithmetic coefficient -/







/-! ## The carry-dependent Fourier integrand -/









/-! ## Exact divisor-sum and scaled-main-term bridges -/





/-! ## Exact finite-box decomposition -/

/-- The product of the two coordinatewise Fourier boxes used by the paired
divisor transform. -/
def selectedCFZPairedFourierBox
    {k : ℕ} (e : LinearFormsExponent k) (T : ℝ) :
    Set
      ((SelectedCFZFormIndex e → ℝ) ×
        (SelectedCFZFormIndex e → ℝ)) :=
  fourierProductBox T ×ˢ fourierProductBox T







end SmoothSieveCutoff

end Wikipedia.SzemeredisTheorem



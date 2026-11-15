-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryHarmonicLcmEulerBound
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryHarmonicLcmEulerBound
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:14:25.172745+00:00
-- url     : https://prove2.me/theorems/89b3f630-3be2-4ec5-a044-cb0979437f10
-- title:
--   Squarefree paired divisor families below a coordinatewise cutoff
-- statement:
--   For a finite index type $K$ and a natural cutoff $R$, the squarefree choice set consists of all families of divisor pairs $(d_q,e_q)_{q\in K}$ with each coordinate in $\{1,\ldots,R\}$ and with both $d_q$ and $e_q$ squarefree at every index. It is formed by filtering the finite coordinatewise choice set. This isolates the nonvanishing Möbius-support families used in the harmonic LCM Euler majorant.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/CFZCarryHarmonicLcmEulerBound.lean#L496-L503

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierTailBound
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
# A finite Euler majorant for the carry harmonic LCM mass

The divisor cutoff in `smoothDivisorFamilyChoices κ R` is imposed on every
individual divisor.  It therefore couples the prime choices and does not
give an exact Euler product.  This file uses only the honest one-sided
comparison: a squarefree paired divisor family is injected into the larger
space in which, independently for every prime `p ≤ R`, an arbitrary subset
of the `2 * card κ` divisor occurrences may contain `p`.

The empty subset has weight one.  Every nonempty subset has weight `p⁻¹`,
because `p` then occurs in the global LCM.  Summing over the unrestricted
assignment space gives the finite product

`∏ p ∈ Nat.primesLE R, (1 + (2 ^ (2 * card κ) - 1) / p)`.

Only the injection into that space is used; no false equality with the
coordinatewise-truncated divisor family is asserted.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped ArithmeticFunction.Moebius BigOperators

namespace SmoothSieveCutoff

/-! ## Prime-occurrence assignments -/













/-! ## The unrestricted assignment sum -/





/-! ## Encoding supported divisor families -/



















/-! ## Möbius mass as the squarefree indicator -/





/-- The squarefree part of the coordinatewise-truncated paired divisor
family. -/
noncomputable def squarefreeSmoothPairedDivisorChoices
    (κ : Type*) [Fintype κ] [DecidableEq κ]
    (R : ℕ) : Finset (κ → ℕ × ℕ) := by
  classical
  exact (smoothDivisorFamilyChoices κ R).filter
    SquarefreePairedDivisorChoice





/-! ## The harmonic LCM Euler majorant -/









/-! ## Selected and Selberg-scaled corollaries -/

















end SmoothSieveCutoff

end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.squarefreeSmoothPairedDivisorChoices.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"



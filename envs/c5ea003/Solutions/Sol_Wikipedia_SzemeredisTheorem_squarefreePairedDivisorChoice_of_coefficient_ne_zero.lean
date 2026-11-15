-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.squarefreePairedDivisorChoice_of_coefficient_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:45:56.031227+00:00
-- url     : https://prove2.me/submissions/af50a8a6-a290-4385-b3a4-e03ebe3b2ba0

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CongruenceAverage
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ExceptionalPrimes
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LinearFormsExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedDivisibilityCRT
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedLocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
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
import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Squarefree paired divisors and finite-family local factors

The Selberg expansion only receives a contribution from squarefree divisor
choices: a nonzero Möbius coefficient forces each of the two divisors attached
to every form to be squarefree.  Consequently all local least common multiples,
and their global least common multiple, are squarefree.  The canonical
prime-power CRT from `PairedDivisibilityCRT` therefore has exponent one at
every prime.

This file records that reduction exactly.  It also packages the local
intersection density of an arbitrary finite subfamily of affine forms.  The
empty, singleton, and two-element cases reduce to the exact APIs in
`LocalFactors`; the full avoidance factor is their finite
inclusion--exclusion sum.  Higher intersections require an additional
arithmetic input, so the final interface exposes that input as a hypothesis
rather than asserting an unavailable estimate.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## Squarefree divisor choices -/

open Wikipedia.SzemeredisTheorem in
/-- A nonzero coefficient in the Selberg divisor expansion has squarefree
support.  This is the precise way in which the Möbius factors eliminate
nonsquarefree divisor choices. -/
theorem solution
    {κ : Type*} [Fintype κ]
    (χ : ℝ → ℝ) (R : ℕ) (z : κ → ℕ × ℕ)
    (hz : smoothDivisorFamilyCoefficient χ R z ≠ 0) :
    SquarefreePairedDivisorChoice z := by
  intro q
  have hzq :
      smoothDivisorSummand χ R (z q).1 *
          smoothDivisorSummand χ R (z q).2 ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hz) q (Finset.mem_univ q)
  have hleftR :
      (ArithmeticFunction.moebius (z q).1 : ℝ) ≠ 0 := by
    intro hzero
    apply (mul_ne_zero_iff.mp hzq).1
    simp [smoothDivisorSummand, hzero]
  have hrightR :
      (ArithmeticFunction.moebius (z q).2 : ℝ) ≠ 0 := by
    intro hzero
    apply (mul_ne_zero_iff.mp hzq).2
    simp [smoothDivisorSummand, hzero]
  have hleft :
      ArithmeticFunction.moebius (z q).1 ≠ 0 := by
    exact_mod_cast hleftR
  have hright :
      ArithmeticFunction.moebius (z q).2 ≠ 0 := by
    exact_mod_cast hrightR
  exact
    ⟨ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hleft,
      ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hright⟩

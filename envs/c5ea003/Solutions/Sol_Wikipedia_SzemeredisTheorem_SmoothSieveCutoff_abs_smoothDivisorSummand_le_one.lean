-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.abs_smoothDivisorSummand_le_one
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:26:06.624796+00:00
-- url     : https://prove2.me/submissions/d232681f-3376-467b-8544-991003098aa8

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CongruenceAverage
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ExceptionalPrimes
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LinearFormsExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LocalFactors
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
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
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
# Uniform bounds for finite smooth-divisor expansions

The finite Selberg expansion contains two smooth Möbius-cutoff coefficients
for every form.  This file records the elementary bounds needed to propagate
a uniform arithmetic-density error through that expansion.

For a `SmoothSieveCutoff`, every cutoff value lies in `[0,1]` and the
Möbius function has absolute value at most one.  Hence each divisor summand
and each product-family coefficient has absolute value at most one.

The choice set is also counted exactly.  There are `R` positive choices in
`[1,R]`, two choices per form, and therefore

`card (smoothDivisorFamilyChoices κ R) = R ^ (2 * card κ)`.

The final theorems combine these facts with the triangle inequality.  A
uniform density perturbation of size `ε` changes the divisor sum by at most
`R ^ (2 * card κ) * ε`; a second theorem retains exactly the two scalar
prefactors occurring in the normalized Selberg expansion.
-/
open Wikipedia.SzemeredisTheorem
open scoped ArithmeticFunction.Moebius BigOperators
open Wikipedia.SzemeredisTheorem.SmoothSieveCutoff
/-! ## Coefficient bounds -/

open Wikipedia.SzemeredisTheorem.SmoothSieveCutoff in
/-- Every smooth Möbius-cutoff divisor summand has absolute value at most
one. -/
theorem solution
    (χ : SmoothSieveCutoff) (R d : ℕ) :
    |smoothDivisorSummand χ.toFun R d| ≤ 1 := by
  have hmu :
      |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have hchi :
      |χ.toFun (Real.log d / Real.log R)| ≤ 1 := by
    rw [abs_of_nonneg (χ.nonneg _)]
    exact χ.le_one _
  rw [smoothDivisorSummand, abs_mul]
  calc
    |(ArithmeticFunction.moebius d : ℝ)| *
          |χ.toFun (Real.log d / Real.log R)| ≤
        1 * 1 :=
      mul_le_mul hmu hchi (abs_nonneg _) (by norm_num)
    _ = 1 := one_mul 1

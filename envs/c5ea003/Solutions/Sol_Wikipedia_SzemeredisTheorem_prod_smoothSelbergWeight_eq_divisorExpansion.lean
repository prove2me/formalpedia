-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.prod_smoothSelbergWeight_eq_divisorExpansion
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:31:12.117735+00:00
-- url     : https://prove2.me/submissions/11b45d6a-659e-45ef-a8d3-f78c2eaf88df

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_smoothSelbergWeight_eq_pair_choice_sum

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Exact finite expansion of Selberg weights along linear forms

This file performs the algebraic expansion that precedes the analytic
Goldston--Yıldırım estimate.  For a finite family of positive
natural-valued forms, the mean of a product of smooth Selberg squares is
written exactly as a finite sum over two bounded divisor choices per form.
Each term splits into

* a product of smooth Möbius-cutoff coefficients; and
* the exact density of the simultaneous divisibility congruences.

The least common multiple of the chosen divisors is bounded by
`R ^ (2 * card κ)`, using `CongruenceAverage`.  The final section
specializes the identity to the full CFZ family evaluated through
`apLinearForm` and the natural W-tricked lift.

There are no asymptotic estimates here.  Factoring the composite-modulus
congruence density into prime local factors, controlling the exceptional
primes, and bounding the resulting Euler product remain separate analytic
steps.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## Bounded divisor choices and congruence densities -/
/-! ## One Selberg square -/
/-! ## A finite family of Selberg squares -/

open Wikipedia.SzemeredisTheorem in
/-- Pointwise product expansion for a finite family of positive
natural-valued forms. -/
theorem solution
    {κ X : Type*} [Fintype κ] [DecidableEq κ]
    (χ : ℝ → ℝ) {R : ℕ}
    (hR : 1 < R)
    (hχ : ∀ x : ℝ, 1 ≤ x → χ x = 0)
    (values : κ → X → ℕ)
    (hvalues : ∀ q x, 0 < values q x)
    (x : X) :
    (∏ q, smoothSelbergWeight χ R (values q x)) =
      (Real.log R ^ 2) ^ Fintype.card κ *
        ∑ z ∈ smoothDivisorFamilyChoices κ R,
          smoothDivisorFamilyCoefficient χ R z *
            pairedDivisibilityIndicator values z x := by
  calc
    (∏ q, smoothSelbergWeight χ R (values q x)) =
        ∏ q,
          (Real.log R ^ 2 *
            ∑ z ∈ smoothDivisorPairChoices R,
              (smoothDivisorSummand χ R z.1 *
                  smoothDivisorSummand χ R z.2) *
                (natDivisibilityIndicator z.1
                    (values q x) *
                  natDivisibilityIndicator z.2
                    (values q x))) := by
      apply Finset.prod_congr rfl
      intro q _hq
      exact smoothSelbergWeight_eq_pair_choice_sum
        χ hR hχ (hvalues q x)
    _ =
        (Real.log R ^ 2) ^ Fintype.card κ *
          ∏ q,
            ∑ z ∈ smoothDivisorPairChoices R,
              (smoothDivisorSummand χ R z.1 *
                  smoothDivisorSummand χ R z.2) *
                (natDivisibilityIndicator z.1
                    (values q x) *
                  natDivisibilityIndicator z.2
                    (values q x)) := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ]
    _ =
        (Real.log R ^ 2) ^ Fintype.card κ *
          ∑ z ∈ smoothDivisorFamilyChoices κ R,
            ∏ q,
              ((smoothDivisorSummand χ R (z q).1 *
                  smoothDivisorSummand χ R (z q).2) *
                (natDivisibilityIndicator (z q).1
                    (values q x) *
                  natDivisibilityIndicator (z q).2
                    (values q x))) := by
      unfold smoothDivisorFamilyChoices
      rw [Finset.prod_univ_sum]
    _ =
        (Real.log R ^ 2) ^ Fintype.card κ *
          ∑ z ∈ smoothDivisorFamilyChoices κ R,
            smoothDivisorFamilyCoefficient χ R z *
              pairedDivisibilityIndicator values z x := by
      apply congrArg
        (fun t : ℝ =>
          (Real.log R ^ 2) ^ Fintype.card κ * t)
      apply Finset.sum_congr rfl
      intro z _hz
      unfold smoothDivisorFamilyCoefficient
        pairedDivisibilityIndicator
      rw [← Finset.prod_mul_distrib]

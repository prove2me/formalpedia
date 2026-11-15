-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.mean_prod_smoothSelbergWeight_eq_divisorExpansion
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:41:56.319649+00:00
-- url     : https://prove2.me/submissions/54f85ecf-06cb-435a-82fc-57484e95d6e1

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_prod_smoothSelbergWeight_eq_divisorExpansion

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
/-- **Exact finite linear-forms expansion.**  Averaging the pointwise
identity separates every term into its smooth coefficient and its exact
simultaneous divisibility density. -/
theorem solution
    {κ X : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype X]
    (χ : ℝ → ℝ) {R : ℕ}
    (hR : 1 < R)
    (hχ : ∀ x : ℝ, 1 ≤ x → χ x = 0)
    (values : κ → X → ℕ)
    (hvalues : ∀ q x, 0 < values q x) :
    mean (fun x =>
        ∏ q, smoothSelbergWeight χ R (values q x)) =
      (Real.log R ^ 2) ^ Fintype.card κ *
        ∑ z ∈ smoothDivisorFamilyChoices κ R,
          smoothDivisorFamilyCoefficient χ R z *
            pairedDivisibilityDensity values z := by
  rw [show
      (fun x =>
        ∏ q, smoothSelbergWeight χ R (values q x)) =
      fun x =>
        (Real.log R ^ 2) ^ Fintype.card κ *
          ∑ z ∈ smoothDivisorFamilyChoices κ R,
            smoothDivisorFamilyCoefficient χ R z *
              pairedDivisibilityIndicator values z x by
    funext x
    exact prod_smoothSelbergWeight_eq_divisorExpansion
      χ hR hχ values hvalues x]
  rw [mean_smul]
  have hmean :
      mean (fun x =>
          ∑ z ∈ smoothDivisorFamilyChoices κ R,
            smoothDivisorFamilyCoefficient χ R z *
              pairedDivisibilityIndicator values z x) =
        ∑ z ∈ smoothDivisorFamilyChoices κ R,
          mean (fun x =>
            smoothDivisorFamilyCoefficient χ R z *
              pairedDivisibilityIndicator values z x) := by
    simpa [mean] using
      (Finset.expect_sum_comm
        (Finset.univ : Finset X)
        (smoothDivisorFamilyChoices κ R)
        (fun x z =>
          smoothDivisorFamilyCoefficient χ R z *
            pairedDivisibilityIndicator values z x))
  rw [hmean]
  apply congrArg
    (fun t : ℝ =>
      (Real.log R ^ 2) ^ Fintype.card κ * t)
  apply Finset.sum_congr rfl
  intro z _hz
  rw [mean_smul]
  rfl

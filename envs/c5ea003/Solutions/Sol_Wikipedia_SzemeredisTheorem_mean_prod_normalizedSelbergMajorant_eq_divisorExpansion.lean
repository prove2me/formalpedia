-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.mean_prod_normalizedSelbergMajorant_eq_divisorExpansion
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:43:16.322572+00:00
-- url     : https://prove2.me/submissions/0bddbdb6-3d69-4c30-ae68-a9192497c12a

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_mean_prod_smoothSelbergWeight_eq_divisorExpansion

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section





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

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Bounded divisor choices and congruence densities -/





















/-! ## One Selberg square -/







/-! ## A finite family of Selberg squares -/





/-! ## Normalized Selberg majorants -/



theorem normalizedSelbergMajorant_eq_scale_mul
    (χ : ℝ → ℝ) (cχ : ℝ) (R W n : ℕ) :
    normalizedSelbergMajorant χ cχ R W n =
      normalizedSelbergScale cχ R W *
        smoothSelbergWeight χ R n := by
  unfold normalizedSelbergMajorant
    normalizedSelbergScale
  ring



/-! ## CFZ specialization -/









end Wikipedia.SzemeredisTheorem

end
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
/-! ## Normalized Selberg majorants -/

open Wikipedia.SzemeredisTheorem in
/-- Exact expansion for a product of normalized Selberg majorants. -/
theorem solution
    {κ X : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype X]
    (χ : ℝ → ℝ) (cχ : ℝ) {R W : ℕ}
    (hR : 1 < R)
    (hχ : ∀ x : ℝ, 1 ≤ x → χ x = 0)
    (values : κ → X → ℕ)
    (hvalues : ∀ q x, 0 < values q x) :
    mean (fun x =>
        ∏ q,
          normalizedSelbergMajorant
            χ cχ R W (values q x)) =
      normalizedSelbergScale cχ R W ^
          Fintype.card κ *
        ((Real.log R ^ 2) ^ Fintype.card κ *
          ∑ z ∈ smoothDivisorFamilyChoices κ R,
            smoothDivisorFamilyCoefficient χ R z *
              pairedDivisibilityDensity values z) := by
  rw [show
      (fun x =>
        ∏ q,
          normalizedSelbergMajorant
            χ cχ R W (values q x)) =
      fun x =>
        normalizedSelbergScale cχ R W ^
            Fintype.card κ *
          ∏ q, smoothSelbergWeight χ R (values q x) by
    funext x
    simp_rw [normalizedSelbergMajorant_eq_scale_mul]
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_univ]]
  rw [mean_smul,
    mean_prod_smoothSelbergWeight_eq_divisorExpansion
      χ hR hχ values hvalues]

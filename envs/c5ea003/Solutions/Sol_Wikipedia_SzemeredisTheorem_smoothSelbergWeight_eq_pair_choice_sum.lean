-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.smoothSelbergWeight_eq_pair_choice_sum
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:30:19.232529+00:00
-- url     : https://prove2.me/submissions/7ed07a43-156c-4e2d-9f95-27303235bad2

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

section






/-!
# Smooth truncated divisor sums

The Goldston--Yıldırım majorant is the square of a smoothly truncated
Möbius divisor sum.  This file fixes the normalization and proves the exact
prime-value identity used for pointwise domination of the W-tricked prime
weight.  The later linear-forms estimate is deliberately separated from
these elementary identities.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped ArithmeticFunction.Moebius BigOperators





/-- The truncated divisor sum written using its named summand. -/
theorem smoothTruncatedDivisorSum_eq_sum_smoothDivisorSummand
    (χ : ℝ → ℝ) (R n : ℕ) :
    smoothTruncatedDivisorSum χ R n =
      Real.log R *
        ∑ d ∈ n.divisors, smoothDivisorSummand χ R d :=
  rfl





/-- A cutoff supported below one vanishes at `log p / log R` whenever
`R < p`. -/
theorem smoothCutoff_zero_of_lt
    (χ : ℝ → ℝ) {R p : ℕ}
    (hR : 1 < R) (hRp : R < p)
    (hχ : ∀ x : ℝ, 1 ≤ x → χ x = 0) :
    χ (Real.log p / Real.log R) = 0 := by
  have hlogR : 0 < Real.log (R : ℝ) :=
    Real.log_pos (by exact_mod_cast hR)
  apply hχ
  rw [le_div_iff₀ hlogR]
  simpa using
    (Real.log_lt_log
      (by exact_mod_cast (Nat.zero_lt_of_lt hR))
      (by exact_mod_cast hRp)).le

/-- A divisor summand past the cutoff `R` vanishes. -/
@[simp]
theorem smoothDivisorSummand_eq_zero_of_lt
    (χ : ℝ → ℝ) {R d : ℕ}
    (hR : 1 < R) (hRd : R < d)
    (hχ : ∀ x : ℝ, 1 ≤ x → χ x = 0) :
    smoothDivisorSummand χ R d = 0 := by
  rw [smoothDivisorSummand,
    smoothCutoff_zero_of_lt χ hR hRd hχ, mul_zero]

/-- Exact support restriction: under the standard support hypothesis on
`χ`, only divisors at most `R` contribute to the truncated divisor sum. -/
theorem smoothTruncatedDivisorSum_eq_filtered_divisors
    (χ : ℝ → ℝ) {R : ℕ}
    (hR : 1 < R)
    (hχ : ∀ x : ℝ, 1 ≤ x → χ x = 0)
    (n : ℕ) :
    smoothTruncatedDivisorSum χ R n =
      Real.log R *
        ∑ d ∈ n.divisors.filter (fun d ↦ d ≤ R),
          smoothDivisorSummand χ R d := by
  rw [smoothTruncatedDivisorSum_eq_sum_smoothDivisorSummand]
  apply congrArg (fun t : ℝ ↦ Real.log R * t)
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro d hd hnot
  apply smoothDivisorSummand_eq_zero_of_lt χ hR
  · exact lt_of_not_ge fun hdR ↦
      hnot (Finset.mem_filter.mpr ⟨hd, hdR⟩)
  · exact hχ





















end Wikipedia.SzemeredisTheorem

end

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

/-- For a positive integer, filtered divisors up to `R` are exactly the
positive choices up to `R` which divide that integer. -/
theorem filtered_divisors_eq_smoothDivisorChoices
    {R n : ℕ} (hn : 0 < n) :
    n.divisors.filter (fun d => d ≤ R) =
      (smoothDivisorChoices R).filter
        (fun d => d ∣ n) := by
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors,
    smoothDivisorChoices, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hdvd, _hn0⟩, hdR⟩
    exact
      ⟨⟨Nat.pos_of_dvd_of_pos hdvd hn, hdR⟩, hdvd⟩
  · rintro ⟨⟨_hdpos, hdR⟩, hdvd⟩
    exact ⟨⟨hdvd, hn.ne'⟩, hdR⟩

/-- A support-filtered divisor sum reindexed over the fixed interval
`[1,R]`, with divisibility recorded by a zero--one factor. -/
theorem smoothTruncatedDivisorSum_eq_choice_sum
    (χ : ℝ → ℝ) {R n : ℕ}
    (hR : 1 < R)
    (hχ : ∀ x : ℝ, 1 ≤ x → χ x = 0)
    (hn : 0 < n) :
    smoothTruncatedDivisorSum χ R n =
      Real.log R *
        ∑ d ∈ smoothDivisorChoices R,
          smoothDivisorSummand χ R d *
            natDivisibilityIndicator d n := by
  rw [smoothTruncatedDivisorSum_eq_filtered_divisors
    χ hR hχ n]
  rw [filtered_divisors_eq_smoothDivisorChoices hn]
  apply congrArg (fun t : ℝ => Real.log R * t)
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _hd
  by_cases hdn : d ∣ n <;>
    simp [natDivisibilityIndicator, hdn]



/-! ## A finite family of Selberg squares -/





/-! ## Normalized Selberg majorants -/







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

open Wikipedia.SzemeredisTheorem in
/-- Exact bounded paired-divisor expansion of one smooth Selberg square. -/
theorem solution
    (χ : ℝ → ℝ) {R n : ℕ}
    (hR : 1 < R)
    (hχ : ∀ x : ℝ, 1 ≤ x → χ x = 0)
    (hn : 0 < n) :
    smoothSelbergWeight χ R n =
      Real.log R ^ 2 *
        ∑ z ∈ smoothDivisorPairChoices R,
          (smoothDivisorSummand χ R z.1 *
              smoothDivisorSummand χ R z.2) *
            (natDivisibilityIndicator z.1 n *
              natDivisibilityIndicator z.2 n) := by
  rw [smoothSelbergWeight,
    smoothTruncatedDivisorSum_eq_choice_sum
      χ hR hχ hn]
  calc
    (Real.log R *
        ∑ d ∈ smoothDivisorChoices R,
          smoothDivisorSummand χ R d *
            natDivisibilityIndicator d n) ^ 2 =
        Real.log R ^ 2 *
          ((∑ d ∈ smoothDivisorChoices R,
              smoothDivisorSummand χ R d *
                natDivisibilityIndicator d n) *
            ∑ e ∈ smoothDivisorChoices R,
              smoothDivisorSummand χ R e *
                natDivisibilityIndicator e n) := by
      ring
    _ =
        Real.log R ^ 2 *
          ∑ d ∈ smoothDivisorChoices R,
            ∑ e ∈ smoothDivisorChoices R,
              (smoothDivisorSummand χ R d *
                  natDivisibilityIndicator d n) *
                (smoothDivisorSummand χ R e *
                  natDivisibilityIndicator e n) := by
      rw [Finset.sum_mul_sum]
    _ =
        Real.log R ^ 2 *
          ∑ d ∈ smoothDivisorChoices R,
            ∑ e ∈ smoothDivisorChoices R,
              (smoothDivisorSummand χ R d *
                  smoothDivisorSummand χ R e) *
                (natDivisibilityIndicator d n *
                  natDivisibilityIndicator e n) := by
      apply congrArg (fun t : ℝ => Real.log R ^ 2 * t)
      apply Finset.sum_congr rfl
      intro d _hd
      apply Finset.sum_congr rfl
      intro e _he
      ring
    _ =
        Real.log R ^ 2 *
          ∑ z ∈ smoothDivisorPairChoices R,
            (smoothDivisorSummand χ R z.1 *
                smoothDivisorSummand χ R z.2) *
              (natDivisibilityIndicator z.1 n *
                natDivisibilityIndicator z.2 n) := by
      unfold smoothDivisorPairChoices
      apply congrArg (fun t : ℝ => Real.log R ^ 2 * t)
      exact
        (Finset.sum_product
          (s := smoothDivisorChoices R)
          (t := smoothDivisorChoices R)
          (f := fun z : ℕ × ℕ =>
            (smoothDivisorSummand χ R z.1 *
                smoothDivisorSummand χ R z.2) *
              (natDivisibilityIndicator z.1 n *
                natDivisibilityIndicator z.2 n))).symm

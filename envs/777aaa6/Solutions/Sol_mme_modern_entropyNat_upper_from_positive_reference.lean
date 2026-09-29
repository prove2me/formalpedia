-- Prove2me | solution 1 for mme_modern_entropyNat_upper_from_positive_reference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T03:47:29.539557+00:00
-- url     : https://prove2.me/submissions/1532e828-f9d4-45b1-bd58-3037cd78c18d

import Definitions.Def_mme_modern_entropy_data
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open BigOperators

universe u v w x

set_option autoImplicit false
set_option warningAsError true

private theorem negMulLog_le_cross_tangent {r y : ℝ} (hr : 0 ≤ r) (hy : 0 < y) :
    Real.negMulLog r ≤ -r * Real.log y + y - r := by
  rcases hr.eq_or_lt with rfl | hr
  · simp only [Real.negMulLog_zero, neg_zero, zero_mul, zero_add, sub_zero]
    exact hy.le
  · have hlog := Real.log_le_sub_one_of_pos (div_pos hy hr)
    have hmul := mul_le_mul_of_nonneg_left hlog hr.le
    rw [Real.log_div hy.ne' hr.ne'] at hmul
    rw [Real.negMulLog]
    field_simp at hmul
    nlinarith

private theorem additive_expectation_eq
    {D : Type u} {I : Type v} [Fintype D] [Fintype I] [DecidableEq I]
    (coord : D → I) (rho alpha : D → ℝ) (potential : I → ℝ)
    (hmarg : ∀ i, mme_modern_marginal coord rho i =
      mme_modern_marginal coord alpha i) :
    (∑ a, rho a * potential (coord a)) = ∑ a, alpha a * potential (coord a) := by
  rw [← Fintype.sum_fiberwise coord (fun a ↦ rho a * potential (coord a)),
      ← Fintype.sum_fiberwise coord (fun a ↦ alpha a * potential (coord a))]
  apply Finset.sum_congr rfl
  intro i _hi
  simp_rw [show ∀ a : {a // coord a = i}, coord a = i from fun a ↦ a.property]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  change mme_modern_marginal coord rho i * potential i =
    mme_modern_marginal coord alpha i * potential i
  rw [hmarg i]

/-- A positive reference distribution need not have the target marginals. -/
theorem solution
    {D : Type u} {X : Type v} {Y : Type w} {Z : Type x}
    [Fintype D] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (coordX : D → X) (coordY : D → Y) (coordZ : D → Z)
    (rho alpha y : D → ℝ) (lambdaZero : ℝ)
    (lambdaX : X → ℝ) (lambdaY : Y → ℝ) (lambdaZ : Z → ℝ)
    (epsilon : ℝ)
    (hrho : ∀ a, 0 ≤ rho a) (hy : ∀ a, 0 < y a)
    (hrhoSum : ∑ a, rho a = 1) (halphaSum : ∑ a, alpha a = 1)
    (hySum : ∑ a, y a = 1)
    (hmargX : ∀ i, mme_modern_marginal coordX rho i =
      mme_modern_marginal coordX alpha i)
    (hmargY : ∀ i, mme_modern_marginal coordY rho i =
      mme_modern_marginal coordY alpha i)
    (hmargZ : ∀ i, mme_modern_marginal coordZ rho i =
      mme_modern_marginal coordZ alpha i)
    (hlogLower : ∀ a,
      lambdaZero + lambdaX (coordX a) + lambdaY (coordY a) +
        lambdaZ (coordZ a) - epsilon ≤ Real.log (y a)) :
    (∑ a, Real.negMulLog (rho a)) ≤
      -(∑ a, alpha a * (lambdaZero + lambdaX (coordX a) +
        lambdaY (coordY a) + lambdaZ (coordZ a))) + epsilon := by
  let g : D → ℝ := fun a ↦ lambdaZero + lambdaX (coordX a) +
    lambdaY (coordY a) + lambdaZ (coordZ a)
  have hg : (∑ a, rho a * g a) = ∑ a, alpha a * g a := by
    have hx := additive_expectation_eq coordX rho alpha lambdaX hmargX
    have hy' := additive_expectation_eq coordY rho alpha lambdaY hmargY
    have hz := additive_expectation_eq coordZ rho alpha lambdaZ hmargZ
    dsimp [g]
    simp_rw [mul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, ← Finset.sum_mul, hrhoSum, halphaSum, hx, hy', hz]
  have hcross : (∑ a, Real.negMulLog (rho a)) ≤
      -(∑ a, rho a * Real.log (y a)) := by
    calc
      _ ≤ ∑ a, (-rho a * Real.log (y a) + y a - rho a) :=
        Finset.sum_le_sum fun a _ha ↦ negMulLog_le_cross_tangent (hrho a) (hy a)
      _ = -(∑ a, rho a * Real.log (y a)) := by
        simp_rw [neg_mul]
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib,
          hySum, hrhoSum]
        ring
  have hbound : (∑ a, rho a * g a) - epsilon ≤
      ∑ a, rho a * Real.log (y a) := by
    calc
      _ = ∑ a, rho a * (g a - epsilon) := by
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hrhoSum, one_mul]
      _ ≤ ∑ a, rho a * Real.log (y a) :=
        Finset.sum_le_sum fun a _ha ↦ mul_le_mul_of_nonneg_left (hlogLower a) (hrho a)
  change (∑ a, Real.negMulLog (rho a)) ≤ -(∑ a, alpha a * g a) + epsilon
  rw [hg] at hbound
  linarith

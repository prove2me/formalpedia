-- Prove2me | solution 1 for MarkovMixing.ising_tanh_lemma
-- status  : ACCEPTED   (prove)
-- author  : @chenmin
-- created : 2026-08-22T17:52:26.311384+00:00
-- url     : https://prove2.me/submissions/e60f6c23-e39d-4d45-8728-cce674571379

import Definitions.Def_mm_ising
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

set_option maxHeartbeats 800000

theorem solution (β : ℝ) (hβ : 0 < β) :
    (∀ x : ℝ, Real.tanh (β * (-x + 1)) - Real.tanh (β * (-x - 1)) =
      Real.tanh (β * (x + 1)) - Real.tanh (β * (x - 1))) ∧
    (∀ x y : ℝ, 0 ≤ x → x ≤ y →
      Real.tanh (β * (y + 1)) - Real.tanh (β * (y - 1)) ≤
        Real.tanh (β * (x + 1)) - Real.tanh (β * (x - 1))) ∧
    (∀ x : ℝ, Real.tanh (β * (x + 1)) - Real.tanh (β * (x - 1)) ≤
      2 * Real.tanh β) ∧
    ∀ k : ℤ, Odd k →
      Real.tanh (β * (k + 1)) - Real.tanh (β * (k - 1)) ≤
        Real.tanh (2 * β) := by
  have hs : 0 < Real.sinh (2 * β) := Real.sinh_pos_iff.mpr (by linarith)
  have hkey : ∀ x : ℝ, Real.tanh (β * (x + 1)) - Real.tanh (β * (x - 1))
      = 2 * Real.sinh (2 * β) / (Real.cosh (2 * β * x) + Real.cosh (2 * β)) := by
    intro x
    have hc1 : Real.cosh (β * (x + 1)) ≠ 0 := (Real.cosh_pos _).ne'
    have hc2 : Real.cosh (β * (x - 1)) ≠ 0 := (Real.cosh_pos _).ne'
    have e1 : β * (x + 1) + β * (x - 1) = 2 * β * x := by ring
    have e2 : β * (x + 1) - β * (x - 1) = 2 * β := by ring
    have hadd := Real.cosh_add (β * (x + 1)) (β * (x - 1))
    have hsub := Real.cosh_sub (β * (x + 1)) (β * (x - 1))
    rw [e1] at hadd
    rw [e2] at hsub
    have hden : Real.cosh (2 * β * x) + Real.cosh (2 * β)
        = 2 * (Real.cosh (β * (x + 1)) * Real.cosh (β * (x - 1))) := by
      rw [hadd, hsub]; ring
    have hsinh := Real.sinh_sub (β * (x + 1)) (β * (x - 1))
    rw [e2] at hsinh
    rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh, div_sub_div _ _ hc1 hc2,
      ← hsinh, hden]
    field_simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    have h1 : β * (-x + 1) = -(β * (x - 1)) := by ring
    have h2 : β * (-x - 1) = -(β * (x + 1)) := by ring
    rw [h1, h2, Real.tanh_neg, Real.tanh_neg]
    ring
  · intro x y hx hxy
    rw [hkey x, hkey y]
    have hcmp : Real.cosh (2 * β * x) ≤ Real.cosh (2 * β * y) := by
      rw [Real.cosh_le_cosh, abs_of_nonneg (by positivity), abs_of_nonneg (by nlinarith)]
      nlinarith
    have hcx : 0 < Real.cosh (2 * β * x) + Real.cosh (2 * β) := by positivity
    gcongr
  · intro x
    rw [hkey x]
    have h1 : 2 * Real.tanh β = 2 * Real.sinh (2 * β) / (1 + Real.cosh (2 * β)) := by
      rw [Real.sinh_two_mul, Real.cosh_two_mul, Real.tanh_eq_sinh_div_cosh]
      have hc : Real.cosh β ≠ 0 := (Real.cosh_pos _).ne'
      field_simp
      linarith [Real.cosh_sq_sub_sinh_sq β]
    rw [h1]
    have h2 : (1 : ℝ) ≤ Real.cosh (2 * β * x) := Real.one_le_cosh _
    have h3 : (0 : ℝ) < 1 + Real.cosh (2 * β) := by positivity
    gcongr
  · intro k hk
    rw [hkey (k : ℝ)]
    have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      have hk0 : k ≠ 0 := by
        rintro rfl
        have := Int.odd_iff.mp hk
        omega
      have : (1 : ℤ) ≤ |k| := Int.one_le_abs (by omega)
      calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
        _ ≤ ((|k| : ℤ) : ℝ) := by exact_mod_cast this
        _ = |(k : ℝ)| := by push_cast [Int.cast_abs]; rfl
    have hcmp : Real.cosh (2 * β) ≤ Real.cosh (2 * β * (k : ℝ)) := by
      rw [Real.cosh_le_cosh, abs_of_nonneg (by positivity), abs_mul,
        abs_of_nonneg (by positivity)]
      nlinarith
    have h4 : Real.tanh (2 * β) = Real.sinh (2 * β) / Real.cosh (2 * β) :=
      Real.tanh_eq_sinh_div_cosh _
    rw [h4, div_le_div_iff₀ (by positivity) (Real.cosh_pos _)]
    nlinarith [Real.cosh_pos (2 * β), hs]

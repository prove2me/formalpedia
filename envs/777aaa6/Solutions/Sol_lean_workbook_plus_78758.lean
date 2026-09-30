-- Prove2me | solution 1 for lean_workbook_plus_78758
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:09:22.283495+00:00
-- url     : https://prove2.me/submissions/0e3182d1-5fce-429a-8a84-5b4d957db82c

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

theorem shifted_recurrence_four_step (c : ℝ) (f : ℝ → ℝ)
    (hf : ∀ x, f (x + 1) + f (x - 1) = c * f x) (x : ℝ) :
    f (x + 4) + f x = (c ^ 2 - 2) * f (x + 2) := by
  have hstep (y : ℝ) : f (y + 2) + f y = c * f (y + 1) := by
    simpa only [show y + 1 + 1 = y + 2 by ring,
      show y + 1 - 1 = y by ring] using hf (y + 1)
  have h0 := hstep x
  have h1 : f (x + 3) + f (x + 1) = c * f (x + 2) := by
    simpa only [show x + 1 + 2 = x + 3 by ring,
      show x + 1 + 1 = x + 2 by ring] using hstep (x + 1)
  have h2 : f (x + 4) + f (x + 2) = c * f (x + 3) := by
    simpa only [show x + 2 + 2 = x + 4 by ring,
      show x + 2 + 1 = x + 3 by ring] using hstep (x + 2)
  linear_combination h0 + c * h1 + h2

theorem shifted_recurrence_six_step (c : ℝ) (f : ℝ → ℝ)
    (hf : ∀ x, f (x + 1) + f (x - 1) = c * f x) (x : ℝ) :
    f (x + 6) + (c ^ 2 - 2) * f x =
      ((c ^ 2 - 2) ^ 2 - 1) * f (x + 2) := by
  have h0 := shifted_recurrence_four_step c f hf x
  have h2 : f (x + 6) + f (x + 2) = (c ^ 2 - 2) * f (x + 4) := by
    simpa only [show x + 2 + 4 = x + 6 by ring,
      show x + 2 + 2 = x + 4 by ring] using
      shifted_recurrence_four_step c f hf (x + 2)
  linear_combination (c ^ 2 - 2) * h0 + h2

theorem periodic_of_shift_antiperiodic (f : ℝ → ℝ) (T : ℝ)
    (h : ∀ x, f (x + T) = -f x) : ∀ x, f (x + 2 * T) = f x := by
  intro x
  rw [show x + 2 * T = (x + T) + T by ring, h, h, neg_neg]

theorem small_sqrt_shift_recurrence_periodic (n : ℕ) (hn : n < 4)
    (f : ℝ → ℝ)
    (hf : ∀ x, f (x + 1) + f (x - 1) = Real.sqrt n * f x) :
    ∃ T > 0, ∀ x, f (x + T) = f x := by
  have hs : (Real.sqrt (n : ℝ)) ^ 2 = n := Real.sq_sqrt (by positivity)
  have h4 (x : ℝ) : f (x + 4) + f x = ((n : ℝ) - 2) * f (x + 2) := by
    simpa only [hs] using shifted_recurrence_four_step (Real.sqrt n) f hf x
  have h6 (x : ℝ) : f (x + 6) + ((n : ℝ) - 2) * f x =
      (((n : ℝ) - 2) ^ 2 - 1) * f (x + 2) := by
    simpa only [hs] using shifted_recurrence_six_step (Real.sqrt n) f hf x
  interval_cases n
  · have ha (x : ℝ) : f (x + 2) = -f x := by
      have h := hf (x + 1)
      rw [show x + 1 + 1 = x + 2 by ring,
        show x + 1 - 1 = x by ring] at h
      norm_num at h
      linarith
    exact ⟨4, by norm_num, by
      simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using
        periodic_of_shift_antiperiodic f 2 ha⟩
  · refine ⟨6, by norm_num, ?_⟩
    intro x
    have h := h6 x
    norm_num at h
    change f (x + 6) + -f x = (0 : ℝ) * f (x + 2) at h
    simp only [zero_mul] at h
    linarith
  · have ha (x : ℝ) : f (x + 4) = -f x := by
      have h := h4 x
      norm_num at h
      change f (x + 4) + f x = (0 : ℝ) * f (x + 2) at h
      simp only [zero_mul] at h
      linarith
    exact ⟨8, by norm_num, by
      simpa only [show (2 : ℝ) * 4 = 8 by norm_num] using
        periodic_of_shift_antiperiodic f 4 ha⟩
  · have ha (x : ℝ) : f (x + 6) = -f x := by
      have h := h6 x
      norm_num at h
      change f (x + 6) + (1 : ℝ) * f x = (0 : ℝ) * f (x + 2) at h
      simp only [zero_mul, one_mul] at h
      linarith
    exact ⟨12, by norm_num, by
      simpa only [show (2 : ℝ) * 6 = 12 by norm_num] using
        periodic_of_shift_antiperiodic f 6 ha⟩

theorem exponential_shift_recurrence (c r : ℝ) (hr : 1 < r)
    (hroot : r + 1 / r = c) :
    (∀ x, Real.exp ((x + 1) * Real.log r) + Real.exp ((x - 1) * Real.log r) =
      c * Real.exp (x * Real.log r)) ∧
    ¬ (∃ T > 0, ∀ x, Real.exp ((x + T) * Real.log r) =
      Real.exp (x * Real.log r)) := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  constructor
  · intro x
    rw [show (x + 1) * Real.log r = x * Real.log r + Real.log r by ring,
      show (x - 1) * Real.log r = x * Real.log r - Real.log r by ring,
      Real.exp_add, Real.exp_sub, Real.exp_log hr0]
    calc
      Real.exp (x * Real.log r) * r + Real.exp (x * Real.log r) / r =
          (r + 1 / r) * Real.exp (x * Real.log r) := by ring
      _ = c * Real.exp (x * Real.log r) := by rw [hroot]
  · rintro ⟨T, hT, hp⟩
    have he := Real.exp_injective (hp 0)
    have hlog : 0 < Real.log r := Real.log_pos hr
    simp only [zero_add, zero_mul] at he
    nlinarith [mul_pos hT hlog]

theorem large_sqrt_shift_nonperiodic (n : ℕ) (hn : 4 < n) :
    ∃ f : ℝ → ℝ,
      (∀ x, f (x + 1) + f (x - 1) = Real.sqrt n * f x) ∧
      ¬ (∃ T > 0, ∀ x, f (x + T) = f x) := by
  have hnR : (4 : ℝ) < n := by exact_mod_cast hn
  have hc := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
  have hc0 := Real.sqrt_nonneg (n : ℝ)
  have hc2 : 2 < Real.sqrt (n : ℝ) := by nlinarith
  have hd := Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) - 4 by linarith)
  have hd0 := Real.sqrt_nonneg ((n : ℝ) - 4)
  let r := (Real.sqrt (n : ℝ) + Real.sqrt ((n : ℝ) - 4)) / 2
  have hr : 1 < r := by dsimp [r]; linarith
  have hr0 : r ≠ 0 := ne_of_gt (lt_trans zero_lt_one hr)
  have hpoly : r ^ 2 - Real.sqrt (n : ℝ) * r + 1 = 0 := by
    dsimp [r]
    nlinarith
  have hroot : r + 1 / r = Real.sqrt n := by
    field_simp
    nlinarith [hpoly]
  exact ⟨fun x => Real.exp (x * Real.log r), exponential_shift_recurrence _ _ hr hroot⟩

theorem nonperiodic_sqrt_shift_classification (n : ℕ) :
    (∃ f : ℝ → ℝ,
      (∀ x, f (x + 1) + f (x - 1) = Real.sqrt n * f x) ∧
      ¬ (∃ T > 0, ∀ x, f (x + T) = f x)) ↔ 4 ≤ n := by
  constructor
  · rintro ⟨f, hf, hnp⟩
    by_contra hn
    exact hnp (small_sqrt_shift_recurrence_periodic n (by omega) f hf)
  · intro hn
    rcases eq_or_lt_of_le hn with h4 | h4
    · subst n
      refine ⟨fun x => x, ?_, ?_⟩
      · intro x
        norm_num
        ring
      · rintro ⟨T, hT, hp⟩
        have he := hp 0
        norm_num at he
        linarith
    · exact large_sqrt_shift_nonperiodic n h4

theorem solution (n : ℕ) (hn : 0 < n) : ∃ f : ℝ → ℝ,
    ¬ ∃ T > 0, ∀ x, f (x + T) = f x ∧
      ∀ x, f (x + 1) + f (x - 1) = Real.sqrt n * f x := by
  refine ⟨fun x => x, ?_⟩
  rintro ⟨T, hT, hp⟩
  have he := (hp 0).1
  norm_num at he
  linarith

#print axioms solution
#print axioms shifted_recurrence_four_step
#print axioms shifted_recurrence_six_step
#print axioms small_sqrt_shift_recurrence_periodic
#print axioms exponential_shift_recurrence
#print axioms large_sqrt_shift_nonperiodic
#print axioms nonperiodic_sqrt_shift_classification

-- Prove2me | solution 1 for lean_workbook_plus_22862
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T19:28:24.447733+00:00
-- url     : https://prove2.me/submissions/3e7a92fb-a069-45c8-aa45-ccd9ce84bf43

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter Topology

namespace RadicalIntegerPair

def pair (k : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | n + 1 => ((2 * k + 1) * (pair k n).1 + k + 2 * (pair k n).2,
      2 * k * (k + 1) * (pair k n).1 + k * (k + 1) + (2 * k + 1) * (pair k n).2)

def value (k n : ℕ) : ℕ := (pair k n).1
def rootValue (k n : ℕ) : ℕ := (pair k n).2

theorem value_zero (k : ℕ) : value k 0 = 0 := rfl
theorem rootValue_zero (k : ℕ) : rootValue k 0 = 0 := rfl

theorem value_succ (k n : ℕ) :
    value k (n + 1) = (2 * k + 1) * value k n + k + 2 * rootValue k n := rfl

theorem rootValue_succ (k n : ℕ) : rootValue k (n + 1) =
    2 * k * (k + 1) * value k n + k * (k + 1) + (2 * k + 1) * rootValue k n := rfl

theorem invariant (k n : ℕ) : (rootValue k n) ^ 2 = k * (k + 1) * value k n * (value k n + 1) := by
  induction n with
  | zero => simp only [value_zero, rootValue_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul]
  | succ n ih =>
    rw [value_succ, rootValue_succ]
    nlinarith only [ih]

theorem linear_recurrence (k n : ℕ) :
    value k (n + 2) + value k n = (4 * k + 2) * value k (n + 1) + 2 * k := by
  rw [show n + 2 = (n + 1) + 1 from rfl, value_succ, rootValue_succ, value_succ]
  ring

theorem increment_lower (k n : ℕ) : value k n + k ≤ value k (n + 1) := by
  rw [value_succ]
  nlinarith

theorem linear_lower (k n : ℕ) : k * n ≤ value k n := by
  induction n with
  | zero => simp only [mul_zero, value_zero, le_refl]
  | succ n ih =>
    have h := increment_lower k n
    rw [Nat.mul_succ]
    omega

theorem positive {k n : ℕ} (hk : 0 < k) (hn : 0 < n) : 0 < value k n :=
  lt_of_lt_of_le (Nat.mul_pos hk hn) (linear_lower k n)

theorem strict_increase {k : ℕ} (hk : 0 < k) (n : ℕ) : value k n < value k (n + 1) := by
  have h := increment_lower k n
  omega

theorem radical_certificate (k n : ℕ) :
    Real.sqrt ((k : ℝ) * (k + 1) * (value k n : ℝ) * (value k n + 1)) = rootValue k n := by
  have h : (rootValue k n : ℝ) ^ 2 = (k : ℝ) * (k + 1) * (value k n : ℝ) * (value k n + 1) := by
    exact_mod_cast invariant k n
  rw [← h, Real.sqrt_sq_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]

noncomputable def step (k : ℕ) (x : ℝ) : ℝ :=
  (x + 1) * k + (k + 1) * x + 2 * Real.sqrt ((k : ℝ) * (k + 1) * x * (x + 1))

theorem real_recurrence (k n : ℕ) : (value k (n + 1) : ℝ) = step k (value k n) := by
  unfold step
  rw [radical_certificate, value_succ]
  push_cast
  ring

theorem uniqueness (k : ℕ) (a : ℕ → ℝ) (h0 : a 0 = 0)
    (ha : ∀ n, a (n + 1) = step k (a n)) (n : ℕ) : a n = (value k n : ℝ) := by
  induction n with
  | zero => simpa only [value_zero, Nat.cast_zero] using h0
  | succ n ih => rw [ha, real_recurrence, ih]

theorem exists_unique_sequence (k : ℕ) : ∃! a : ℕ → ℝ,
    a 0 = 0 ∧ ∀ n, a (n + 1) = step k (a n) := by
  refine ⟨fun n => (value k n : ℝ), ⟨?_, real_recurrence k⟩, ?_⟩
  · simp only [value_zero, Nat.cast_zero]
  · rintro a ⟨h0, ha⟩
    funext n
    exact uniqueness k a h0 ha n

theorem source_integral (k : ℕ) (a : ℕ → ℝ) (h0 : a 0 = 0)
    (ha : ∀ n, a (n + 1) = step k (a n)) (n : ℕ) : ∃ m : ℕ, a n = (m : ℝ) :=
  ⟨value k n, uniqueness k a h0 ha n⟩

theorem source_positive {k : ℕ} (hk : 0 < k) (a : ℕ → ℝ) (h0 : a 0 = 0)
    (ha : ∀ n, a (n + 1) = step k (a n)) {n : ℕ} (hn : 0 < n) : 0 < a n := by
  rw [uniqueness k a h0 ha]
  exact_mod_cast positive hk hn

theorem source_radical_integral (k : ℕ) (a : ℕ → ℝ) (h0 : a 0 = 0)
    (ha : ∀ n, a (n + 1) = step k (a n)) (n : ℕ) :
    ∃ m : ℕ, Real.sqrt ((k : ℝ) * (k + 1) * a n * (a n + 1)) = m := by
  rw [uniqueness k a h0 ha]
  exact ⟨rootValue k n, radical_certificate k n⟩

theorem source_linear_recurrence (k : ℕ) (a : ℕ → ℝ) (h0 : a 0 = 0)
    (ha : ∀ n, a (n + 1) = step k (a n)) (n : ℕ) :
    a (n + 2) = (4 * (k : ℝ) + 2) * a (n + 1) - a n + 2 * k := by
  simp only [uniqueness k a h0 ha]
  have h : (value k (n + 2) : ℝ) + value k n = (4 * (k : ℝ) + 2) * value k (n + 1) + 2 * k := by
    exact_mod_cast linear_recurrence k n
  linarith

theorem model_tendsto_atTop {k : ℕ} (hk : 0 < k) :
    Tendsto (fun n => (value k n : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
  have hn : n ≤ k * n := Nat.le_mul_of_pos_left n hk
  exact_mod_cast hn.trans (linear_lower k n)

theorem source_tendsto_atTop {k : ℕ} (hk : 0 < k) (a : ℕ → ℝ) (h0 : a 0 = 0)
    (ha : ∀ n, a (n + 1) = step k (a n)) : Tendsto a atTop atTop := by
  have he : a = fun n => (value k n : ℝ) := funext (uniqueness k a h0 ha)
  rw [he]
  exact model_tendsto_atTop hk

theorem posted_recurrence (k n : ℕ) : value k (n + 1) =
    (value k n + 1) * k + (k + 1) * value k n +
      2 * Real.sqrt (k * (k + 1) * value k n * (value k n + 1)) := by
  simpa only [step, Nat.cast_add, Nat.cast_mul, Nat.cast_one] using real_recurrence k n

end RadicalIntegerPair

theorem solution : ¬ (∀ (k : ℕ) (a : ℕ → ℕ), a 0 = 0 →
    (∀ n, a (n + 1) = (a n + 1) * k + (k + 1) * a n +
      2 * Real.sqrt (k * (k + 1) * a n * (a n + 1))) → ∀ n, 0 < a n) := by
  intro h
  have hc := h 1 (RadicalIntegerPair.value 1) rfl (RadicalIntegerPair.posted_recurrence 1) 0
  exact Nat.lt_irrefl 0 hc

#print axioms RadicalIntegerPair.pair
#print axioms RadicalIntegerPair.value
#print axioms RadicalIntegerPair.rootValue
#print axioms RadicalIntegerPair.value_zero
#print axioms RadicalIntegerPair.rootValue_zero
#print axioms RadicalIntegerPair.value_succ
#print axioms RadicalIntegerPair.rootValue_succ
#print axioms RadicalIntegerPair.invariant
#print axioms RadicalIntegerPair.linear_recurrence
#print axioms RadicalIntegerPair.increment_lower
#print axioms RadicalIntegerPair.linear_lower
#print axioms RadicalIntegerPair.positive
#print axioms RadicalIntegerPair.strict_increase
#print axioms RadicalIntegerPair.radical_certificate
#print axioms RadicalIntegerPair.step
#print axioms RadicalIntegerPair.real_recurrence
#print axioms RadicalIntegerPair.uniqueness
#print axioms RadicalIntegerPair.exists_unique_sequence
#print axioms RadicalIntegerPair.source_integral
#print axioms RadicalIntegerPair.source_positive
#print axioms RadicalIntegerPair.source_radical_integral
#print axioms RadicalIntegerPair.source_linear_recurrence
#print axioms RadicalIntegerPair.model_tendsto_atTop
#print axioms RadicalIntegerPair.source_tendsto_atTop
#print axioms RadicalIntegerPair.posted_recurrence
#print axioms solution

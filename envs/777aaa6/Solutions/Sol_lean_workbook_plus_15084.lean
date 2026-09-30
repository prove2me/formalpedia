-- Prove2me | solution 1 for lean_workbook_plus_15084
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:07:41.541163+00:00
-- url     : https://prove2.me/submissions/29dfc1bd-2093-49c4-9b83-d9fb342bc761

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter Topology

namespace NonlinearProductInteger

def state : ℕ → ℤ × ℤ
  | 0 => (1, 1)
  | n + 1 => ((state n).2, 4 * (state n).2 - (state n).1 - 1)

def value (n : ℕ) : ℤ := (state n).1

theorem value_zero : value 0 = 1 := rfl
theorem value_one : value 1 = 1 := rfl

theorem linear_recurrence (n : ℕ) : value (n + 2) = 4 * value (n + 1) - value n - 1 := rfl

theorem positive_monotone (n : ℕ) : 1 ≤ value n ∧ value n ≤ value (n + 1) := by
  induction n with
  | zero => exact ⟨le_refl _, le_refl _⟩
  | succ n ih =>
    change 1 ≤ value (n + 1) ∧ value (n + 1) ≤ value (n + 2)
    rw [linear_recurrence]
    constructor <;> omega

theorem value_pos (n : ℕ) : 0 < value n := lt_of_lt_of_le (by decide) (positive_monotone n).1

def invariant (x y : ℤ) : ℤ := x ^ 2 + y ^ 2 - 4 * x * y + x + y

theorem invariant_step (x y : ℤ) : invariant y (4 * y - x - 1) = invariant x y := by
  unfold invariant
  ring

theorem invariant_zero (n : ℕ) : invariant (value n) (value (n + 1)) = 0 := by
  induction n with
  | zero => rw [value_zero, value_one]; unfold invariant; ring
  | succ n ih =>
    change invariant (value (n + 1)) (value (n + 2)) = 0
    rw [linear_recurrence, invariant_step, ih]

theorem nonlinear_recurrence (n : ℕ) :
    value (n + 2) * value n = value (n + 1) * (value (n + 1) + 1) := by
  have h := invariant_zero n
  unfold invariant at h
  rw [linear_recurrence]
  nlinarith only [h]

theorem doubling_lower (n : ℕ) : 2 * value (n + 1) ≤ value (n + 2) := by
  rw [linear_recurrence]
  have h := positive_monotone n
  omega

theorem geometric_lower (n : ℕ) : (2 : ℤ) ^ n ≤ value (n + 1) := by
  induction n with
  | zero => exact le_refl _
  | succ n ih =>
    rw [pow_succ]
    have h := doubling_lower n
    change 2 ^ n * 2 ≤ value (n + 2)
    omega

theorem strict_increase (n : ℕ) : value (n + 1) < value (n + 2) := by
  have h := doubling_lower n
  have hp := value_pos (n + 1)
  omega

section Field
variable {K : Type*} [Field K] [CharZero K]

theorem cast_nonlinear_recurrence (n : ℕ) :
    (value (n + 2) : K) * (value n : K) = (value (n + 1) : K) * ((value (n + 1) : K) + 1) := by
  exact_mod_cast nonlinear_recurrence n

theorem field_uniqueness (a : ℕ → K) (h0 : a 0 = 1) (h1 : a 1 = 1)
    (ha : ∀ n, a (n + 2) * a n = a (n + 1) * (a (n + 1) + 1)) (n : ℕ) :
    a n = (value n : K) := by
  have h (k : ℕ) : a k = (value k : K) ∧ a (k + 1) = (value (k + 1) : K) := by
    induction k with
    | zero => simpa only [Nat.zero_add, value_zero, value_one, Int.cast_one] using And.intro h0 h1
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      change a (k + 2) = (value (k + 2) : K)
      have hk : (value k : K) ≠ 0 := Int.cast_ne_zero.mpr (ne_of_gt (value_pos k))
      apply mul_right_cancel₀ hk
      rw [← ih.1, ha k, ih.1, ih.2, cast_nonlinear_recurrence]
  exact (h n).1

theorem exists_unique_field_sequence : ∃! a : ℕ → K,
    a 0 = 1 ∧ a 1 = 1 ∧ ∀ n, a (n + 2) * a n = a (n + 1) * (a (n + 1) + 1) := by
  refine ⟨fun n => (value n : K), ⟨?_, ?_, cast_nonlinear_recurrence⟩, ?_⟩
  · simp only [value_zero, Int.cast_one]
  · simp only [value_one, Int.cast_one]
  · rintro a ⟨h0, h1, ha⟩
    funext n
    exact field_uniqueness a h0 h1 ha n

theorem source_eq_integer (a : ℕ → K) (h0 : a 0 = 1) (h1 : a 1 = 1)
    (ha : ∀ n, 1 ≤ n → a (n + 1) * a (n - 1) = a n * (a n + 1)) (n : ℕ) :
    a n = (value n : K) := by
  apply field_uniqueness a h0 h1
  intro k
  simpa only [Nat.add_sub_cancel] using ha (k + 1) (by omega)

theorem source_linear_recurrence (a : ℕ → K) (h0 : a 0 = 1) (h1 : a 1 = 1)
    (ha : ∀ n, 1 ≤ n → a (n + 1) * a (n - 1) = a n * (a n + 1)) (n : ℕ) :
    a (n + 2) = 4 * a (n + 1) - a n - 1 := by
  simp only [source_eq_integer a h0 h1 ha]
  exact_mod_cast linear_recurrence n

end Field

theorem source_integral (a : ℕ → ℚ) (h0 : a 0 = 1) (h1 : a 1 = 1)
    (ha : ∀ n, 1 ≤ n → a (n + 1) * a (n - 1) = a n * (a n + 1)) (n : ℕ) :
    ∃ z : ℤ, a n = (z : ℚ) := ⟨value n, source_eq_integer a h0 h1 ha n⟩

theorem source_positive (a : ℕ → ℚ) (h0 : a 0 = 1) (h1 : a 1 = 1)
    (ha : ∀ n, 1 ≤ n → a (n + 1) * a (n - 1) = a n * (a n + 1)) (n : ℕ) :
    0 < a n := by
  rw [source_eq_integer a h0 h1 ha]
  exact_mod_cast value_pos n

theorem source_exists : ∃ a : ℕ → ℚ,
    a 0 = 1 ∧ a 1 = 1 ∧
    (∀ n, 1 ≤ n → a (n + 1) * a (n - 1) = a n * (a n + 1)) ∧
    (∀ n, 0 < a n) ∧ ∀ n, ∃ z : ℤ, a n = (z : ℚ) := by
  refine ⟨fun n => (value n : ℚ), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [value_zero, Int.cast_one]
  · simp only [value_one, Int.cast_one]
  · intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simpa only [Nat.add_sub_cancel] using (cast_nonlinear_recurrence (K := ℚ) k)
  · intro n
    change (0 : ℚ) < (value n : ℚ)
    exact_mod_cast value_pos n
  · intro n
    exact ⟨value n, rfl⟩

theorem value_tendsto_atTop : Tendsto (fun n => (value n : ℝ)) atTop atTop := by
  have hp : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hv : Tendsto (fun n => (value (n + 1) : ℝ)) atTop atTop := by
    apply tendsto_atTop_mono (fun n => ?_) hp
    exact_mod_cast geometric_lower n
  exact (tendsto_add_atTop_iff_nat 1).mp hv

theorem source_tendsto_atTop (a : ℕ → ℝ) (h0 : a 0 = 1) (h1 : a 1 = 1)
    (ha : ∀ n, 1 ≤ n → a (n + 1) * a (n - 1) = a n * (a n + 1)) :
    Tendsto a atTop atTop := by
  have he : a = fun n => (value n : ℝ) := funext (source_eq_integer a h0 h1 ha)
  rw [he]
  exact value_tendsto_atTop

end NonlinearProductInteger

theorem solution {a : ℕ → ℚ} (a0 : a 0 = 1) (a1 : a 1 = 1)
    (a_rec : ∀ n, a (n + 1) * a (n - 1) = a n * (a n + 1)) :
    ∀ n, a n = ⌊a n⌋ := by
  intro n
  obtain ⟨z, hz⟩ := NonlinearProductInteger.source_integral a a0 a1 (fun k _ => a_rec k) n
  rw [hz]
  simp

#print axioms NonlinearProductInteger.state
#print axioms NonlinearProductInteger.value
#print axioms NonlinearProductInteger.value_zero
#print axioms NonlinearProductInteger.value_one
#print axioms NonlinearProductInteger.linear_recurrence
#print axioms NonlinearProductInteger.positive_monotone
#print axioms NonlinearProductInteger.value_pos
#print axioms NonlinearProductInteger.invariant
#print axioms NonlinearProductInteger.invariant_step
#print axioms NonlinearProductInteger.invariant_zero
#print axioms NonlinearProductInteger.nonlinear_recurrence
#print axioms NonlinearProductInteger.doubling_lower
#print axioms NonlinearProductInteger.geometric_lower
#print axioms NonlinearProductInteger.strict_increase
#print axioms NonlinearProductInteger.cast_nonlinear_recurrence
#print axioms NonlinearProductInteger.field_uniqueness
#print axioms NonlinearProductInteger.exists_unique_field_sequence
#print axioms NonlinearProductInteger.source_eq_integer
#print axioms NonlinearProductInteger.source_linear_recurrence
#print axioms NonlinearProductInteger.source_integral
#print axioms NonlinearProductInteger.source_positive
#print axioms NonlinearProductInteger.source_exists
#print axioms NonlinearProductInteger.value_tendsto_atTop
#print axioms NonlinearProductInteger.source_tendsto_atTop
#print axioms solution

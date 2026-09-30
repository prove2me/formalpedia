-- Prove2me | solution 1 for lean_workbook_plus_63532
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:27:13.025616+00:00
-- url     : https://prove2.me/submissions/44f46057-0661-4dee-95e4-186bb455d089

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace NonlinearSquareSequence

def pair : ℕ → ℤ × ℤ
  | 0 => (1, 2)
  | n + 1 => (9 * (pair n).2 - (pair n).1,
      26 * (pair n).2 - 3 * (pair n).1)

def s (n : ℕ) : ℤ := (pair n).1
def t (n : ℕ) : ℤ := (pair n).2

@[simp] theorem s_zero : s 0 = 1 := rfl
@[simp] theorem t_zero : t 0 = 2 := rfl
@[simp] theorem s_succ (n : ℕ) : s (n + 1) = 9 * t n - s n := rfl
@[simp] theorem t_succ (n : ℕ) : t (n + 1) = 26 * t n - 3 * s n := rfl

theorem pair_positive (n : ℕ) : 0 < s n ∧ s n < t n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    simp only [s_succ, t_succ]
    constructor <;> omega

theorem invariant (n : ℕ) : s n ^ 2 + 3 * t n ^ 2 - 9 * s n * t n = -5 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [s_succ, t_succ]
    nlinarith only [ih]

theorem adjacent_s (n : ℕ) : s n * s (n + 1) = 3 * t n ^ 2 + 5 := by
  rw [s_succ]
  nlinarith only [invariant n]

theorem adjacent_t (n : ℕ) : 3 * t n * t (n + 1) = s (n + 1) ^ 2 + 5 := by
  rw [s_succ, t_succ]
  nlinarith only [invariant n]

def integerModel (n : ℕ) : ℤ :=
  if n % 2 = 0 then s (n / 2) ^ 2 else 3 * t (n / 2) ^ 2

@[simp] theorem model_even (n : ℕ) : integerModel (2 * n) = s n ^ 2 := by
  simp [integerModel]

@[simp] theorem model_odd (n : ℕ) : integerModel (2 * n + 1) = 3 * t n ^ 2 := by
  have h : (2 * n + 1) / 2 = n := by omega
  simp [integerModel, h]

@[simp] theorem model_zero : integerModel 0 = 1 := by
  simpa using model_even 0

@[simp] theorem model_one : integerModel 1 = 12 := by
  simpa using model_odd 0

theorem model_pos (n : ℕ) : 0 < integerModel n := by
  have hs := (pair_positive (n / 2)).1
  have ht : 0 < t (n / 2) := lt_trans hs (pair_positive (n / 2)).2
  unfold integerModel
  split <;> positivity

theorem model_cross (n : ℕ) :
    integerModel (n + 2) * integerModel n = (integerModel (n + 1) + 5) ^ 2 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
    rw [show 2 * m + 2 = 2 * (m + 1) by omega, model_even, model_even, model_odd]
    calc
      s (m + 1) ^ 2 * s m ^ 2 = (s m * s (m + 1)) ^ 2 := by ring
      _ = (3 * t m ^ 2 + 5) ^ 2 := by rw [adjacent_s]
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
    rw [show 2 * m + 1 + 2 = 2 * (m + 1) + 1 by omega,
      show 2 * m + 1 + 1 = 2 * (m + 1) by omega, model_odd, model_odd, model_even]
    calc
      3 * t (m + 1) ^ 2 * (3 * t m ^ 2) = (3 * t m * t (m + 1)) ^ 2 := by ring
      _ = (s (m + 1) ^ 2 + 5) ^ 2 := by rw [adjacent_t]

theorem model_linear (n : ℕ) :
    integerModel (n + 2) = 25 * integerModel (n + 1) - integerModel n - 10 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
    rw [show 2 * m + 2 = 2 * (m + 1) by omega, model_even, model_even, model_odd,
      s_succ]
    nlinarith only [invariant m]
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
    rw [show 2 * m + 1 + 2 = 2 * (m + 1) + 1 by omega,
      show 2 * m + 1 + 1 = 2 * (m + 1) by omega, model_odd, model_odd, model_even,
      s_succ, t_succ]
    nlinarith only [invariant m]

theorem model_recurrence {K : Type*} [Field K] [CharZero K] (n : ℕ) :
    (integerModel (n + 2) : K) =
      ((integerModel (n + 1) : K) + 5) ^ 2 / (integerModel n : K) := by
  have hn : (integerModel n : K) ≠ 0 := by
    exact_mod_cast (ne_of_gt (model_pos n))
  apply (eq_div_iff hn).2
  exact_mod_cast model_cross n

theorem unique_model {K : Type*} [Field K] [CharZero K] (u : ℕ → K)
    (h0 : u 0 = 1) (h1 : u 1 = 12)
    (hrec : ∀ n, u (n + 2) = (u (n + 1) + 5) ^ 2 / u n) :
    ∀ n, u n = (integerModel n : K) := by
  apply Nat.twoStepInduction
  · simpa using h0
  · simpa using h1
  · intro n hn hn1
    rw [hrec, hn, hn1, model_recurrence]

theorem exists_unique_sequence {K : Type*} [Field K] [CharZero K] :
    ∃! u : ℕ → K, u 0 = 1 ∧ u 1 = 12 ∧
      ∀ n, u (n + 2) = (u (n + 1) + 5) ^ 2 / u n := by
  refine ⟨fun n => (integerModel n : K), ?_, ?_⟩
  · exact ⟨by simp, by simp, model_recurrence⟩
  · intro u hu
    funext n
    exact unique_model u hu.1 hu.2.1 hu.2.2 n

theorem sequence_linear {K : Type*} [Field K] [CharZero K] (u : ℕ → K)
    (h0 : u 0 = 1) (h1 : u 1 = 12)
    (hrec : ∀ n, u (n + 2) = (u (n + 1) + 5) ^ 2 / u n) (n : ℕ) :
    u (n + 2) = 25 * u (n + 1) - u n - 10 := by
  simp only [unique_model u h0 h1 hrec]
  exact_mod_cast model_linear n

theorem rational_positive_integral (u : ℕ → ℚ)
    (h0 : u 0 = 1) (h1 : u 1 = 12)
    (hrec : ∀ n, u (n + 2) = (u (n + 1) + 5) ^ 2 / u n) (n : ℕ) :
    (u n).den = 1 ∧ 0 < (u n).num := by
  rw [unique_model u h0 h1 hrec n]
  simp only [Rat.den_intCast, Rat.num_intCast, true_and]
  exact model_pos n

theorem real_positive_integral (u : ℕ → ℝ)
    (h0 : u 0 = 1) (h1 : u 1 = 12)
    (hrec : ∀ n, u (n + 2) = (u (n + 1) + 5) ^ 2 / u n) (n : ℕ) :
    ∃ z : ℤ, 0 < z ∧ u n = z :=
  ⟨integerModel n, model_pos n, unique_model u h0 h1 hrec n⟩

theorem paired_values (u : ℕ → ℝ)
    (h0 : u 0 = 1) (h1 : u 1 = 12)
    (hrec : ∀ n, u (n + 2) = (u (n + 1) + 5) ^ 2 / u n) (n : ℕ) :
    u (2 * n) = (s n : ℝ) ^ 2 ∧ u (2 * n + 1) = 3 * (t n : ℝ) ^ 2 := by
  rw [unique_model u h0 h1 hrec, unique_model u h0 h1 hrec, model_even, model_odd]
  push_cast
  exact ⟨rfl, rfl⟩

theorem square_root_pair (u : ℕ → ℝ)
    (h0 : u 0 = 1) (h1 : u 1 = 12)
    (hrec : ∀ n, u (n + 2) = (u (n + 1) + 5) ^ 2 / u n) (n : ℕ) :
    Real.sqrt (u (2 * n)) + Real.sqrt (3 * u (2 * n + 1)) =
      (s n + 3 * t n : ℤ) := by
  obtain ⟨he, ho⟩ := paired_values u h0 h1 hrec n
  have hs : (0 : ℝ) ≤ s n := by exact_mod_cast (le_of_lt (pair_positive n).1)
  have ht : (0 : ℝ) ≤ t n := by
    exact_mod_cast (le_of_lt (lt_trans (pair_positive n).1 (pair_positive n).2))
  rw [he, ho, show (3 : ℝ) * (3 * (t n : ℝ) ^ 2) = (3 * (t n : ℝ)) ^ 2 by ring,
    Real.sqrt_sq hs, Real.sqrt_sq (mul_nonneg (by norm_num) ht)]
  push_cast
  rfl

theorem square_root_pair_integral (u : ℕ → ℝ)
    (h0 : u 0 = 1) (h1 : u 1 = 12)
    (hrec : ∀ n, u (n + 2) = (u (n + 1) + 5) ^ 2 / u n) (n : ℕ) :
    ∃ z : ℤ, 0 < z ∧
      Real.sqrt (u (2 * n)) + Real.sqrt (3 * u (2 * n + 1)) = z := by
  refine ⟨s n + 3 * t n, ?_, square_root_pair u h0 h1 hrec n⟩
  have := pair_positive n
  omega

theorem positive_index_source (u : ℕ → ℝ)
    (h1 : u 1 = 1) (h2 : u 2 = 12)
    (hrec : ∀ n, 2 ≤ n → u (n + 1) = (u n + 5) ^ 2 / u (n - 1)) :
    (∀ n, 0 < n → ∃ z : ℤ, 0 < z ∧ u n = z) ∧
      ∃ z : ℤ, 0 < z ∧ Real.sqrt (u 2015) + Real.sqrt (3 * u 2016) = z := by
  let v : ℕ → ℝ := fun n => u (n + 1)
  have hv0 : v 0 = 1 := h1
  have hv1 : v 1 = 12 := h2
  have hvrec : ∀ n, v (n + 2) = (v (n + 1) + 5) ^ 2 / v n := by
    intro n
    simpa [v, Nat.add_assoc] using hrec (n + 2) (by omega)
  constructor
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact real_positive_integral v hv0 hv1 hvrec m
  · exact square_root_pair_integral v hv0 hv1 hvrec 1007

end NonlinearSquareSequence

theorem solution (u : ℕ → ℚ) (u1 : u 0 = 1) (u2 : u 1 = 12)
    (u_rec : ∀ n, u (n + 1) = (u n + 5) ^ 2 / u (n - 1)) :
    ∀ n, 0 < n → (u n).den = 1 ∧ (u n).num > 0 := by
  have hrec : ∀ n, u (n + 2) = (u (n + 1) + 5) ^ 2 / u n := by
    intro n
    simpa [Nat.add_assoc] using u_rec (n + 1)
  intro n _
  exact NonlinearSquareSequence.rational_positive_integral u u1 u2 hrec n

#print axioms NonlinearSquareSequence.pair_positive
#print axioms NonlinearSquareSequence.s_zero
#print axioms NonlinearSquareSequence.t_zero
#print axioms NonlinearSquareSequence.s_succ
#print axioms NonlinearSquareSequence.t_succ
#print axioms NonlinearSquareSequence.invariant
#print axioms NonlinearSquareSequence.adjacent_s
#print axioms NonlinearSquareSequence.adjacent_t
#print axioms NonlinearSquareSequence.model_even
#print axioms NonlinearSquareSequence.model_odd
#print axioms NonlinearSquareSequence.model_zero
#print axioms NonlinearSquareSequence.model_one
#print axioms NonlinearSquareSequence.model_pos
#print axioms NonlinearSquareSequence.model_cross
#print axioms NonlinearSquareSequence.model_linear
#print axioms NonlinearSquareSequence.model_recurrence
#print axioms NonlinearSquareSequence.unique_model
#print axioms NonlinearSquareSequence.exists_unique_sequence
#print axioms NonlinearSquareSequence.sequence_linear
#print axioms NonlinearSquareSequence.rational_positive_integral
#print axioms NonlinearSquareSequence.real_positive_integral
#print axioms NonlinearSquareSequence.paired_values
#print axioms NonlinearSquareSequence.square_root_pair
#print axioms NonlinearSquareSequence.square_root_pair_integral
#print axioms NonlinearSquareSequence.positive_index_source
#print axioms solution

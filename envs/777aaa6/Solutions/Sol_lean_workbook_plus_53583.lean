-- Prove2me | solution 1 for lean_workbook_plus_53583
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:02:50.387698+00:00
-- url     : https://prove2.me/submissions/493c3167-003c-4086-8904-0f0cf89815fe

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace CompositionProductBounds

theorem positive_classification (f : ℕ → ℕ) :
    (∀ n, 0 < n → (n - 1) ^ 2 < f n * f (f n) ∧
      f n * f (f n) < n ^ 2 + n) ↔ ∀ n, 0 < n → f n = n := by
  constructor
  · intro hf n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      obtain ⟨hl, hu⟩ := hf n hn
      have hmpos : 0 < f n := by
        by_contra h
        have hz : f n = 0 := by omega
        simp [hz] at hl
      have hrpos : 0 < f (f n) := by
        by_contra h
        have hz : f (f n) = 0 := by omega
        simp [hz] at hl
      rcases lt_trichotomy (f n) n with hlt | heq | hgt
      · have hfix := ih (f n) hlt hmpos
        rw [hfix] at hl
        have hle : f n ≤ n - 1 := by omega
        nlinarith
      · exact heq
      · have hrlt : f (f n) < n := by
          by_contra h
          have hmle : n + 1 ≤ f n := by omega
          have hrle : n ≤ f (f n) := by omega
          have hmul := Nat.mul_le_mul hmle hrle
          nlinarith
        have hfix := ih (f (f n)) hrlt hrpos
        have hlow := (hf (f n) hmpos).1
        rw [hfix] at hlow
        have hle : f (f n) ≤ f n - 1 := by omega
        nlinarith
  · intro hf n hn
    rw [hf n hn, hf n hn]
    have hsub : n - 1 + 1 = n := by omega
    constructor <;> nlinarith

theorem all_solutions (f : ℕ → ℕ) :
    (∀ n, 0 < n → (n - 1) ^ 2 < f n * f (f n) ∧
      f n * f (f n) < n ^ 2 + n) ↔
      ∃ c : ℕ, f = fun n => if n = 0 then c else n := by
  rw [positive_classification]
  constructor
  · intro hf
    refine ⟨f 0, ?_⟩
    funext n
    by_cases hn : n = 0
    · simp [hn]
    · simp [hn, hf n (by omega)]
  · rintro ⟨c, rfl⟩ n hn
    simp [Nat.ne_of_gt hn]

theorem arbitrary_zero_model (c : ℕ) :
    ∀ n, 0 < n → (n - 1) ^ 2 <
      (if n = 0 then c else n) *
        (if (if n = 0 then c else n) = 0 then c else (if n = 0 then c else n)) ∧
      (if n = 0 then c else n) *
        (if (if n = 0 then c else n) = 0 then c else (if n = 0 then c else n)) <
          n ^ 2 + n :=
  (all_solutions (fun n => if n = 0 then c else n)).mpr ⟨c, rfl⟩

end CompositionProductBounds

theorem solution (f : ℕ → ℕ)
    (hf : ∀ n : ℕ, (n - 1) ^ 2 < f n * f (f n) ∧
      f n * f (f n) < n ^ 2 + n) : ∀ n : ℕ, f n = n := by
  intro n
  by_cases hn : 0 < n
  · exact (CompositionProductBounds.positive_classification f).mp (fun k _ => hf k) n hn
  · have hzero := (hf 0).2
    simp at hzero

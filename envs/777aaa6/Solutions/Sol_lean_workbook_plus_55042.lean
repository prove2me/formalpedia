-- Prove2me | solution 1 for lean_workbook_plus_55042
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T08:26:34.291375+00:00
-- url     : https://prove2.me/submissions/74fa647a-d3da-451b-ba7b-5ec7298fa1fb

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

theorem cube_sum_identity {R : Type*} [CommRing R] (a b : R) :
    a ^ 3 + b ^ 3 = (a + b) ^ 3 - 3 * a * b * (a + b) := by ring

theorem equal_sum_cube_classification (a b c d : ℝ) :
    (a + b = c + d ∧ a ^ 3 + b ^ 3 = c ^ 3 + d ^ 3) ↔
    (a + b = 0 ∧ c + d = 0) ∨ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  constructor
  · rintro ⟨hs, hc⟩
    rw [cube_sum_identity, cube_sum_identity, ← hs] at hc
    have hp : (a + b) * (a * b - c * d) = 0 := by nlinarith
    rcases mul_eq_zero.mp hp with hz | hprod
    · exact Or.inl ⟨hz, by linarith⟩
    · have ha := congrArg (fun t : ℝ => a * t) hs
      have hf : (a - c) * (a - d) = 0 := by nlinarith
      rcases mul_eq_zero.mp hf with h | h
      · exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
      · exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)
  · rintro (⟨hs, ht⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · refine ⟨by linarith, ?_⟩
      rw [cube_sum_identity, cube_sum_identity, hs, ht]
      ring
    · exact ⟨rfl, rfl⟩
    · constructor <;> ring

theorem distinct_solution_iff (a b c d : ℝ)
    (hd : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) :
    (a + b = c + d ∧ a ^ 3 + b ^ 3 = c ^ 3 + d ^ 3) ↔
    b = -a ∧ d = -c := by
  constructor
  · intro h
    rcases (equal_sum_cube_classification a b c d).mp h with hz | hc | hd'
    · exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
    · exact (hd.2.1 hc.1).elim
    · exact (hd.2.2.1 hd'.1).elim
  · rintro ⟨rfl, rfl⟩
    constructor <;> ring

theorem positive_magnitude_counterfamily (p q : ℝ) (hp : 0 < p) (hpq : p < q) :
    (p ≠ -p ∧ p ≠ q ∧ p ≠ -q ∧ -p ≠ q ∧ -p ≠ -q ∧ q ≠ -q) ∧
    p + -p = q + -q ∧ p ^ 3 + (-p) ^ 3 = q ^ 3 + (-q) ^ 3 := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  all_goals first | (intro h; linarith) | ring

theorem solution : ¬ ∀ a b c d : ℝ,
    (a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) →
    a + b = c + d → a ^ 3 + b ^ 3 = c ^ 3 + d ^ 3 → False := by
  intro h
  obtain ⟨hd, hs, hc⟩ := positive_magnitude_counterfamily 1 2 (by norm_num) (by norm_num)
  exact h 1 (-1) 2 (-2) hd hs hc

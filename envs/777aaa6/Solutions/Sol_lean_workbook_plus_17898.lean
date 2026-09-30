-- Prove2me | solution 1 for lean_workbook_plus_17898
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:38:40.004955+00:00
-- url     : https://prove2.me/submissions/97ebc887-cdf6-41ce-9187-b25973f9c836

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Filter Topology

namespace NegativeGeometric

theorem ratio (α β : ℝ) (a : ℕ → ℝ) (hα : 0 < α)
    (ha : ∀ n, α * a (n + 1) + β * a n = 0) (n : ℕ) :
    a (n + 1) = (-β / α) * a n := by
  apply (mul_left_cancel₀ hα.ne')
  calc
    α * a (n + 1) = -β * a n := by linarith [ha n]
    _ = α * ((-β / α) * a n) := by field_simp

theorem closed_form (α β : ℝ) (a : ℕ → ℝ) (hα : 0 < α)
    (ha : ∀ n, α * a (n + 1) + β * a n = 0) (n : ℕ) :
    a n = (-β / α) ^ n * a 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [ratio α β a hα ha, ih, pow_succ]; ring

theorem abs_closed_form (α β : ℝ) (a : ℕ → ℝ) (hα : 0 < α) (hβ : 0 < β)
    (ha : ∀ n, α * a (n + 1) + β * a n = 0) (n : ℕ) :
    |a n| = (β / α) ^ n * |a 0| := by
  rw [closed_form α β a hα ha n, abs_mul, abs_pow, abs_div, abs_neg,
    abs_of_pos hα, abs_of_pos hβ]

theorem model_recurrence (α β c : ℝ) (hα : 0 < α) (n : ℕ) :
    α * ((-β / α) ^ (n + 1) * c) + β * ((-β / α) ^ n * c) = 0 := by
  rw [pow_succ]
  field_simp
  ring

theorem exists_unique_sequence (α β c : ℝ) (hα : 0 < α) :
    ∃! a : ℕ → ℝ, a 0 = c ∧ ∀ n, α * a (n + 1) + β * a n = 0 := by
  refine ⟨fun n => (-β / α) ^ n * c, ⟨by simp, model_recurrence α β c hα⟩, ?_⟩
  rintro a ⟨h0, ha⟩
  funext n
  rw [closed_form α β a hα ha n, h0]

theorem limit_eq_zero (α β : ℝ) (a : ℕ → ℝ) (hα : 0 < α) (hβ : 0 < β)
    (ha : ∀ n, α * a (n + 1) + β * a n = 0) {L : ℝ}
    (hL : Tendsto a atTop (𝓝 L)) : L = 0 := by
  have hn : Tendsto (fun n => a (n + 1)) atTop (𝓝 L) :=
    hL.comp (tendsto_add_atTop_nat 1)
  have hs := (hn.const_mul α).add (hL.const_mul β)
  have hz : Tendsto (fun n => α * a (n + 1) + β * a n) atTop (𝓝 0) := by
    simpa only [ha] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have he : (α + β) * L = 0 := by nlinarith only [tendsto_nhds_unique hs hz]
  exact (mul_eq_zero.mp he).resolve_left (ne_of_gt (add_pos hα hβ))

theorem tendsto_zero_of_lt (α β : ℝ) (a : ℕ → ℝ) (hα : 0 < α) (hβ : 0 < β)
    (ha : ∀ n, α * a (n + 1) + β * a n = 0) (hβα : β < α) :
    Tendsto a atTop (𝓝 0) := by
  have hr : |-β / α| < 1 := by
    rw [abs_div, abs_neg, abs_of_pos hα, abs_of_pos hβ]
    exact (div_lt_one hα).2 hβα
  have hp := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hr).mul_const (a 0)
  simp only [zero_mul] at hp
  exact hp.congr (fun n => (closed_form α β a hα ha n).symm)

theorem converges_iff (α β : ℝ) (a : ℕ → ℝ) (hα : 0 < α) (hβ : 0 < β)
    (ha : ∀ n, α * a (n + 1) + β * a n = 0) :
    (∃ L : ℝ, Tendsto a atTop (𝓝 L)) ↔ a 0 = 0 ∨ β < α := by
  constructor
  · rintro ⟨L, hL⟩
    by_cases hβα : β < α
    · exact Or.inr hβα
    · left
      have hL0 := limit_eq_zero α β a hα hβ ha hL
      rw [hL0] at hL
      have hr : 1 ≤ β / α := (one_le_div hα).2 (le_of_not_gt hβα)
      have hb (n : ℕ) : |a 0| ≤ |a n| := by
        rw [abs_closed_form α β a hα hβ ha n]
        exact le_mul_of_one_le_left (abs_nonneg _) (one_le_pow₀ hr)
      have habs : Tendsto (fun n => |a n|) atTop (𝓝 0) := by simpa using hL.abs
      exact abs_eq_zero.mp (le_antisymm (ge_of_tendsto habs (.of_forall hb)) (abs_nonneg _))
  · rintro (h0 | hβα)
    · refine ⟨0, ?_⟩
      have he : a = fun _ => 0 := funext fun n => by rw [closed_form α β a hα ha n, h0]; simp
      rw [he]
      exact tendsto_const_nhds
    · exact ⟨0, tendsto_zero_of_lt α β a hα hβ ha hβα⟩

theorem equal_parameters (α : ℝ) (a : ℕ → ℝ) (hα : 0 < α)
    (ha : ∀ n, α * a (n + 1) + α * a n = 0) (n : ℕ) :
    a n = (-1 : ℝ) ^ n * a 0 := by
  rw [closed_form α α a hα ha n]
  congr 2
  exact neg_div_self hα.ne'

theorem abs_tendsto_atTop (α β : ℝ) (a : ℕ → ℝ) (hα : 0 < α) (hβ : 0 < β)
    (ha : ∀ n, α * a (n + 1) + β * a n = 0) (hβα : α < β) (h0 : a 0 ≠ 0) :
    Tendsto (fun n => |a n|) atTop atTop := by
  have hp := (tendsto_pow_atTop_atTop_of_one_lt ((one_lt_div hα).2 hβα)).atTop_mul_const
    (abs_pos.mpr h0)
  exact hp.congr (fun n => (abs_closed_form α β a hα hβ ha n).symm)

theorem consecutive_opposite_signs (α β : ℝ) (a : ℕ → ℝ) (hα : 0 < α) (hβ : 0 < β)
    (ha : ∀ n, α * a (n + 1) + β * a n = 0) (h0 : a 0 ≠ 0) (n : ℕ) :
    a (n + 1) * a n < 0 := by
  have hr : -β / α < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos hβ) hα
  have hn : a n ≠ 0 := by
    rw [closed_form α β a hα ha n]
    exact mul_ne_zero (pow_ne_zero _ hr.ne) h0
  rw [ratio α β a hα ha n]
  have he : (-β / α) * a n * a n = (-β / α) * (a n) ^ 2 := by ring
  rw [he]
  exact mul_neg_of_neg_of_pos hr (sq_pos_of_ne_zero hn)

end NegativeGeometric

theorem solution (α β : ℝ) (a : ℕ → ℝ) (hα : α > 0) (hβ : β > 0)
    (ha : ∀ n, α * a (n + 1) + β * a n = 0) :
    ∃ k : ℝ, ∀ n, a (n + 1) = k * a n :=
  ⟨-β / α, NegativeGeometric.ratio α β a hα ha⟩

#print axioms NegativeGeometric.ratio
#print axioms NegativeGeometric.closed_form
#print axioms NegativeGeometric.abs_closed_form
#print axioms NegativeGeometric.model_recurrence
#print axioms NegativeGeometric.exists_unique_sequence
#print axioms NegativeGeometric.limit_eq_zero
#print axioms NegativeGeometric.tendsto_zero_of_lt
#print axioms NegativeGeometric.converges_iff
#print axioms NegativeGeometric.equal_parameters
#print axioms NegativeGeometric.abs_tendsto_atTop
#print axioms NegativeGeometric.consecutive_opposite_signs
#print axioms solution

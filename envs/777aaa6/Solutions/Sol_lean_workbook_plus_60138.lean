-- Prove2me | solution 1 for lean_workbook_plus_60138
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:16:41.671297+00:00
-- url     : https://prove2.me/submissions/d1848854-9382-4a3b-ae93-a079a8f784fd

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace OrderedCubicProduct

theorem gap_lower (a b c : ℝ) (ha : 0 ≤ a) (hb : a ≤ b) (hc : b ≤ c) :
    15 * (b - a) ^ 3 + 8 * a ^ 2 * (c - b) ≤
      (a + 3 * b) * (b + 4 * c) * (c + 2 * a) - 60 * a * b * c := by
  have hu : 0 ≤ b - a := sub_nonneg.mpr hb
  have hv : 0 ≤ c - b := sub_nonneg.mpr hc
  have hr : 0 ≤ 5 * a ^ 2 * (b - a) + 20 * a * (b - a) ^ 2 +
      27 * a * (b - a) * (c - b) + 16 * a * (c - b) ^ 2 +
      27 * (b - a) ^ 2 * (c - b) + 12 * (b - a) * (c - b) ^ 2 := by positivity
  nlinarith

theorem bound (a b c : ℝ) (ha : 0 ≤ a) (hb : a ≤ b) (hc : b ≤ c) :
    60 * a * b * c ≤ (a + 3 * b) * (b + 4 * c) * (c + 2 * a) := by
  have hu : 0 ≤ b - a := sub_nonneg.mpr hb
  have hv : 0 ≤ c - b := sub_nonneg.mpr hc
  have hnon : 0 ≤ 15 * (b - a) ^ 3 + 8 * a ^ 2 * (c - b) := by positivity
  linarith [gap_lower a b c ha hb hc]

theorem equality (a b c : ℝ) (ha : 0 ≤ a) (hb : a ≤ b) (hc : b ≤ c) :
    (a + 3 * b) * (b + 4 * c) * (c + 2 * a) = 60 * a * b * c ↔
      (a = b ∧ b = c) ∨ (a = 0 ∧ b = 0) := by
  constructor
  · intro he
    have hu : 0 ≤ b - a := sub_nonneg.mpr hb
    have hv : 0 ≤ c - b := sub_nonneg.mpr hc
    have h1 : 0 ≤ (b - a) ^ 3 := by positivity
    have h2 : 0 ≤ a ^ 2 * (c - b) := by positivity
    have hl := gap_lower a b c ha hb hc
    have hz : (b - a) ^ 3 = 0 := by nlinarith
    have hab : a = b := (eq_of_sub_eq_zero (eq_zero_of_pow_eq_zero hz)).symm
    have hz2 : a ^ 2 * (c - b) = 0 := by nlinarith
    rcases mul_eq_zero.mp hz2 with ha0 | hcb
    · right
      have ha0' : a = 0 := eq_zero_of_pow_eq_zero ha0
      exact ⟨ha0', hab ▸ ha0'⟩
    · exact Or.inl ⟨hab, (eq_of_sub_eq_zero hcb).symm⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> ring

end OrderedCubicProduct

theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : a ≤ b) (hc : b ≤ c) :
    (a + 3 * b) * (b + 4 * c) * (c + 2 * a) ≥ 60 * a * b * c :=
  OrderedCubicProduct.bound a b c ha hb hc

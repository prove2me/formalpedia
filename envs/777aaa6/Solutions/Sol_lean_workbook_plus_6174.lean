-- Prove2me | solution 1 for lean_workbook_plus_6174
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:31:52.204279+00:00
-- url     : https://prove2.me/submissions/90f44755-8bed-46cd-bb24-ef4dac7acb19

import Mathlib

namespace CyclicRadicalZero

noncomputable def paired (a b c x : ℝ) : ℝ :=
  Real.sqrt (a + b * x) - Real.sqrt (a - c * x)

theorem paired_strictMono (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    StrictMono (paired a b c) := by
  intro x y hxy
  have hl : a + b * x < a + b * y := by
    simpa only [add_comm] using add_lt_add_left (mul_lt_mul_of_pos_left hxy hb) a
  have hr : a - c * y < a - c * x := sub_lt_sub_left (mul_lt_mul_of_pos_left hxy hc) a
  unfold paired
  by_cases hx : 0 ≤ x
  · have hpos : 0 ≤ a + b * x := add_nonneg ha.le (mul_nonneg hb.le hx)
    have hl' := Real.sqrt_lt_sqrt hpos hl
    have hr' := Real.sqrt_le_sqrt hr.le
    linarith
  · have hx' : x < 0 := lt_of_not_ge hx
    have hpos : 0 < a - c * x := by linarith [mul_neg_of_pos_of_neg hc hx']
    have hr' := (Real.sqrt_lt_sqrt_iff_of_pos hpos).mpr hr
    have hl' := Real.sqrt_le_sqrt hl.le
    linarith

noncomputable def balance (a b c x : ℝ) : ℝ :=
  paired a b c x + paired b c a x + paired c a b x

theorem balance_identity (a b c x : ℝ) :
    balance a b c x =
      (Real.sqrt (a + b * x) + Real.sqrt (b + c * x) + Real.sqrt (c + a * x)) -
      (Real.sqrt (b - a * x) + Real.sqrt (c - b * x) + Real.sqrt (a - c * x)) := by
  unfold balance paired
  ring

theorem balance_strictMono (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    StrictMono (balance a b c) := by
  intro x y hxy
  have h1 := paired_strictMono a b c ha hb hc hxy
  have h2 := paired_strictMono b c a hb hc ha hxy
  have h3 := paired_strictMono c a b hc ha hb hxy
  unfold balance
  linarith only [h1, h2, h3]

theorem balance_continuous (a b c : ℝ) : Continuous (balance a b c) := by
  unfold balance paired
  fun_prop

theorem balance_zero (a b c : ℝ) : balance a b c 0 = 0 := by
  simp [balance, paired]

theorem balance_signs (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (x : ℝ) :
    (balance a b c x < 0 ↔ x < 0) ∧
      (balance a b c x = 0 ↔ x = 0) ∧ (0 < balance a b c x ↔ 0 < x) := by
  have hm := balance_strictMono a b c ha hb hc
  refine ⟨?_, ?_, ?_⟩
  · simpa only [balance_zero] using
      (hm.lt_iff_lt : balance a b c x < balance a b c 0 ↔ x < 0)
  · simpa only [balance_zero] using
      (hm.injective.eq_iff : balance a b c x = balance a b c 0 ↔ x = 0)
  · simpa only [balance_zero] using
      (hm.lt_iff_lt : balance a b c 0 < balance a b c x ↔ 0 < x)

theorem full_source_iff (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (x : ℝ) :
    (Real.sqrt (a + b * x) + Real.sqrt (b + c * x) + Real.sqrt (c + a * x) =
      Real.sqrt (b - a * x) + Real.sqrt (c - b * x) + Real.sqrt (a - c * x)) ↔ x = 0 := by
  have he := (balance_signs a b c ha hb hc x).2.1
  rw [balance_identity, sub_eq_zero] at he
  exact he

theorem genuine_domain_iff (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (x : ℝ) :
    (0 ≤ a + b * x ∧ 0 ≤ b + c * x ∧ 0 ≤ c + a * x ∧
      0 ≤ b - a * x ∧ 0 ≤ c - b * x ∧ 0 ≤ a - c * x ∧
      Real.sqrt (a + b * x) + Real.sqrt (b + c * x) + Real.sqrt (c + a * x) =
        Real.sqrt (b - a * x) + Real.sqrt (c - b * x) + Real.sqrt (a - c * x)) ↔ x = 0 := by
  constructor
  · intro h
    exact (full_source_iff a b c ha hb hc x).mp h.2.2.2.2.2.2
  · rintro rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, (full_source_iff a b c ha hb hc 0).mpr rfl⟩
    all_goals first | simpa using ha.le | simpa using hb.le | simpa using hc.le

theorem unique_zero (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∃! x : ℝ, balance a b c x = 0 := by
  refine ⟨0, balance_zero a b c, ?_⟩
  intro x hx
  exact (balance_signs a b c ha hb hc x).2.1.mp hx

end CyclicRadicalZero

theorem solution (a b c x : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (_h₁ : 0 < x)
    (h₂ : Real.sqrt (a + b * x) + Real.sqrt (b + c * x) + Real.sqrt (c + a * x) =
      Real.sqrt (b - a * x) + Real.sqrt (c - b * x) + Real.sqrt (a - c * x)) :
    x = 0 := by
  exact (CyclicRadicalZero.full_source_iff a b c h₀.1 h₀.2.1 h₀.2.2 x).mp h₂

#print axioms CyclicRadicalZero.paired_strictMono
#print axioms CyclicRadicalZero.balance_identity
#print axioms CyclicRadicalZero.balance_strictMono
#print axioms CyclicRadicalZero.balance_continuous
#print axioms CyclicRadicalZero.balance_zero
#print axioms CyclicRadicalZero.balance_signs
#print axioms CyclicRadicalZero.full_source_iff
#print axioms CyclicRadicalZero.genuine_domain_iff
#print axioms CyclicRadicalZero.unique_zero
#print axioms solution

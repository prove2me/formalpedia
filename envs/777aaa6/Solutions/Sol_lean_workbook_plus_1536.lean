-- Prove2me | solution 1 for lean_workbook_plus_1536
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:27:13.416924+00:00
-- url     : https://prove2.me/submissions/974299d3-b67f-4daf-ae4f-d4ba4cdc96ba

import Mathlib

namespace FourVariableComplementProductSystem

def System (a b c d : ℝ) : Prop :=
  a + b * c * d = 2 ∧ b + c * d * a = 2 ∧
  c + d * a * b = 2 ∧ d + a * b * c = 2

def Listed (a b c d : ℝ) : Prop :=
  (a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 1) ∨
  (a = 3 ∧ b = -1 ∧ c = -1 ∧ d = -1) ∨
  (a = -1 ∧ b = 3 ∧ c = -1 ∧ d = -1) ∨
  (a = -1 ∧ b = -1 ∧ c = 3 ∧ d = -1) ∨
  (a = -1 ∧ b = -1 ∧ c = -1 ∧ d = 3)

theorem swap_second_third (a b c d : ℝ) (h : System a b c d) : System a c b d := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination h.1
  · linear_combination h.2.2.1
  · linear_combination h.2.1
  · linear_combination h.2.2.2

theorem swap_second_fourth (a b c d : ℝ) (h : System a b c d) : System a d c b := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination h.1
  · linear_combination h.2.2.2
  · linear_combination h.2.2.1
  · linear_combination h.2.1

theorem sum_product_rigidity (a b : ℝ) (hs : a + b = 2) (hp : a * b = 1) :
    a = 1 ∧ b = 1 := by
  have hb : b = 2 - a := by linarith
  rw [hb] at hp
  have hz : (a - 1) ^ 2 = 0 := by nlinarith only [hp]
  have he := sq_eq_zero_iff.mp hz
  constructor <;> linarith

theorem unequal_pair (a b c d : ℝ) (h : System a b c d) (hne : a ≠ b) :
    (a = 3 ∧ b = -1 ∧ c = -1 ∧ d = -1) ∨
    (a = -1 ∧ b = 3 ∧ c = -1 ∧ d = -1) := by
  have hf : (a - b) * (1 - c * d) = 0 := by
    linear_combination h.1 - h.2.1
  have hcd : c * d = 1 := by
    have hz := (mul_eq_zero.mp hf).resolve_left (sub_ne_zero.mpr hne)
    linarith
  have hs : a + b = 2 := by
    linear_combination h.1 - b * hcd
  have he : c = d := by
    by_contra hne'
    have hf' : (c - d) * (1 - a * b) = 0 := by
      linear_combination h.2.2.1 - h.2.2.2
    have hab : a * b = 1 := by
      have hz := (mul_eq_zero.mp hf').resolve_left (sub_ne_zero.mpr hne')
      linarith
    obtain ⟨ha, hb⟩ := sum_product_rigidity a b hs hab
    exact hne (ha.trans hb.symm)
  rw [← he] at hcd
  have hc2 : c ^ 2 = (1 : ℝ) ^ 2 := by nlinarith only [hcd]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hc2 with hc | hc
  · have hd : d = 1 := he.symm.trans hc
    have h3 := h.2.2.1
    rw [hc, hd] at h3
    have hab : a * b = 1 := by nlinarith only [h3]
    obtain ⟨ha, hb⟩ := sum_product_rigidity a b hs hab
    exact (hne (ha.trans hb.symm)).elim
  · have hd : d = -1 := he.symm.trans hc
    have h3 := h.2.2.1
    rw [hc, hd] at h3
    have hab : a * b = -3 := by nlinarith only [h3]
    have hb : b = 2 - a := by linarith
    rw [hb] at hab
    have hz : (a - 3) * (a + 1) = 0 := by nlinarith only [hab]
    rcases mul_eq_zero.mp hz with ha | ha
    · exact Or.inl ⟨by linarith, by linarith, hc, hd⟩
    · exact Or.inr ⟨by linarith, by linarith, hc, hd⟩

theorem constant_coordinate (a : ℝ) (h : System a a a a) : a = 1 := by
  have hf : (a - 1) * (a ^ 2 + a + 2) = 0 := by
    linear_combination h.1
  have hp : 0 < a ^ 2 + a + 2 := by nlinarith [sq_nonneg (2 * a + 1)]
  have hz := (mul_eq_zero.mp hf).resolve_right (ne_of_gt hp)
  linarith

theorem full_classification (a b c d : ℝ) : System a b c d ↔ Listed a b c d := by
  constructor
  · intro h
    by_cases hab : a = b
    · by_cases hac : a = c
      · by_cases had : a = d
        · have ha := constant_coordinate a (by simpa [← hab, ← hac, ← had] using h)
          exact Or.inl ⟨ha, hab.symm.trans ha, hac.symm.trans ha, had.symm.trans ha⟩
        · rcases unequal_pair a d c b (swap_second_fourth a b c d h) had with
            ⟨ha, hd, hc, hb⟩ | ⟨ha, hd, hc, hb⟩
          · exact Or.inr (Or.inl ⟨ha, hb, hc, hd⟩)
          · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ha, hb, hc, hd⟩)))
      · rcases unequal_pair a c b d (swap_second_third a b c d h) hac with
          ⟨ha, hc, hb, hd⟩ | ⟨ha, hc, hb, hd⟩
        · exact Or.inr (Or.inl ⟨ha, hb, hc, hd⟩)
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ha, hb, hc, hd⟩)))
    · rcases unequal_pair a b c d h hab with ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩
      · exact Or.inr (Or.inl ⟨ha, hb, hc, hd⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨ha, hb, hc, hd⟩))
  · rintro (⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩) <;>
      refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

theorem positive_classification (a b c d : ℝ) :
    (System a b c d ∧ 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) ↔
      a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 1 := by
  rw [full_classification]
  constructor
  · rintro ⟨h, ha, hb, hc, hd⟩
    rcases h with h | h | h | h | h
    · exact h
    · linarith [h.2.1]
    · linarith [h.1]
    · linarith [h.1]
    · linarith [h.1]
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨Or.inl ⟨rfl, rfl, rfl, rfl⟩, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem source_exists : ∃ a b c d : ℝ, System a b c d :=
  ⟨1, 1, 1, 1, (full_classification _ _ _ _).mpr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)⟩

end FourVariableComplementProductSystem

theorem solution (x : ℕ → ℝ) :
    (∃ a b c d : ℝ, a + b * c * d = 2 ∧ b + c * d * a = 2 ∧
      c + d * a * b = 2 ∧ d + a * b * c = 2) ↔
    (∃ a b c d : ℝ, a + b * c * d = 2 ∧ b + c * d * a = 2 ∧
      c + d * a * b = 2 ∧ d + a * b * c = 2) := Iff.rfl

#print axioms FourVariableComplementProductSystem.swap_second_third
#print axioms FourVariableComplementProductSystem.swap_second_fourth
#print axioms FourVariableComplementProductSystem.sum_product_rigidity
#print axioms FourVariableComplementProductSystem.unequal_pair
#print axioms FourVariableComplementProductSystem.constant_coordinate
#print axioms FourVariableComplementProductSystem.full_classification
#print axioms FourVariableComplementProductSystem.positive_classification
#print axioms FourVariableComplementProductSystem.source_exists
#print axioms solution

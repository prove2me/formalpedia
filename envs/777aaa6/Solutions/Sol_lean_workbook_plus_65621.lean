-- Prove2me | solution 1 for lean_workbook_plus_65621
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T08:58:25.149152+00:00
-- url     : https://prove2.me/submissions/af8491da-6e0c-4737-8a2d-2458b3d73139

import Mathlib

namespace SignedEvenMomentClassification

def System (x y z : ℝ) : Prop :=
  x ^ 2 + y ^ 2 + z ^ 2 = 9 ∧ x ^ 4 + y ^ 4 + z ^ 4 = 33 ∧ x * y * z = -4

def Listed (x y z : ℝ) : Prop :=
  (x = -1 ∧ y = 2 ∧ z = 2) ∨ (x = 2 ∧ y = -1 ∧ z = 2) ∨
  (x = 2 ∧ y = 2 ∧ z = -1) ∨ (x = 1 ∧ y = 2 ∧ z = -2) ∨
  (x = 1 ∧ y = -2 ∧ z = 2) ∨ (x = 2 ∧ y = 1 ∧ z = -2) ∨
  (x = 2 ∧ y = -2 ∧ z = 1) ∨ (x = -2 ∧ y = 1 ∧ z = 2) ∨
  (x = -2 ∧ y = 2 ∧ z = 1) ∨ (x = -1 ∧ y = -2 ∧ z = -2) ∨
  (x = -2 ∧ y = -1 ∧ z = -2) ∨ (x = -2 ∧ y = -2 ∧ z = -1)

theorem elementary_squares (x y z : ℝ) (h : System x y z) :
    x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2 = 24 ∧
      x ^ 2 * y ^ 2 * z ^ 2 = 16 := by
  have hs : (x ^ 2 + y ^ 2 + z ^ 2) ^ 2 = 81 := by rw [h.1]; norm_num
  refine ⟨by nlinarith [h.2.1], ?_⟩
  calc
    x ^ 2 * y ^ 2 * z ^ 2 = (x * y * z) ^ 2 := by ring
    _ = 16 := by rw [h.2.2]; norm_num

theorem coordinate_polynomial (x y z : ℝ) (h : System x y z) :
    (x ^ 2 - 1) * (x ^ 2 - 4) ^ 2 = 0 := by
  obtain ⟨hq, hp⟩ := elementary_squares x y z h
  linear_combination x ^ 4 * h.1 - x ^ 2 * hq + hp

theorem coordinate_roots (x y z : ℝ) (h : System x y z) :
    x = 1 ∨ x = -1 ∨ x = 2 ∨ x = -2 := by
  rcases mul_eq_zero.mp (coordinate_polynomial x y z h) with hx | hx
  · have hf : (x - 1) * (x + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hf with h1 | h1
    · exact Or.inl (by linarith)
    · exact Or.inr (Or.inl (by linarith))
  · have hx' : x ^ 2 - 4 = 0 := (sq_eq_zero_iff).mp hx
    have hf : (x - 2) * (x + 2) = 0 := by nlinarith
    rcases mul_eq_zero.mp hf with h1 | h1
    · exact Or.inr (Or.inr (Or.inl (by linarith)))
    · exact Or.inr (Or.inr (Or.inr (by linarith)))

theorem cyclic_invariance (x y z : ℝ) (h : System x y z) : System y z x := by
  exact ⟨by nlinarith [h.1], by nlinarith [h.2.1], by nlinarith [h.2.2]⟩

theorem of_absolute_values (x y z : ℝ)
    (h : (|x| = 1 ∧ |y| = 2 ∧ |z| = 2) ∨
      (|x| = 2 ∧ |y| = 1 ∧ |z| = 2) ∨
      (|x| = 2 ∧ |y| = 2 ∧ |z| = 1))
    (hp : x * y * z = -4) : System x y z := by
  have habs (a b : ℝ) (h : |a| = b) : a ^ 2 = b ^ 2 := by rw [← h, sq_abs]
  rcases h with ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩
  all_goals
    have hx2 := habs x _ hx
    have hy2 := habs y _ hy
    have hz2 := habs z _ hz
    refine ⟨by nlinarith, ?_, hp⟩
    nlinarith [sq_nonneg (x ^ 2), sq_nonneg (y ^ 2), sq_nonneg (z ^ 2)]

theorem full_classification (x y z : ℝ) : System x y z ↔ Listed x y z := by
  constructor
  · intro h
    have hx := coordinate_roots x y z h
    have hy := coordinate_roots y z x (cyclic_invariance x y z h)
    have hz := coordinate_roots z x y (cyclic_invariance y z x (cyclic_invariance x y z h))
    rcases hx with rfl | rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl | rfl <;>
      rcases hz with rfl | rfl | rfl | rfl <;> norm_num [System, Listed] at *
  · intro h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    all_goals obtain ⟨rfl, rfl, rfl⟩ := h
    all_goals apply of_absolute_values <;> norm_num

theorem absolute_value_classification (x y z : ℝ) : System x y z ↔
    ((|x| = 1 ∧ |y| = 2 ∧ |z| = 2) ∨
      (|x| = 2 ∧ |y| = 1 ∧ |z| = 2) ∨
      (|x| = 2 ∧ |y| = 2 ∧ |z| = 1)) ∧ x * y * z = -4 := by
  constructor
  · intro h
    refine ⟨?_, h.2.2⟩
    have hc := (full_classification x y z).mp h
    rcases hc with h | h | h | h | h | h | h | h | h | h | h | h
    all_goals obtain ⟨rfl, rfl, rfl⟩ := h
    all_goals norm_num
  · rintro ⟨h, hp⟩
    exact of_absolute_values x y z h hp

theorem genuine_model : System 2 2 (-1) :=
  (full_classification _ _ _).mpr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))

end SignedEvenMomentClassification

theorem solution : ¬ (∀ x y z : ℝ, x ^ 2 + y ^ 2 + z ^ 2 = 9 →
    x ^ 4 + y ^ 4 + z ^ 4 = 33 → x * y * z = -4 → x = 2 ∧ y = -1 ∧ z = -2) := by
  intro h
  obtain ⟨h1, h2, h3⟩ := SignedEvenMomentClassification.genuine_model
  have hy := (h 2 2 (-1) h1 h2 h3).2.1
  norm_num at hy

#print axioms SignedEvenMomentClassification.elementary_squares
#print axioms SignedEvenMomentClassification.coordinate_polynomial
#print axioms SignedEvenMomentClassification.coordinate_roots
#print axioms SignedEvenMomentClassification.cyclic_invariance
#print axioms SignedEvenMomentClassification.of_absolute_values
#print axioms SignedEvenMomentClassification.full_classification
#print axioms SignedEvenMomentClassification.absolute_value_classification
#print axioms SignedEvenMomentClassification.genuine_model
#print axioms solution

-- Prove2me | solution 1 for lean_workbook_plus_73131
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:52:13.001113+00:00
-- url     : https://prove2.me/submissions/03e91a40-4e65-44d6-bb41-408f74899be8

import Mathlib

namespace FiveVariableComplementSums

def System (A B C D E x y z u v : ℝ) : Prop :=
  x + y + z + u = A ∧ y + z + u + v = B ∧ z + u + v + x = C ∧
    u + v + x + y = D ∧ v + x + y + z = E

theorem general_classification (A B C D E x y z u v : ℝ) :
    System A B C D E x y z u v ↔
    x = (A - 3 * B + C + D + E) / 4 ∧
      y = (A + B - 3 * C + D + E) / 4 ∧
      z = (A + B + C - 3 * D + E) / 4 ∧
      u = (A + B + C + D - 3 * E) / 4 ∧
      v = (-3 * A + B + C + D + E) / 4 := by
  constructor
  · rintro ⟨h0, h1, h2, h3, h4⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem general_exists (A B C D E : ℝ) :
    ∃ x y z u v : ℝ, System A B C D E x y z u v := by
  refine ⟨(A - 3 * B + C + D + E) / 4, (A + B - 3 * C + D + E) / 4,
    (A + B + C - 3 * D + E) / 4, (A + B + C + D - 3 * E) / 4,
    (-3 * A + B + C + D + E) / 4, ?_⟩
  exact (general_classification _ _ _ _ _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem total_sum (A B C D E x y z u v : ℝ)
    (h : System A B C D E x y z u v) : x + y + z + u + v = (A + B + C + D + E) / 4 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  linarith

theorem source_classification (x y z u v : ℝ) :
    System 5 1 2 0 4 x y z u v ↔ x = 2 ∧ y = 1 ∧ z = 3 ∧ u = -1 ∧ v = -2 := by
  rw [general_classification]
  norm_num
  rfl

theorem source_model : System 5 1 2 0 4 2 1 3 (-1) (-2) := by
  norm_num [System]

end FiveVariableComplementSums

theorem solution (x y z u v : ℝ) (h0 : x + y + z + u = 5)
    (h1 : y + z + u + v = 1) (h2 : z + u + v + x = 2)
    (h3 : u + v + x + y = 0) (h4 : v + x + y + z = 4) :
    x = 2 ∧ y = 1 ∧ z = 3 ∧ u = -1 ∧ v = -2 :=
  (FiveVariableComplementSums.source_classification x y z u v).mp ⟨h0, h1, h2, h3, h4⟩

#print axioms FiveVariableComplementSums.general_classification
#print axioms FiveVariableComplementSums.general_exists
#print axioms FiveVariableComplementSums.total_sum
#print axioms FiveVariableComplementSums.source_classification
#print axioms FiveVariableComplementSums.source_model
#print axioms solution

-- Prove2me | solution 1 for lean_workbook_plus_75435
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:39:20.414337+00:00
-- url     : https://prove2.me/submissions/b65d57c2-35b9-4bde-b469-d6e86bbac136

import Mathlib

namespace TranslatedEllipseQuarticInfeasible

def Ellipse (x y : ℝ) : Prop := (x + y) ^ 2 - x * y - 3 * x - 4 * y + 4 = 0

def System (x y : ℝ) : Prop := x ^ 4 + y ^ 2 = 697 / 81 ∧ Ellipse x y

theorem translated_equivalence (x y : ℝ) :
    Ellipse x y ↔ (x - 1) ^ 2 + (x - 1) * (y - 1) + (y - 1) ^ 2 - (y - 1) = 0 := by
  unfold Ellipse
  constructor <;> intro h <;> nlinarith only [h]

-- The completed-square argument is the translated coordinate-bound lemma.
theorem coordinate_bounds (x y : ℝ) (h : Ellipse x y) :
    0 ≤ x ∧ x ≤ 4 / 3 ∧ 1 ≤ y ∧ y ≤ 7 / 3 := by
  have he := (translated_equivalence x y).mp h
  have hsx : (x + 2 * y - 4) ^ 2 + 3 * (x - 1) ^ 2 + 2 * (x - 1) - 1 = 0 := by
    nlinarith only [he]
  have hsy : (2 * x + y - 3) ^ 2 + 3 * (y - 1) ^ 2 - 4 * (y - 1) = 0 := by
    nlinarith only [he]
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith only [hsx, sq_nonneg (x + 2 * y - 4), sq_nonneg x]
  · nlinarith only [hsx, sq_nonneg (x + 2 * y - 4), sq_nonneg (x - 4 / 3)]
  · nlinarith only [hsy, sq_nonneg (2 * x + y - 3), sq_nonneg (y - 1)]
  · nlinarith only [hsy, sq_nonneg (2 * x + y - 3), sq_nonneg (y - 7 / 3)]

theorem sharp_coordinate_models :
    Ellipse 0 2 ∧ Ellipse (4 / 3) (4 / 3) ∧ Ellipse 1 1 ∧
      Ellipse (1 / 3) (7 / 3) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals unfold Ellipse; ring

theorem separate_power_bounds (x y : ℝ) (h : Ellipse x y) :
    x ^ 4 ≤ 256 / 81 ∧ y ^ 2 ≤ 49 / 9 := by
  obtain ⟨hx0, hx, hy1, hy⟩ := coordinate_bounds x y h
  have hx2 : x ^ 2 ≤ 16 / 9 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hx) (show 0 ≤ 4 / 3 + x by linarith)]
  constructor
  · have hm := mul_nonneg (sub_nonneg.mpr hx2)
      (show 0 ≤ 16 / 9 + x ^ 2 by positivity)
    nlinarith only [hm]
  · have hm := mul_nonneg (sub_nonneg.mpr hy) (show 0 ≤ 7 / 3 + y by linarith)
    nlinarith only [hm]

theorem upper_y_forces_x (x y : ℝ) (h : Ellipse x y) (hy : y = 7 / 3) :
    x = 1 / 3 := by
  change (x + y) ^ 2 - x * y - 3 * x - 4 * y + 4 = 0 at h
  rw [hy] at h
  have hs : (x - 1 / 3) ^ 2 = 0 := by nlinarith only [h]
  have hz := sq_eq_zero_iff.mp hs
  linarith only [hz]

theorem strict_quartic_square_bound (x y : ℝ) (h : Ellipse x y) :
    x ^ 4 + y ^ 2 < 697 / 81 := by
  obtain ⟨hx4, hy2⟩ := separate_power_bounds x y h
  obtain ⟨_, _, hy1, _⟩ := coordinate_bounds x y h
  have hle : x ^ 4 + y ^ 2 ≤ 697 / 81 := by linarith only [hx4, hy2]
  apply lt_of_le_of_ne hle
  intro he
  have hy2eq : y ^ 2 = (7 / 3) ^ 2 := by nlinarith only [he, hx4, hy2]
  have hy : y = 7 / 3 :=
    (sq_eq_sq₀ (by linarith only [hy1] : 0 ≤ y) (by positivity : (0 : ℝ) ≤ 7 / 3)).mp hy2eq
  have hx := upper_y_forces_x x y h hy
  rw [hx, hy] at he
  norm_num at he

theorem no_solutions (x y : ℝ) : ¬ System x y := by
  rintro ⟨he, h⟩
  have hb := strict_quartic_square_bound x y h
  linarith only [he, hb]

theorem empty_solution_set : {p : ℝ × ℝ | System p.1 p.2} = ∅ := by
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false]
  exact iff_false_intro (no_solutions p.1 p.2)

theorem workbook_pair_fails_ellipse : ¬ Ellipse (4 / 3) (7 / 3) := by
  intro h
  have he := upper_y_forces_x (4 / 3) (7 / 3) h rfl
  norm_num at he

end TranslatedEllipseQuarticInfeasible

theorem solution (x y : ℝ) (h1 : x ^ 4 + y ^ 2 = 697 / 81)
    (h2 : (x + y) ^ 2 - x * y - 3 * x - 4 * y + 4 = 0) : x = 2 ∧ y = -1 / 3 := by
  exact False.elim (TranslatedEllipseQuarticInfeasible.no_solutions x y ⟨h1, h2⟩)

#print axioms TranslatedEllipseQuarticInfeasible.translated_equivalence
#print axioms TranslatedEllipseQuarticInfeasible.coordinate_bounds
#print axioms TranslatedEllipseQuarticInfeasible.sharp_coordinate_models
#print axioms TranslatedEllipseQuarticInfeasible.separate_power_bounds
#print axioms TranslatedEllipseQuarticInfeasible.upper_y_forces_x
#print axioms TranslatedEllipseQuarticInfeasible.strict_quartic_square_bound
#print axioms TranslatedEllipseQuarticInfeasible.no_solutions
#print axioms TranslatedEllipseQuarticInfeasible.empty_solution_set
#print axioms TranslatedEllipseQuarticInfeasible.workbook_pair_fails_ellipse
#print axioms solution

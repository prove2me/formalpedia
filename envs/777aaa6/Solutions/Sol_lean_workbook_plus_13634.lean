-- Prove2me | solution 1 for lean_workbook_plus_13634
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T01:57:31.52617+00:00
-- url     : https://prove2.me/submissions/e7a825be-79fd-45d1-985a-4e0048181701

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

private theorem full_source (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0)
    (hz : z ≥ 0) (h : x + y + z ≥ 5) :
    ((2*x+3*y+6*z ≥ 14) ∧ (2*y+3*z+6*x ≥ 14)) ∨
    ((2*y+3*z+6*x ≥ 14) ∧ (2*z+3*x+6*y ≥ 14)) ∨
    ((2*z+3*x+6*y ≥ 14) ∧ (2*x+3*y+6*z ≥ 14)) := by
  by_cases ha : 2*x+3*y+6*z ≥ 14
  · by_cases hb : 2*y+3*z+6*x ≥ 14
    · exact Or.inl ⟨ha, hb⟩
    · exact Or.inr (Or.inr ⟨by linarith, ha⟩)
  · exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)

theorem solution (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0)
    (h : x + y + z ≥ 5) : ∃ i j : Fin 3, i ≠ j ∧
    (2*x+3*y+6*z ≥ 14 ∨ 2*y+3*z+6*x ≥ 14 ∨ 2*z+3*x+6*y ≥ 14) := by
  refine ⟨0, 1, by decide, ?_⟩
  rcases full_source x y z hx hy hz h with hab | hbc | hca
  · exact Or.inl hab.1
  · exact Or.inr (Or.inl hbc.1)
  · exact Or.inr (Or.inr hca.1)

#print axioms solution

-- Prove2me | solution 1 for lean_workbook_plus_77282
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:11:00.01802+00:00
-- url     : https://prove2.me/submissions/eb5e5ae1-a12d-4ca0-b8cb-0c552d535314

import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

theorem solution (f : ℝ → ℝ) (hf : Continuous f) (h : ∀ x, f x = f (1 / x)) :
    ∃ h : ℝ → ℝ, Continuous h ∧ ∀ x, f x = h x + h (1 / x) := by
  refine ⟨fun x => f x / 2, hf.div_const 2, ?_⟩
  intro x
  dsimp
  linarith [h x]

#print axioms solution

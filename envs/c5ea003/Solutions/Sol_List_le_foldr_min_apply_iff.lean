-- Prove2me | solution 1 for List.le_foldr_min_apply_iff
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-30T17:50:53.844585+00:00
-- url     : https://prove2.me/submissions/f452b256-dfd8-4978-8f85-4417f5fcfbbe

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.List.MinMax
import Mathlib.Tactic

set_option autoImplicit false

open Filter Topology

open List

theorem solution (l : List (ℝ → ℝ)) (r x y : ℝ) :
    y ≤ l.foldr (fun f s ↦ min (f x) s) r ↔ y ≤ r ∧ ∀ f ∈ l, y ≤ f x := by
  induction l with
  | nil => simp
  | cons f l ih => simp [ih, and_left_comm]

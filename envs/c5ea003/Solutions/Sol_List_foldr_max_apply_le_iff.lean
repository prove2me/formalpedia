-- Prove2me | solution 1 for List.foldr_max_apply_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-30T17:54:00.27303+00:00
-- url     : https://prove2.me/submissions/ba5b5313-97a2-422d-befe-061089d5b61f

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.List.MinMax
import Mathlib.Tactic

set_option autoImplicit false

open Filter Topology

open List

theorem solution (l : List (ℝ → ℝ)) (r x y : ℝ) :
    l.foldr (fun f s ↦ max (f x) s) r ≤ y ↔ r ≤ y ∧ ∀ f ∈ l, f x ≤ y := by
  induction l with
  | nil => simp
  | cons f l ih => simp [ih, and_left_comm]

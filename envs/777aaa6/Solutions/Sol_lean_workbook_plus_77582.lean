-- Prove2me | solution 1 for lean_workbook_plus_77582
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-17T16:59:15.001+00:00
-- url     : https://prove2.me/submissions/bd522b7e-59db-4dd4-82c4-0debfb4a4ea7

import Mathlib.Tactic

theorem solution (f : ℕ → ℕ) (hf : f = fun n => n.div 3) : ∀ n, f n = n.div 3 :=
  fun n => by rw [hf]

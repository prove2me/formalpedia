-- Prove2me | solution 1 for lean_workbook_plus_2315
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:41:04.260115+00:00
-- url     : https://prove2.me/submissions/317bbc93-7a6f-4cb1-8cd7-72d2e0c34458

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℕ → ℝ) (hx : CauchySeq x) :
    ∃ n : ℕ → ℕ, ∀ k : ℕ, ‖x (n (k + 1)) - x (n k)‖ ≤ (1 / 2)^k := by
  refine ⟨fun _ => 0, fun k => ?_⟩
  simp only [sub_self, norm_zero]
  positivity

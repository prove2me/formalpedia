-- Prove2me | solution 1 for lean_workbook_plus_42340
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T03:24:37.193674+00:00
-- url     : https://prove2.me/submissions/890efff8-876e-49a2-b7b9-369c2d09f2c6

import Mathlib.Analysis.Complex.Basic

theorem solution (f : ℝ → ℝ) (hf: ∀ c > 0, f c > 1) : ∀ c > 0, ∃ k > 0, f c > k :=
  fun c hc => ⟨1, one_pos, hf c hc⟩

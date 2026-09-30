-- Prove2me | solution 1 for lean_workbook_plus_74263
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:10:12.229056+00:00
-- url     : https://prove2.me/submissions/f4550408-aa5c-4414-bdd1-f8196407d663

import Mathlib.Analysis.Complex.Basic

theorem solution {a b : ℤ} (h₁ : a ∣ b) : a^3 ∣ b^3 := by
  rcases h₁ with ⟨k, hk⟩
  refine ⟨k^3, ?_⟩
  rw [hk, mul_pow]

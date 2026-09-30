-- Prove2me | solution 1 for lean_workbook_plus_63668
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:41:38.937937+00:00
-- url     : https://prove2.me/submissions/09b7fa96-12aa-4264-8d97-5de1327913f3

import Mathlib.Analysis.Complex.Basic

theorem solution (p : ℕ) (hp : p.Prime) (F : Type*) [Field F]
  [CharP F p] (x : F) : (x + p - 1) ∣ (x^2 + p - 1) := by
  have hp0 : (p : F) = 0 := CharP.cast_eq_zero F p
  rw [hp0]
  exact ⟨x + 1, by ring⟩

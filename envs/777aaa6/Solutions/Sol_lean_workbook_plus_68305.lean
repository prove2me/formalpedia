-- Prove2me | solution 1 for lean_workbook_plus_68305
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:33:49.791711+00:00
-- url     : https://prove2.me/submissions/5858c8ef-1bf6-47f2-8205-829e393f03a8

import Mathlib.Analysis.Complex.Basic

theorem solution (p : ℕ) (hp : p.Prime) (h : p ≡ 1 [ZMOD 4]) : ∃ a : ℕ, a < p ∧ a^2 + 1 ∣ p :=
  ⟨0, hp.pos, by simp⟩

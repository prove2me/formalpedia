-- Prove2me | solution 1 for lean_workbook_plus_37433
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T03:23:12.149843+00:00
-- url     : https://prove2.me/submissions/1fa3104d-fdf8-4a34-ae25-264a6a3e8a60

import Mathlib.Analysis.Complex.Basic

theorem solution (p : ℕ) (hp : p.Prime) (hp1 : p ≡ 1 [ZMOD 4]) : (∃ x : ZMod p, x^2 = 1) ↔ ∃ x : ZMod p, x = 1 ∨ x = -1 := by
  constructor
  · intro _
    exact ⟨1, Or.inl rfl⟩
  · intro _
    exact ⟨1, one_pow 2⟩

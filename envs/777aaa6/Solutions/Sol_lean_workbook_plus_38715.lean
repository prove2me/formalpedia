-- Prove2me | solution 1 for lean_workbook_plus_38715
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:13:44.919929+00:00
-- url     : https://prove2.me/submissions/eaee826d-ed84-4338-ae4d-24f90cac9ef0

import Mathlib.Analysis.Complex.Basic

theorem solution (x y : ℝ) : (y = -1/2 * x + 2 ∧ y = 2 * x) ↔ (x = 4/5 ∧ y = 8/5) := by
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    constructor <;> linarith

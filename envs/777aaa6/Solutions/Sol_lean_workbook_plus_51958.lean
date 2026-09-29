-- Prove2me | solution 1 for lean_workbook_plus_51958
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:41:22.648406+00:00
-- url     : https://prove2.me/submissions/150554cf-8bd9-45aa-b020-b8aea8df2a34

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (w x y z : ℕ)
  (h₀ : w ≡ x [ZMOD 11])
  (h₁ : x ≡ y [ZMOD 11])
  (h₂ : y ≡ z [ZMOD 11]) :
  w ≡ z [ZMOD 11] := by
  (intros; simp only [Int.ModEq, Nat.ModEq] at *; omega)

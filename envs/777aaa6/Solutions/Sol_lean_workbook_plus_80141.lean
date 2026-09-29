-- Prove2me | solution 1 for lean_workbook_plus_80141
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:52:32.981869+00:00
-- url     : https://prove2.me/submissions/f9723003-ca99-4cc1-ac58-57db31fbda2c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {X Y : Type*} (f : X → Y) : Function.Surjective f ↔ ∀ y : Y, ∃ x : X, f x = y := by
  rfl

-- Prove2me | solution 1 for lean_workbook_plus_32839
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:17:20.153087+00:00
-- url     : https://prove2.me/submissions/88815af8-631b-499b-87bb-12cbbb5fd411

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {X Y : Type*} (f : X → Y) : Function.Surjective f ↔ ∀ y, ∃ x, f x = y := by
  rfl

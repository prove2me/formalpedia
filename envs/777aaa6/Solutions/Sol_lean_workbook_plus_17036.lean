-- Prove2me | solution 1 for lean_workbook_plus_17036
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:44:23.921795+00:00
-- url     : https://prove2.me/submissions/d757ae55-a322-46ac-9294-a7e9f62863cc

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℤ → ℤ) (hf: f = fun x => 0) : ∀ x, f x = 0 := by
  (intros; simp_all)

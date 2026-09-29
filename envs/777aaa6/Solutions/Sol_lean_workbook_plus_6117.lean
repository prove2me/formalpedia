-- Prove2me | solution 1 for lean_workbook_plus_6117
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:33:51.860095+00:00
-- url     : https://prove2.me/submissions/0a59d253-cdb0-46a8-af24-f4661dd9189f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∃ A B : Matrix (Fin 2) (Fin 2) (ZMod 2), A * B - B * A = 1 := by
  decide

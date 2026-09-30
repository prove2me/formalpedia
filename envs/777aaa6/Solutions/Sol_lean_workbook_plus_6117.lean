-- Prove2me | solution 1 for lean_workbook_plus_6117
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T02:57:10.976982+00:00
-- url     : https://prove2.me/submissions/51c0428d-05f8-4eca-94b4-eec97f14bb12

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

theorem solution : ∃ A B : Matrix (Fin 2) (Fin 2) (ZMod 2), A * B - B * A = 1 := by
  exact ⟨![![1, 0], ![1, 1]], ![![1, 1], ![0, 1]], by decide⟩

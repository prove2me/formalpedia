-- Prove2me | solution 1 for lean_workbook_plus_62336
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:18:45.016985+00:00
-- url     : https://prove2.me/submissions/b309152d-3714-41a8-b0e9-2adef6047bdc

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {n : ℕ} (p e : Fin n → ℝ) (hp : ∑ i, p i = 1) : ∃ k, ∑ i, p i * e i = k := by
  norm_num

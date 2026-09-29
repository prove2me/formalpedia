-- Prove2me | solution 1 for lean_workbook_plus_48724
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:04:28.530256+00:00
-- url     : https://prove2.me/submissions/0c9dc383-3cf4-457b-9f3e-e1923febbe86

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution :
  ∀ n ∈ Finset.range 64, 3^16 ≡ 1 [ZMOD 64] := by
  decide

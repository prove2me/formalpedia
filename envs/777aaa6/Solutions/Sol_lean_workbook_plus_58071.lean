-- Prove2me | solution 1 for lean_workbook_plus_58071
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:41:35.789796+00:00
-- url     : https://prove2.me/submissions/a6a77f42-1b06-4aed-832d-01fc608a041a

import Mathlib.Analysis.Complex.Basic

theorem solution : 2 ^ (2017 - 1) ≡ 1 [ZMOD 2017] := by
  decide +kernel

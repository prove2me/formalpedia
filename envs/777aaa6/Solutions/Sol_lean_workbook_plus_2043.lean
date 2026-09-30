-- Prove2me | solution 1 for lean_workbook_plus_2043
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:56:19.388213+00:00
-- url     : https://prove2.me/submissions/07ada7b3-f002-46b6-b5f2-5f2b95fddfba

import Mathlib.Analysis.Complex.Basic

theorem solution : 56^6053 ≡ 56^53 [MOD 1000] := by
  decide +kernel

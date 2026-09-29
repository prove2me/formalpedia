-- Prove2me | Theorems.Thm_lean_workbook_plus_50001
-- name    : lean_workbook_plus_50001
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/8133c97e-a315-4e75-8d83-eea00a79d8b7
-- statement:
--   so S $ =(2^4-1)+2(3^4-2^4)+3(4^4-3^4)+4(5^4-4^4)+5(6^4-5^4)+6(2006-6^4)$ $ S=9781$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50001  (s : ℝ)
  (h₀ : s = (2^4 - 1) + 2 * (3^4 - 2^4) + 3 * (4^4 - 3^4) + 4 * (5^4 - 4^4) + 5 * (6^4 - 5^4) + 6 * (2006 - 6^4)) :
  s = 9781   :=  by sorry

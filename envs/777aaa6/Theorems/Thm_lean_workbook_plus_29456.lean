-- Prove2me | Theorems.Thm_lean_workbook_plus_29456
-- name    : lean_workbook_plus_29456
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/4b1ff3db-76bc-4e00-adfa-076a4ed651d5
-- statement:
--   $\log_3(90-3^4)\log_2(76-44)\log_6(1421-5^3)=\boxed{40}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29456 : Real.logb 3 (90 - 3^4) * Real.logb 2 (76 - 44) * Real.logb 6 (1421 - 5^3) = 40   :=  by sorry

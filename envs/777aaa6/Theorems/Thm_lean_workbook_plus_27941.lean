-- Prove2me | Theorems.Thm_lean_workbook_plus_27941
-- name    : lean_workbook_plus_27941
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/b795429c-3b2b-4d39-9593-cf85710a1b64
-- statement:
--   And ${x^4} + {y^4} + {z^4} \ge \frac{{{{(x + y + z)}^4}}}{{27}}$ (Cauchy-Schwartz)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27941 (x y z : ℝ) : x ^ 4 + y ^ 4 + z ^ 4 ≥ (x + y + z) ^ 4 / 27   :=  by sorry

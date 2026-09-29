-- Prove2me | Theorems.Thm_lean_workbook_plus_72012
-- name    : lean_workbook_plus_72012
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/1fda4847-486b-49e5-b105-2477d79b18e1
-- statement:
--   Let $ a>b>0$ and $a^5 + b^5 =a-b.$ Prove that $$a^4 +2b^4 <1.$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72012 {a b : ℝ} (h1 : a > b) (h2 : b > 0) (h3 : a^5 + b^5 = a - b) : a^4 + 2 * b^4 < 1   :=  by sorry

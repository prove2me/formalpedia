-- Prove2me | Theorems.Thm_lean_workbook_plus_64376
-- name    : lean_workbook_plus_64376
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/88e2f364-46f4-4dd3-b800-81249108dd50
-- statement:
--   Prove that if $ a>b>0$ and $ a^5+b^5=a-b$ then $ a^4+b^4<1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64376 {a b : ℝ} (h1 : a > b) (h2 : b > 0) (h3 : a^5 + b^5 = a - b) : a^4 + b^4 < 1   :=  by sorry

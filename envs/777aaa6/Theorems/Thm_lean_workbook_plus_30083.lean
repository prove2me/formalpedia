-- Prove2me | Theorems.Thm_lean_workbook_plus_30083
-- name    : lean_workbook_plus_30083
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/6cd37fc8-6839-4c45-8418-8780b4a7dcc3
-- statement:
--   (d) If $ x \neq 0$ then $ 1/(1/x) = x$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30083 (x : ℝ) (hx : x ≠ 0) : 1 / (1 / x) = x   :=  by sorry

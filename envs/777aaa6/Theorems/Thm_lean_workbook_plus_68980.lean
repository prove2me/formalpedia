-- Prove2me | Theorems.Thm_lean_workbook_plus_68980
-- name    : lean_workbook_plus_68980
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/fdf4ccdf-45da-4efb-97cb-133aa69c68d9
-- statement:
--   Prove that $\frac{n}{n+1} > \frac{n-1}{n}$ for any natural number $n \geq 2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68980 (n : ℕ) (_hn : 2 ≤ n) : (n : ℝ) / (n + 1) > (n - 1) / n   :=  by sorry

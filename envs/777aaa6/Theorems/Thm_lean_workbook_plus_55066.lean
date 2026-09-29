-- Prove2me | Theorems.Thm_lean_workbook_plus_55066
-- name    : lean_workbook_plus_55066
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/3b6eb219-607d-45c1-9b12-86312ca4f516
-- statement:
--   The partial fraction decomposition of $\dfrac{1}{n(n+1)(n+2)(n+3)}$ is $\dfrac{1}{6n} -\dfrac{1}{6(n+3)} - \dfrac{1}{2(n+1)} + \dfrac{1}{2(n+2)}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55066 (n : ℕ) (hn : n ≠ 0) : (1 : ℝ) / (n * (n + 1) * (n + 2) * (n + 3)) = 1 / (6 * n) - 1 / (6 * (n + 3)) - 1 / (2 * (n + 1)) + 1 / (2 * (n + 2))   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_31657
-- name    : lean_workbook_plus_31657
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/aed3db0d-4e66-46e1-9cb9-17ed4c9b81f4
-- statement:
--   Verify that from CBS inequality $ x^2\le 1\implies - 1\le x\le 1\implies 0\le 1 - x\le 2$ . Therefore $ |1 - x| = 1 - x$ and we get $ 1 - x^2\le 2(1 - x)\iff (x - 1)^2\ge 0$ , which is obviously true.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31657  (x : ℝ) (hx : x^2 ≤ 1) : 1 - x^2 ≤ 2 * (1 - x)   :=  by sorry

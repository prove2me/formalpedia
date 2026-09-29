-- Prove2me | Theorems.Thm_lean_workbook_plus_40716
-- name    : lean_workbook_plus_40716
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/2c08802b-04d2-4818-9eaa-0ae6596e09bb
-- statement:
--   We just have to prove that $6(a^2+b^2) \ge (3a^2+3b^2+(a+b)^2+2ab)$ which is equivalent to $2a^2+2b^2 \ge 4ab$ which is true.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40716  (a b : ℝ) :
  2 * a^2 + 2 * b^2 ≥ 4 * a * b   :=  by sorry

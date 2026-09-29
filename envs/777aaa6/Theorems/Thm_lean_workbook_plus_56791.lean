-- Prove2me | Theorems.Thm_lean_workbook_plus_56791
-- name    : lean_workbook_plus_56791
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/2cb05223-1b87-4031-95bd-18327d64a3a2
-- statement:
--   From schur inequality we have : $ (a+b+c)^3+9abc \ge 4(a+b+c)(ab+bc+ca) $ , so if $ a+b+c=1 $ we get \n$ 4(ab+bc+ca)-9abc \le 1 $ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56791 : ∀ a b c : ℝ, a + b + c = 1 → 4 * (a * b + b * c + c * a) - 9 * a * b * c ≤ 1   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_77425
-- name    : lean_workbook_plus_77425
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/5de0de65-fa4d-4f36-ad3c-350db5c64fe2
-- statement:
--   $x_1x_2x_3x_4x_5x_6(x_1+x_2+x_3+x_4+x_5+x_6+n-6)=100n.$ One solution is $x_1=50, n=49,x_2=x_3=...=x_{49}=1.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77425 (n : ℕ) (x : ℕ → ℕ) (hx: x 1 = 50) (hn: n = 49) (hx2: ∀ i, 2 <= i ∧ i <= 49 → x i = 1): x 1 * x 2 * x 3 * x 4 * x 5 * x 6 * (x 1 + x 2 + x 3 + x 4 + x 5 + x 6 + n - 6) = 100 * n   :=  by sorry

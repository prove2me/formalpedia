-- Prove2me | Theorems.Thm_lean_workbook_plus_4693
-- name    : lean_workbook_plus_4693
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/b6d219a9-ce2f-491a-865c-cec237dd4832
-- statement:
--   Show that for $n\geq 2$ , the number of digits in the block of repeating digits in the decimal expansion of $\frac{1}{3^n}$ is $3^{n-2}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4693 (n : ℕ) (hn : 2 ≤ n) : (Nat.digits 10 (1 / 3 ^ n)).length = 3 ^ (n - 2)   :=  by sorry

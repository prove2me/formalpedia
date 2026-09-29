-- Prove2me | Theorems.Thm_lean_workbook_plus_67181
-- name    : lean_workbook_plus_67181
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/6fcea49b-6c67-4480-b16f-c004207a6dff
-- statement:
--   For a positive integer $ N $ we denote by $ S(N) $ the sum of its digits. \n\n Then, $ S(10^{2n}+10^n+1)=3\Rightarrow 10^{2n}+10^n+1 $ is divisible by $ 3 $ , with $ n\in\mathbb N $ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67181 (n : ℕ) : (10^(2*n) + 10^n + 1) % 3 = 0   :=  by sorry

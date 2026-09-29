-- Prove2me | Theorems.Thm_lean_workbook_plus_77235
-- name    : lean_workbook_plus_77235
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/b6ea4c11-2507-4565-83cf-a0fbafed3622
-- statement:
--   If $2^{22}=4,194,304$ find the sum $1*2+2*2^2+3*2^3+...+21*2^{21}=\displaystyle\sum_{n=1}^{21}{n*2^n}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77235 (h₁ : 2^22 = 4194304) : ∑ n in Finset.Icc 1 21, (n * 2^n) = 4194303   :=  by sorry

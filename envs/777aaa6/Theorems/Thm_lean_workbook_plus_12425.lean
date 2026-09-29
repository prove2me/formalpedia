-- Prove2me | Theorems.Thm_lean_workbook_plus_12425
-- name    : lean_workbook_plus_12425
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/42ed25be-772c-40d3-a128-150684739ded
-- statement:
--   If a number has to be divisible by $3$ , But it can't be divisible by $6$ , Then it can't be divisible by $2$ If it was divisible by $2$ and $3$ , that automatically implies it is divisible by $6$ due to the divisibility rule of six. Therefore, being divisible by $3$ and not $6$ is the same as being divisible by $3$ but not $2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12425  (n : ℕ)
  (h₀ : 3 ∣ n)
  (h₁ : ¬ 6 ∣ n) :
  ¬ 2 ∣ n   :=  by sorry

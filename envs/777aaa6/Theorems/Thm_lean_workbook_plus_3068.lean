-- Prove2me | Theorems.Thm_lean_workbook_plus_3068
-- name    : lean_workbook_plus_3068
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/9d5bcb35-a26a-4f7a-96c8-d056c52776dd
-- statement:
--   (x_1 - x_2)^2 \geq 0 \Rightarrow x_1 \cdot x_2 \leq (x_1^2 + x_2^2)/2 . Then, $ f \leq \sqrt{x_1^2 + x_2^2}/2$ which can be made arbitrarily small as $ (x_1,x_2) \rightarrow 0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3068  (x y : ℝ) :
  (x - y)^2 ≥ 0 → x * y ≤ (x^2 + y^2) / 2   :=  by sorry

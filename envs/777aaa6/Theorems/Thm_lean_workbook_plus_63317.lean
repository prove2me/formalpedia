-- Prove2me | Theorems.Thm_lean_workbook_plus_63317
-- name    : lean_workbook_plus_63317
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/2c4e364d-c577-4494-b19b-52dd32f7fa37
-- statement:
--   Originally, each person had to pay $\$\frac{900}{x}$ (x is the number of people). Then, five people left, so each person then had to pay $\$\frac{900}{x-5}$ . We are given that $\$\frac{900}{x-5}$ is 2.5 greater than $\$\frac{900}{x}$ . So, $\frac{900}{x}=\frac{900}{x-5}-2.5$ . Solving, we get $x=-40,45$ , but we want the positive, so $x=45$ . Since we want the number of people, and $x$ is the number of people, we find that the number of people that had to share the price was $\boxed{45}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63317  (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : 900 / (x - 5) = 900 / x + 2.5) :
  x = 45   :=  by sorry

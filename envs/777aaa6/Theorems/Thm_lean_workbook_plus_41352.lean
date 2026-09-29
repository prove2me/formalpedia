-- Prove2me | Theorems.Thm_lean_workbook_plus_41352
-- name    : lean_workbook_plus_41352
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/2c8bcfe1-d21e-4f33-b809-9b659eea5d36
-- statement:
--   Using proportions, we get that $\frac{4}{15}=\frac{x}{60}$ , where $x$ is the number of bass that C.A can catch in an hour. This comes out to $15x=4\times60$ , which simplifies to $15x=240$ . Divide by 15 to get $x=16$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41352  (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : 15 / 4 = 60 / x) :
  x = 16   :=  by sorry

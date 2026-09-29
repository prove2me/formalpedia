-- Prove2me | Theorems.Thm_lean_workbook_plus_33359
-- name    : lean_workbook_plus_33359
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/f447fbc9-e1d5-44b2-8b0c-dca18884e177
-- statement:
--   $60\\%$ of $x$ is just $0.6x$. We know that $0.6x = 36$. Dividing both sides by $0.6$, we get $x = \\dfrac{36}{0.6} = \\boxed{60}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33359  (x : ℝ)
  (h₀ : 0.6 * x = 36) :
  x = 60   :=  by sorry

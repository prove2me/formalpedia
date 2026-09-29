-- Prove2me | Theorems.Thm_lean_workbook_plus_70358
-- name    : lean_workbook_plus_70358
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/00c718f5-8383-4276-8fdc-6b730da71bbb
-- statement:
--   Multiply the first equation by $5$ and the second by $2$ . \n\n $$125x+50y=3475$$ \n$$20x+50y = 1480$$ Subtract: \n\n $$95x=1995 \implies x=19$$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70358  (x y : ℝ)
  (h₀ : 125 * x + 50 * y = 3475)
  (h₁ : 20 * x + 50 * y = 1480) :
  x = 19   :=  by sorry

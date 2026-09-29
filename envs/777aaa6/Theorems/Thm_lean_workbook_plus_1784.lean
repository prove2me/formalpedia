-- Prove2me | Theorems.Thm_lean_workbook_plus_1784
-- name    : lean_workbook_plus_1784
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/aff324ff-7a2f-4198-871f-63516cd64c95
-- statement:
--   Solution without Geometric Formula\n$$\frac{7}{1} + \frac{7}{2} + \frac{7}{4} + \frac{7}{8}\cdots= x $$ We divide everything by 2: \n $$\frac{7}{2} + \frac{7}{4} + \frac{7}{8} + \frac{7}{16}\cdots= \frac{x}{2} $$ We substitute the original equation in: \n $$x-7=\frac{x}{2}$$ $$\frac{x}{2}=7$$ Therefore, $\boxed{x=14}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1784  (x : ℝ)
  (h₀ : ∑' k : ℕ, (7 / (2^k)) = x) :
  x = 14   :=  by sorry

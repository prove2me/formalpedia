-- Prove2me | Theorems.Thm_lean_workbook_plus_17792
-- name    : lean_workbook_plus_17792
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/7bae5e6d-7fd5-42f7-ad71-8c11098fa5c0
-- statement:
--   It works because: \n\n $$\frac {x+y}{2} \ge \sqrt {xy}$$ \n $$x+y \ge 2\sqrt {xy}$$ \n $$x^2+y^2+2xy \ge 4xy$$ \n $$(x-y)^2 \ge 0$$ \n\n which is true by the trivial inequality. The equality happens at $x=y$ . We can not have $x,y$ be negative otherwise $\sqrt {xy}$ is not real.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17792  (x y : ℝ)
  (h₀ : 0 ≤ x ∧ 0 ≤ y) :
  (x + y) / 2 ≥ Real.sqrt (x * y) ↔ x^2 + y^2 + 2 * (x * y) ≥ 4 * (x * y)   :=  by sorry

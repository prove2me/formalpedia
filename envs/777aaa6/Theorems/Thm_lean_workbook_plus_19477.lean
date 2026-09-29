-- Prove2me | Theorems.Thm_lean_workbook_plus_19477
-- name    : lean_workbook_plus_19477
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/e717ce7d-8088-479a-b737-7e5e6a18d240
-- statement:
--   Rewrite as: $a^4-a^3-a+1 \ge 0$ Yeah. $3(a^4+a^2+1) \ge (a^2+a+1)^2 $ $\iff a^4-a^3-a+1 \ge 0$ $\iff (a-1)^{2}( a^2 +a +1) \ge 0$ $ \Leftarrow a^2 +a +1=(a+\frac{1}{2})^2+\frac{3}{4}> 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19477  (a : ℝ) :
  a^4 - a^3 - a + 1 ≥ 0   :=  by sorry

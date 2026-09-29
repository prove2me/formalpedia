-- Prove2me | Theorems.Thm_lean_workbook_plus_52853
-- name    : lean_workbook_plus_52853
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/2ed369c5-3d05-4442-9f0a-8aa9d204a170
-- statement:
--   Since $t^2-2t+1 = (t-1)^2 \ge 0$ , we have that $2t \le 1+t^2$ , or equivalently $\dfrac{t}{1+t^2} \le \dfrac{1}{2}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52853  (t : ℝ) :
  2 * t ≤ 1 + t^2   :=  by sorry

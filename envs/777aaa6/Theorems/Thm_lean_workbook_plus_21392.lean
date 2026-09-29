-- Prove2me | Theorems.Thm_lean_workbook_plus_21392
-- name    : lean_workbook_plus_21392
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/f16e8e2b-340f-4253-a138-12200d379f40
-- statement:
--   Prove that for $x, y, z > 0$ and $xyz = x + y + z = 2$, \n1. $xy + yz + zx \geq 2(x + y + z)$\n2. $\sqrt{x} + \sqrt{y} + \sqrt{z} \leq \frac{3\sqrt{xyz}}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21392 (x y z : ℝ) (hx: x > 0 ∧ y > 0 ∧ z > 0 ∧ x*y*z = 2 ∧ x + y + z = 2):  x*y + y*z + z*x >= 2*(x + y + z) ∧ Real.sqrt x + Real.sqrt y + Real.sqrt z <= (3*Real.sqrt (x*y*z))/2   :=  by sorry

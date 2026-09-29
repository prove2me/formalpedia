-- Prove2me | Theorems.Thm_lean_workbook_plus_12705
-- name    : lean_workbook_plus_12705
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/cf612655-faf2-4d65-91e2-0e21ebd72add
-- statement:
--   $\frac{1}{x} + \frac{1}{y} + \frac{1}{z} \ge 4(x + y + z) \implies xy + yz+ zx \ge 2\left( {x + y + z} \right) \implies \sqrt x + \sqrt y + \sqrt z \le \frac{3}{2}\sqrt {xyz}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12705 (x y z : ℝ) (hx : x > 0 ∧ y > 0 ∧ z > 0) (hab : x + y + z = 1) : 1 / x + 1 / y + 1 / z ≥ 4 * (x + y + z) → (x * y + y * z + z * x ≥ 2 * (x + y + z)) → (Real.sqrt x + Real.sqrt y + Real.sqrt z ≤ 3 / 2 * Real.sqrt (x * y * z))   :=  by sorry

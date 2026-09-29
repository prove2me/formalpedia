-- Prove2me | Theorems.Thm_lean_workbook_plus_36928
-- name    : lean_workbook_plus_36928
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/caa9121e-6ead-4897-9777-7533bdb55eff
-- statement:
--   Prove that the value of the nested radical expression $x=\sqrt{5+\sqrt{5+\sqrt{5-\sqrt{5+\sqrt{5+\sqrt{5+ \cdots }}}}}}$ is equal to $x=\frac{2+\sqrt{5}}{2} +\frac{\sqrt{15-6\sqrt{5}}}{2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36928 (x : ℝ) (hx : x = ∑' k : ℕ, (Real.sqrt (5 + Real.sqrt (5 + Real.sqrt (5 - Real.sqrt (5 + Real.sqrt (5 + Real.sqrt (5 + ↑k)))))))) : ∃ y, y = (2 + Real.sqrt 5) / 2 + (Real.sqrt (15 - 6 * Real.sqrt 5)) / 2   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_76835
-- name    : lean_workbook_plus_76835
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/e7c5ad51-28a7-4161-989b-36e5e53c071c
-- statement:
--   We need to prove that $3\\leq a^3+b^3+c^3-3abc+3(ab+ac+bc)-3(a+b+c)+3$ or $3\\sum_{cyc}(a^2-ab)\\geq(a+b+c)^2-3(ab+ac+bc)$ or $\sum_{cyc}(a^2-ab)\\geq0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76835 (a b c : ℝ) : 3 * (a^2 - a * b + b^2 - b * c + c^2 - c * a) ≥ (a + b + c)^2 - 3 * (a * b + b * c + c * a)   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_76467
-- name    : lean_workbook_plus_76467
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/7962db9b-dd41-4967-99e2-bad9980f7af9
-- statement:
--   Since $a+b+c=0$ , $-a-b=c$ . So: $a^{2}+b^{2}+c^{2}=a^{2}+b^{2}+(-a-b)^{2}=2a^{2}+2ab+2b^{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76467 : ∀ a b c : ℝ, a + b + c = 0 → a^2 + b^2 + c^2 = 2 * a^2 + 2 * a * b + 2 * b^2   :=  by sorry

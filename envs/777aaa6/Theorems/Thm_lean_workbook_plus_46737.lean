-- Prove2me | Theorems.Thm_lean_workbook_plus_46737
-- name    : lean_workbook_plus_46737
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/1eebc412-a889-44b3-959c-b9322d222a07
-- statement:
--   Prove that $ \left(a^{2}+b^{2}+c^{2}\right)^{2}\geq\left(a\left(b^{2}-bc+c^{2}\right)+b\left(c^{2}-ca+a^{2}\right)+c\left(a^{2}-ab+b^{2}\right)\right)\left(a+b+c\right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46737 (a b c : ℝ) :
  (a^2 + b^2 + c^2)^2 ≥ (a * (b^2 - b * c + c^2) + b * (c^2 - c * a + a^2) + c * (a^2 - a * b + b^2)) * (a + b + c)   :=  by sorry

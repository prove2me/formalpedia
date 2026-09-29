-- Prove2me | Theorems.Thm_lean_workbook_plus_46159
-- name    : lean_workbook_plus_46159
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/c0cc28dd-7263-4c01-a539-81fa022bbe7d
-- statement:
--   Prove that $\frac{a}{1-r} \cdot \frac{a}{1+r}=\frac{a^2}{1-r^2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46159  (a r : ℂ) :
  (a / (1 - r)) * (a / (1 + r)) = a^2 / (1 - r^2)   :=  by sorry

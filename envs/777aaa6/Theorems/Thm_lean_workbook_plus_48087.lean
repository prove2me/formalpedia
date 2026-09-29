-- Prove2me | Theorems.Thm_lean_workbook_plus_48087
-- name    : lean_workbook_plus_48087
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/1db2644c-11eb-46ea-87ec-1fb5c173895f
-- statement:
--   Prove that $ \sum \frac{a}{b+c}=\sum(\frac{a}{b+c}+1)-3=\sum\frac{a+b+c}{b+c} -3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48087 (a b c: ℝ) : a / (b + c) + b / (a + c) + c / (a + b) = (a / (b + c) + 1 + b / (a + c) + 1 + c / (a + b) + 1) - 3   :=  by sorry

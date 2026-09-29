-- Prove2me | Theorems.Thm_lean_workbook_plus_22243
-- name    : lean_workbook_plus_22243
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/8abdd4ee-1894-4eec-9112-4249d742b658
-- statement:
--   Calculate $\left(\sqrt{\left(17-\sqrt{2}\right)\left(17+\sqrt{2}\right)}-10\right)\left(\sqrt{\left(17-\sqrt{2}\right)\left(17+\sqrt{2}\right)}+10\right)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22243 (h : 0 < √2) : (Real.sqrt ((17 - √2) * (17 + √2)) - 10) * (Real.sqrt ((17 - √2) * (17 + √2)) + 10) = 187   :=  by sorry

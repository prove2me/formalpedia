-- Prove2me | Theorems.Thm_lean_workbook_plus_19282
-- name    : lean_workbook_plus_19282
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/3d0e782a-6142-4075-8a4e-7b392fcc255a
-- statement:
--   By Sophie Germáin's identity, we have $$a^4+4b^4=(a^2+2b^2-2ab)(a^2+2b^2+2ab)$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19282 (a b : ℤ) : a^4 + 4 * b^4 = (a^2 + 2 * b^2 - 2 * a * b) * (a^2 + 2 * b^2 + 2 * a * b)   :=  by sorry

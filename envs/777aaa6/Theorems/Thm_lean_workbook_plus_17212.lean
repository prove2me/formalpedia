-- Prove2me | Theorems.Thm_lean_workbook_plus_17212
-- name    : lean_workbook_plus_17212
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/56d8a327-222c-49cb-ad60-15b8720d78f9
-- statement:
--   Equivalent to $(3-q).\left (1-\dfrac{3-q}{\sqrt{q^2-8q+18}+\sqrt{9-2q}}\right )\geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17212 : ∀ q, (3 - q) * (1 - (3 - q) / (Real.sqrt (q ^ 2 - 8 * q + 18) + Real.sqrt (9 - 2 * q))) ≥ 0   :=  by sorry

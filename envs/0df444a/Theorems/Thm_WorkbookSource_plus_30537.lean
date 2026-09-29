-- Prove2me | Theorems.Thm_WorkbookSource_plus_30537
-- name    : WorkbookSource.plus_30537
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:03:03.60223+00:00
-- url     : https://prove2.me/theorems/eec3d9e2-83ba-46ae-8ad7-2610771f9133
-- title:
--   A sharp bound for three squared differences
-- statement:
--   Let $ a,\ b,\ c$ be real numbers. Prove that $ (b-a)^{2}+(c-b)^{2}+(c-a-2)^{2}\ge\frac{4}{3}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_30537` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_30537; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.plus_30537 : ∀ a b c : ℝ, (b - a) ^ 2 + (c - b) ^ 2 + (c - a - 2) ^ 2 ≥ 4 / 3   :=  by sorry

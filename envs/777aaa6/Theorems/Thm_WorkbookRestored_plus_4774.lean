-- Prove2me | Theorems.Thm_WorkbookRestored_plus_4774
-- name    : WorkbookRestored.plus_4774
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:29:36.757391+00:00
-- url     : https://prove2.me/theorems/6f0dd928-750e-4fef-b812-8e9bd6c05933
-- title:
--   Lean-Workbook Plus 4774: Trigonometric identity
-- statement:
--   For real $b,c,\alpha$ with $\alpha\ne0,\pi$, the area-expression identity is $16(\tfrac12bc\sin\alpha)^2=4b^2c^2\sin^2\alpha$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_4774` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/26898daa-356f-4db4-a007-4d08442b8207); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_4774; immutable original Prove2Me node 26898daa-356f-4db4-a007-4d08442b8207

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_4774 : ∀ b c : ℝ, ∀ α : ℝ, (α ≠ 0 ∧ α ≠ π) → 16 * (1 / 2 * b * c * Real.sin α) ^ 2 = 4 * b ^ 2 * c ^ 2 * (Real.sin α) ^ 2   :=  by sorry

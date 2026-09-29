-- Prove2me | Theorems.Thm_WorkbookRestored_plus_16072
-- name    : WorkbookRestored.plus_16072
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:30:46.208139+00:00
-- url     : https://prove2.me/theorems/ba9cf407-35ac-4459-8e89-102139027845
-- title:
--   Lean-Workbook Plus 16072: Trigonometric identity
-- statement:
--   Prove the identity \(\cos 2kx \cdot \cos x = \frac {1}{2}\left[\cos \left(2k - 1\right)x + \cos \left(2k + 1\right)x\right]\).
--
--   Source: Lean-Workbook row `lean_workbook_plus_16072` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/ef3859c8-cff2-4b55-8c31-0f66ee41a3b0); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_16072; immutable original Prove2Me node ef3859c8-cff2-4b55-8c31-0f66ee41a3b0

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_16072 : ∀ k x, Real.cos (2 * k * x) * Real.cos x = (1 / 2) * (Real.cos ((2 * k - 1) * x) + Real.cos ((2 * k + 1) * x))   :=  by sorry

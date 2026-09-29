-- Prove2me | Theorems.Thm_WorkbookRestored_plus_72417
-- name    : WorkbookRestored.plus_72417
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:17:54.758052+00:00
-- url     : https://prove2.me/theorems/8aec87ed-9ea6-4757-90d8-bdcc3e2dbd8a
-- title:
--   Lean-Workbook Plus 72417: Trigonometric identity
-- statement:
--   $ \cos(2\pi/7)+\cos(4\pi/7)+\cos(6\pi/7) = -(cos(\frac{\pi}{7})+cos(\frac{3 \pi}{7})+cos(\frac{5 \pi}{7}))$
--
--   Source: Lean-Workbook row `lean_workbook_plus_72417` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/381c6b0e-8ef5-42e8-a89a-766cb0a31e75); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_72417; immutable original Prove2Me node 381c6b0e-8ef5-42e8-a89a-766cb0a31e75

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_72417 :  Real.cos (2 * π / 7) + Real.cos (4 * π / 7) + Real.cos (6 * π / 7) = - (Real.cos (π / 7) + Real.cos (3 * π / 7) + Real.cos (5 * π / 7))   :=  by sorry

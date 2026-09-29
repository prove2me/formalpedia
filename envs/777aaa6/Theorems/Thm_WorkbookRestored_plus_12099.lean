-- Prove2me | Theorems.Thm_WorkbookRestored_plus_12099
-- name    : WorkbookRestored.plus_12099
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:30:18.466416+00:00
-- url     : https://prove2.me/theorems/3c636572-92e2-4e07-a47d-13a1d29c770e
-- title:
--   Lean-Workbook Plus 12099: Trigonometric identity
-- statement:
--   The complementary-angle identity gives $\sin 50^\circ=\cos 40^\circ$. The Lean statement writes these angles in radians as $50\pi/180$ and $40\pi/180$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_12099` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/8c1ca9c2-98bd-4ae2-b3d2-09d4b2ea06ff); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_12099; immutable original Prove2Me node 8c1ca9c2-98bd-4ae2-b3d2-09d4b2ea06ff

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_12099 (x : ℝ) : sin (50 * π / 180) = cos (40 * π / 180)   :=  by sorry

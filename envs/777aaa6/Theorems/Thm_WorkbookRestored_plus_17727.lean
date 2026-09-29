-- Prove2me | Theorems.Thm_WorkbookRestored_plus_17727
-- name    : WorkbookRestored.plus_17727
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:31:01.09842+00:00
-- url     : https://prove2.me/theorems/8035ce4f-e9fa-457c-9862-c82cc878eeed
-- title:
--   Lean-Workbook Plus 17727: Trigonometric identity
-- statement:
--   The complementary-angle identity gives $\sin36^\circ=\cos54^\circ$. The Lean statement uses the radian arguments $36\pi/180$ and $54\pi/180$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_17727` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/9a0db0fc-f991-4841-82ee-d86dd0f9a4af); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_17727; immutable original Prove2Me node 9a0db0fc-f991-4841-82ee-d86dd0f9a4af

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_17727 : Real.sin (36 * π / 180) = Real.cos (54 * π / 180)   :=  by sorry

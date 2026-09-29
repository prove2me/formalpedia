-- Prove2me | Theorems.Thm_WorkbookRestored_plus_18380
-- name    : WorkbookRestored.plus_18380
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:31:09.799116+00:00
-- url     : https://prove2.me/theorems/3ad49ec6-9159-4395-9b7d-d5e1e7c433a4
-- title:
--   Lean-Workbook Plus 18380: Trigonometric inequality
-- statement:
--   If $a,b$ are real and $a^2+b^2=1$, then $a\sin x+b\cos x\le1$ for every real $x$. This proves the upper-bound component of the source maximum-value statement.
--
--   Source: Lean-Workbook row `lean_workbook_plus_18380` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/f634a1cb-446e-4e53-ba41-35236b0bb682); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_18380; immutable original Prove2Me node f634a1cb-446e-4e53-ba41-35236b0bb682

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_18380 (a b : ℝ) (x : ℝ) (h : a^2 + b^2 = 1) :
  a * Real.sin x + b * Real.cos x ≤ 1   :=  by sorry

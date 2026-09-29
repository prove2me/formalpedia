-- Prove2me | Theorems.Thm_WorkbookRestored_plus_47972
-- name    : WorkbookRestored.plus_47972
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:03:30.852406+00:00
-- url     : https://prove2.me/theorems/c40679fb-6107-4ad5-9f6f-dafa75dff8cd
-- title:
--   Lean-Workbook Plus 47972: Trigonometric inequality
-- statement:
--   If $A,B,C>0$ and $A+B+C=\pi$, then $4\cos(A/2)\cos(B/2)\cos(C/2)\ge\sin(A+B+C)$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_47972` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/ee415506-b41e-4fae-a4b0-b97ef0b535b7); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_47972; immutable original Prove2Me node ee415506-b41e-4fae-a4b0-b97ef0b535b7

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_47972 (A B C : ℝ) (hx: A > 0 ∧ B > 0 ∧ C > 0) (hab : A + B + C = π) : 4 * Real.cos (A / 2) * Real.cos (B / 2) * Real.cos (C / 2) ≥ Real.sin (A + B + C)   :=  by sorry

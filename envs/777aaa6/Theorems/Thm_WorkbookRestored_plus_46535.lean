-- Prove2me | Theorems.Thm_WorkbookRestored_plus_46535
-- name    : WorkbookRestored.plus_46535
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:03:16.700257+00:00
-- url     : https://prove2.me/theorems/7bf29f42-c545-4cf1-ab3e-8a160a35f1d4
-- title:
--   Lean-Workbook Plus 46535: Trigonometric inequality
-- statement:
--   For $0<x<\pi$, $(9x^2\sin^2x+4)/(x\sin x)\ge12$. This is the lower-bound component of the source’s minimum-value problem.
--
--   Source: Lean-Workbook row `lean_workbook_plus_46535` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/3e7d89b6-def1-44be-9d34-782b41d99fa9); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_46535; immutable original Prove2Me node 3e7d89b6-def1-44be-9d34-782b41d99fa9

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_46535 (x : ℝ) (hx : 0 < x ∧ x < π) : (9 * (x ^ 2 * (sin x) ^ 2) + 4) / (x * sin x) ≥ 12   :=  by sorry

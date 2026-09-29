-- Prove2me | Theorems.Thm_WorkbookRestored_plus_24283
-- name    : WorkbookRestored.plus_24283
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:00:25.106032+00:00
-- url     : https://prove2.me/theorems/2cc58644-8e97-4393-8f9b-391db08aa117
-- title:
--   Lean-Workbook Plus 24283: Trigonometric identity
-- statement:
--   If real $A,B,C$ satisfy $A+B+C=\pi$, then $\sin^2A+\sin^2B+\sin^2C=2(1+\cos A\cos B\cos C)$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_24283` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/5ad05c0c-8aed-4228-b836-edbfe3de6664); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_24283; immutable original Prove2Me node 5ad05c0c-8aed-4228-b836-edbfe3de6664

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_24283 (A B C : ℝ) (hx: A + B + C = π) : (sin A)^2 + (sin B)^2 + (sin C)^2 = 2*(1 + cos A * cos B * cos C)   :=  by sorry

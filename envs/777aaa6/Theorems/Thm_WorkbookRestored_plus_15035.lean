-- Prove2me | Theorems.Thm_WorkbookRestored_plus_15035
-- name    : WorkbookRestored.plus_15035
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:30:51.159009+00:00
-- url     : https://prove2.me/theorems/f2d06fbb-4d7b-4d34-b4ad-48fc849d9877
-- title:
--   Lean-Workbook Plus 15035: Trigonometric identity
-- statement:
--   If $2\sin^2\theta=5/7$, then $\sin^2(2\theta)=45/49$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_15035` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/66a80e0e-c405-4afa-bcd7-fe7ee7cb73c7); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_15035; immutable original Prove2Me node 66a80e0e-c405-4afa-bcd7-fe7ee7cb73c7

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_15035 (θ : ℝ) (h : 2 * sin θ ^ 2 = 5/7) : sin (2 * θ) ^ 2 = 45/49   :=  by sorry

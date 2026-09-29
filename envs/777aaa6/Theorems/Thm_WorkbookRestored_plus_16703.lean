-- Prove2me | Theorems.Thm_WorkbookRestored_plus_16703
-- name    : WorkbookRestored.plus_16703
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:30:53.169118+00:00
-- url     : https://prove2.me/theorems/90f228ac-f4cc-4585-ae7a-3e9094b6d447
-- title:
--   Lean-Workbook Plus 16703: Trigonometric inequality
-- statement:
--   For real $a,b,c,y,z$, $(a\sin y+b\cos z+c)^2\le(a^2+b^2+c^2)(\sin^2y+\cos^2z+1^2)$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_16703` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/0a0d6d11-938b-46d9-86aa-a51d9e759fff); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_16703; immutable original Prove2Me node 0a0d6d11-938b-46d9-86aa-a51d9e759fff

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_16703 {a b c : ℝ} {y z : ℝ} : (a * sin y + b * cos z + c) ^ 2 ≤ (a ^ 2 + b ^ 2 + c ^ 2) * (sin y ^ 2 + cos z ^ 2 + 1 ^ 2)   :=  by sorry

-- Prove2me | Theorems.Thm_WorkbookRestored_plus_64837
-- name    : WorkbookRestored.plus_64837
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:08:12.540415+00:00
-- url     : https://prove2.me/theorems/e015055b-70cf-4a06-8e64-99298827ed4a
-- title:
--   Lean-Workbook Plus 64837: A floor inequality for a positive number and its reciprocal
-- statement:
--   For every real $x>0$, $\lfloor x\rfloor+\lfloor 1/x\rfloor\ge1$, with integer-valued floors.
--
--   Source: Lean-Workbook row `lean_workbook_plus_64837` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/93342ceb-12cf-449e-9d6f-6e4ef691beed); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_64837; immutable original Prove2Me node 93342ceb-12cf-449e-9d6f-6e4ef691beed

import Mathlib.Data.Real.Archimedean
open Int

theorem WorkbookRestored.plus_64837 (x : ℝ) (hx : 0 < x) : 1 ≤ floor x + floor (1 / x)   :=  by sorry

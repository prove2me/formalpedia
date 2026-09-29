-- Prove2me | Theorems.Thm_WorkbookRestored_plus_59538
-- name    : WorkbookRestored.plus_59538
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:58:09.757918+00:00
-- url     : https://prove2.me/theorems/639557bf-ec8d-4723-ad60-c55ce46ddf84
-- title:
--   Lean-Workbook Plus 59538: Exact 2-adic valuation of a power sum
-- statement:
--   The largest exponent $e$ for which $2^e$ divides $3^{101}+5^{101}$ is $e=3$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_59538` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/51155ec1-3dda-4c5e-84ce-cf516efd856c); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_59538; immutable original Prove2Me node 51155ec1-3dda-4c5e-84ce-cf516efd856c

import Mathlib.NumberTheory.Padics.PadicVal.Defs

theorem WorkbookRestored.plus_59538 :
  padicValNat 2 (3^101 + 5^101) = 3   :=  by sorry

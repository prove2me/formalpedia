-- Prove2me | Theorems.Thm_WorkbookRestored_plus_51735
-- name    : WorkbookRestored.plus_51735
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:39:54.814159+00:00
-- url     : https://prove2.me/theorems/3c360c56-4226-4572-b405-3f93f7910346
-- title:
--   Nested irrational powers
-- statement:
--   $((\sqrt3)^{\sqrt2})^{\sqrt2}=\sqrt9=3$, with real exponentiation. The formal statement asserts the equality to $\sqrt9$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_51735` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/1a64f6db-dc89-4ca4-8369-c588827165f6); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_51735; immutable original Prove2Me node 1a64f6db-dc89-4ca4-8369-c588827165f6

import Mathlib.Analysis.SpecialFunctions.Pow.Real

theorem WorkbookRestored.plus_51735 : (Real.sqrt 3 ^ (Real.sqrt 2)) ^ (Real.sqrt 2) = Real.sqrt 9   :=  by sorry

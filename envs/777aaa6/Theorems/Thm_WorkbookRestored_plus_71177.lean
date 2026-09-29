-- Prove2me | Theorems.Thm_WorkbookRestored_plus_71177
-- name    : WorkbookRestored.plus_71177
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:17:52.423138+00:00
-- url     : https://prove2.me/theorems/3993f211-85c1-49ce-a142-f1efdca5a585
-- title:
--   Lean-Workbook Plus 71177: Logarithmic inequality
-- statement:
--   There exists a real $x>0$, $x\ne2$, satisfying $\log_2x=x/2$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_71177` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/d35e14e5-8370-475d-a651-f76c1b3db4a0); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_71177; immutable original Prove2Me node d35e14e5-8370-475d-a651-f76c1b3db4a0

import Mathlib.Analysis.SpecialFunctions.Log.Base
open Real

theorem WorkbookRestored.plus_71177 : ∃ x : ℝ, 0 < x ∧ x ≠ 2 ∧ Real.logb 2 x = x / 2   :=  by sorry

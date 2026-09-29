-- Prove2me | Theorems.Thm_WorkbookRestored_plus_13953
-- name    : WorkbookRestored.plus_13953
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:30:29.185036+00:00
-- url     : https://prove2.me/theorems/c1e4dee1-20c4-4c07-9d09-7ffdafceddae
-- title:
--   Lean-Workbook Plus 13953: Logarithmic inequality
-- statement:
--   Prove that $0 \leq \ln(1+\alpha) \leq \alpha$ for all $\alpha \geq 0$
--
--   Source: Lean-Workbook row `lean_workbook_plus_13953` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/9427c2fe-9bae-49e8-a33f-e1118fe9d406); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_13953; immutable original Prove2Me node 9427c2fe-9bae-49e8-a33f-e1118fe9d406

import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real

theorem WorkbookRestored.plus_13953 (α : ℝ) (hα : 0 ≤ α) : 0 ≤ Real.log (1 + α) ∧ Real.log (1 + α) ≤ α   :=  by sorry

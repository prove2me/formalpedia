-- Prove2me | Theorems.Thm_WorkbookRestored_plus_40944
-- name    : WorkbookRestored.plus_40944
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:02:24.950975+00:00
-- url     : https://prove2.me/theorems/28fb2284-17e5-4382-be3c-5aca2b1c010e
-- title:
--   Lean-Workbook Plus 40944: Trigonometric identity
-- statement:
--   The function $(u,v)\mapsto\sin(u^2+v^2)$ is continuous on $\mathbb R^2$, in particular at the origin.
--
--   Source: Lean-Workbook row `lean_workbook_plus_40944` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/faf2ec93-96c5-46c6-b710-7454ed63b1bb); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_40944; immutable original Prove2Me node faf2ec93-96c5-46c6-b710-7454ed63b1bb

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_40944 (x y : ℝ) : Continuous (fun p : ℝ × ℝ => sin (p.1^2 + p.2^2))   :=  by sorry

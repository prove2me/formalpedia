-- Prove2me | Theorems.Thm_WorkbookRestored_plus_36620
-- name    : WorkbookRestored.plus_36620
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:02:12.368982+00:00
-- url     : https://prove2.me/theorems/ae942c1b-fc56-4376-a1de-00a6661e3d6e
-- title:
--   Lean-Workbook Plus 36620: Trigonometric identity
-- statement:
--   For every real $\theta$, $\sin(2\theta)=2/(\tan\theta+1/\tan\theta)$. Lean’s total tangent and division include the pole and zero cases.
--
--   Source: Lean-Workbook row `lean_workbook_plus_36620` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/d5abfef3-3589-4908-8ae3-99e424ed0a61); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_36620; immutable original Prove2Me node d5abfef3-3589-4908-8ae3-99e424ed0a61

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_36620 (θ : ℝ) : sin (2 * θ) = 2 / (tan θ + 1 / tan θ)   :=  by sorry

-- Prove2me | Theorems.Thm_WorkbookRestored_plus_2614
-- name    : WorkbookRestored.plus_2614
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:27:51.157274+00:00
-- url     : https://prove2.me/theorems/f605e437-7a8a-483c-a3c7-f63e79b6865e
-- title:
--   Lean-Workbook Plus 2614: Trigonometric identity
-- statement:
--   If $\cos(\theta - \alpha) = p$ and $\sin(\theta + \beta) = q$ then prove that $ p^2 + q^2 - 2pq \sin(\alpha + \beta) = \cos^2 (\alpha + \beta) $
--
--   Source: Lean-Workbook row `lean_workbook_plus_2614` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/916dfd8a-702c-46f6-8cb9-8703b6d8ebe8); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_2614; immutable original Prove2Me node 916dfd8a-702c-46f6-8cb9-8703b6d8ebe8

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_2614 (p q α β θ : ℝ) (hp : cos (θ - α) = p) (hq : sin (θ + β) = q) : p^2 + q^2 - 2 * p * q * sin (α + β) = cos (α + β)^2   :=  by sorry

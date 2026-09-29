-- Prove2me | Theorems.Thm_WorkbookRestored_plus_5163
-- name    : WorkbookRestored.plus_5163
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:29:42.472425+00:00
-- url     : https://prove2.me/theorems/c40874db-bdee-4ec2-bfbd-41710a995747
-- title:
--   Lean-Workbook Plus 5163: Trigonometric inequality
-- statement:
--   Prove $\sin(x) * \cos(x) \leq \frac{1}{2}$ .
--
--   Source: Lean-Workbook row `lean_workbook_plus_5163` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/eca5186c-207c-420d-a68a-1f4c6e7c85e8); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_5163; immutable original Prove2Me node eca5186c-207c-420d-a68a-1f4c6e7c85e8

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_5163 : ∀ x : ℝ, sin x * cos x ≤ 1 / 2   :=  by sorry

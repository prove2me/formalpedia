-- Prove2me | Theorems.Thm_WorkbookRestored_plus_37935
-- name    : WorkbookRestored.plus_37935
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:35:11.733485+00:00
-- url     : https://prove2.me/theorems/88d286cf-8cec-46d2-b8cb-c0fff0e9f6da
-- title:
--   Lean-Workbook Plus 37935: Trigonometric inequality
-- statement:
--   **Lean-Workbook Plus 37935: Monotonicity of x^a + a^x**
--
--   For every real $a\ge1$, the function $x\mapsto x^a+a^x$ is nondecreasing on $[0,\infty)$: if $0\le x\le y$, then $x^a+a^x\le y^a+a^y$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_37935` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/6637caec-c4b0-49cd-854a-d7f7e17fee4c); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_37935; immutable original Prove2Me node 6637caec-c4b0-49cd-854a-d7f7e17fee4c

import Mathlib.Analysis.SpecialFunctions.Pow.Real

theorem WorkbookRestored.plus_37935 (a : ℝ) (ha : 1 ≤ a) : ∀ x y : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ x ≤ y → x^a + a^x ≤ y^a + a^y   :=  by sorry

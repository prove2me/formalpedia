-- Prove2me | Theorems.Thm_lean_workbook_plus_28567
-- name    : lean_workbook_plus_28567
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/f75ff7ea-d887-406b-aa43-9659f2441ad0
-- statement:
--   Showing that $ a|a$ is equivalent to showing that $ an = a$ for some integer $ n$ . We have $ a \\cdot 1 = a$ , so $ a|a$ . (Note that $ 0 \\cdot 1 = 0$ , so $ 0|0$ . Am I wrong?)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28567 (a : ℤ) : a ∣ a   :=  by sorry

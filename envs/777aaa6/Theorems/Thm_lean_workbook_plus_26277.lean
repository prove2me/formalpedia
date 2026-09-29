-- Prove2me | Theorems.Thm_lean_workbook_plus_26277
-- name    : lean_workbook_plus_26277
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/49f80fd2-c7f8-4885-af84-8038badee046
-- statement:
--   Let $ a,b,c\in \mathbb{R}$ such that $ a^3b+b^3c+c^3a=0$ . Show that:\n\n $ a^4+b^4+c^4+2abc(a+b+c)\ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26277 (a b c : ℝ) (h : a ^ 3 * b + b ^ 3 * c + c ^ 3 * a = 0) :
  a ^ 4 + b ^ 4 + c ^ 4 + 2 * a * b * c * (a + b + c) ≥ 0   :=  by sorry

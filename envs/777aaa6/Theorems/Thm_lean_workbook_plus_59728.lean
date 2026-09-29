-- Prove2me | Theorems.Thm_lean_workbook_plus_59728
-- name    : lean_workbook_plus_59728
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/184c2140-3264-4f2e-8b48-f001a15b74c0
-- statement:
--   Let the speed of person at $A$ be $a$ and let the speed of person at $B$ be $a - 10$. Also, let the time they take be $t$. Then, $(a - 10) \cdot t + a \cdot t = 390$. Hence, $(2a - 10) \cdot t = 390$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59728 (a t : ℝ) : (a - 10) * t + a * t = 390 ↔ (2 * a - 10) * t = 390   :=  by sorry

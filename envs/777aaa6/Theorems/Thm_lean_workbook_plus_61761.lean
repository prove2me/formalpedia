-- Prove2me | Theorems.Thm_lean_workbook_plus_61761
-- name    : lean_workbook_plus_61761
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/2cd08fe6-c962-4f3b-b9ea-545294952df4
-- statement:
--   Let a,b be two real positive numbers satisfying ${a^3} + {b^3} = a - b$. Prove that ${a^2} + {b^2} < 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61761 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a^3 + b^3 = a - b) : a^2 + b^2 < 1   :=  by sorry

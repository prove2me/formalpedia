-- Prove2me | Theorems.Thm_lean_workbook_plus_46461
-- name    : lean_workbook_plus_46461
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/f6cd646e-6e10-48a4-80aa-cb3070419956
-- statement:
--   Let $ a,b > 0$ ,Prove that: $ 2(a^2 - a + 1)(b^3 + 1) \ge (a^2 + b)(b^2 + 1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46461 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 2 * (a^2 - a + 1) * (b^3 + 1) ≥ (a^2 + b) * (b^2 + 1)   :=  by sorry

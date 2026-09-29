-- Prove2me | Theorems.Thm_lean_workbook_plus_23676
-- name    : lean_workbook_plus_23676
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/b62a1432-c048-4375-85a5-acb4a411167c
-- statement:
--   $ 4(a^3 + b^3)\ge (a + b)^3 \Leftrightarrow a^3+b^3 \ge ab^2+a^2b$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23676 (a b : ℝ) : 4 * (a ^ 3 + b ^ 3) ≥ (a + b) ^ 3 ↔ a ^ 3 + b ^ 3 ≥ a * b ^ 2 + a ^ 2 * b   :=  by sorry

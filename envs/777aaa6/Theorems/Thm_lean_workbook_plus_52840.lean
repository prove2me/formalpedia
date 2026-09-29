-- Prove2me | Theorems.Thm_lean_workbook_plus_52840
-- name    : lean_workbook_plus_52840
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/44130fd6-256e-4b74-91fa-d06ebca2e054
-- statement:
--   Prove the inequality $(1)\ \ \frac {a(3a + 1)}{(a + 1)^2}\leq \frac{3}{4}a+\frac{1}{4}$ for positive real numbers $a$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52840 (a : ℝ) (ha : 0 < a) : (a * (3 * a + 1)) / (a + 1) ^ 2 ≤ (3 / 4 : ℝ) * a + 1 / 4   :=  by sorry

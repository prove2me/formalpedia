-- Prove2me | Theorems.Thm_lean_workbook_plus_21537
-- name    : lean_workbook_plus_21537
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/9ff0cafa-e326-41ca-9a71-56e494b805ae
-- statement:
--   Prove that $a^3b^2+b^3c^2+c^3a^2\geq(a^2+b^2+c^2)abc$ for all triangle with sides $a$, $b$, and $c$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21537 (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : a^3 * b^2 + b^3 * c^2 + c^3 * a^2 >= (a^2 + b^2 + c^2) * a * b * c   :=  by sorry

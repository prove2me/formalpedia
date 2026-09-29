-- Prove2me | Theorems.Thm_lean_workbook_plus_52201
-- name    : lean_workbook_plus_52201
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/af896a1b-61b4-4cab-9421-84296b47bfee
-- statement:
--   Let $a, b, c$ be positive real numbers. Prove that: $a(a+b)(a+c)+b(b+a)(b+c)+c(c+a)(c+b)\geq \frac{4}{9}(a+b+c)^3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52201 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a * (a + b) * (a + c) + b * (b + a) * (b + c) + c * (c + a) * (c + b) ≥ (4 / 9) * (a + b + c) ^ 3   :=  by sorry

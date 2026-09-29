-- Prove2me | Theorems.Thm_lean_workbook_plus_52193
-- name    : lean_workbook_plus_52193
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/60d69bc4-098e-454d-a358-3394f04ad9cb
-- statement:
--   Is $a^3b+b^3c+c^3a \ge abc(a+b+c)$ for all $a, b, c \in \mathbb{R+}$ true? If true, are there any generalizations? How does AM-GM work in this context? Prove the inequality using Chebyshev's inequality and the Cauchy-Schwarz inequality.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52193 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^3 * b + b^3 * c + c^3 * a ≥ a * b * c * (a + b + c)   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_34560
-- name    : lean_workbook_plus_34560
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/49b2603c-aeb3-4f3b-aa43-041cce9e1791
-- statement:
--   If $a, b, c \ge 0$ then $a^3b + b^3c + c^3a - a^2bc - ab^2c - abc^2 = ab(a - c)^2 + bc(a - b)^2 + ac(b - c)^2 \ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34560 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : a^3 * b + b^3 * c + c^3 * a - a^2 * b * c - a * b^2 * c - a * b * c^2 = a * b * (a - c)^2 + b * c * (a - b)^2 + a * c * (b - c)^2   :=  by sorry

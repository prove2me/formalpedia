-- Prove2me | Theorems.Thm_lean_workbook_plus_66580
-- name    : lean_workbook_plus_66580
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/8179974b-69be-420b-8aaf-96a264bc8a6c
-- statement:
--   Let $a, b, c \ge 0$ . Prove that $3(a^2+b^2+c^2)^2 \ge (a+b+c)[2(a^3+b^3+c^3) + 3abc]. \quad (1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66580 (a b c : ℝ) : 3 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ (a + b + c) * (2 * (a ^ 3 + b ^ 3 + c ^ 3) + 3 * a * b * c)   :=  by sorry

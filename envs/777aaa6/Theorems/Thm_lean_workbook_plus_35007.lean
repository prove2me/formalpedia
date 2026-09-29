-- Prove2me | Theorems.Thm_lean_workbook_plus_35007
-- name    : lean_workbook_plus_35007
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/c5e3cf51-38a0-41ea-af1e-9790508481a9
-- statement:
--   Further simplification gives $ 2(ab+bc+ca)+a^2+b^2+c^2 \ge 0$ which is equivalent to $(a+b+c)^2 \ge 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35007 (a b c : ℝ) : 2 * (a * b + b * c + c * a) + a ^ 2 + b ^ 2 + c ^ 2 ≥ 0   :=  by sorry

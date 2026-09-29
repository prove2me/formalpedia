-- Prove2me | Theorems.Thm_lean_workbook_plus_30885
-- name    : lean_workbook_plus_30885
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/3fcaf9b4-6f5c-42c6-97f0-45669735766a
-- statement:
--   Prove that $a^{2}+b^{2}+c^{2}+2(ab+bc+ca) \geq 3(ab+bc+ca)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30885 (a b c : ℝ) : a^2 + b^2 + c^2 + 2 * (a * b + b * c + c * a) ≥ 3 * (a * b + b * c + c * a)   :=  by sorry

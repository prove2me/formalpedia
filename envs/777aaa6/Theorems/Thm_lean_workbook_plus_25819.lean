-- Prove2me | Theorems.Thm_lean_workbook_plus_25819
-- name    : lean_workbook_plus_25819
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/b98bd7f6-4bb2-41fd-b26e-a16a30e70c39
-- statement:
--   Prove that $3\sum_{cyc}{a^2}\ge 2(ab+ac+ad+bc+bd+cd)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25819 (a b c d : ℝ) : 3 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ≥ 2 * (a * b + a * c + a * d + b * c + b * d + c * d)   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_22111
-- name    : lean_workbook_plus_22111
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/bd65b0d4-d672-4a4e-921d-591b54a8f2c3
-- statement:
--   Real numbers $a, b, c$ satisfy $a^2 + b^2 + c^2 = 1.$ Prove the inequality: $\frac {a^2}{1 + 2bc}+\frac {b^2}{1 + 2ca}+\frac {c^2}{1 + 2ab}\geq \frac{3}{5}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22111 : a^2 + b^2 + c^2 = 1 → a^2 / (1 + 2 * b * c) + b^2 / (1 + 2 * c * a) + c^2 / (1 + 2 * a * b) ≥ 3 / 5   :=  by sorry

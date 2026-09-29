-- Prove2me | Theorems.Thm_lean_workbook_plus_12536
-- name    : lean_workbook_plus_12536
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/001a812f-6729-4825-8397-546c7b6e412a
-- statement:
--   (A. Hrabrov) we know that $(a^2+d^2)(c^2+b^2) = (ab+cd)^2 + (ac-bd)^2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12536 {a b c d : ℝ} : (a ^ 2 + d ^ 2) * (c ^ 2 + b ^ 2) = (a * b + c * d) ^ 2 + (a * c - b * d) ^ 2   :=  by sorry

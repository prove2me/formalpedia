-- Prove2me | Theorems.Thm_lean_workbook_plus_36501
-- name    : lean_workbook_plus_36501
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/ed8f27b2-ab53-44cb-8e9e-b03a42849643
-- statement:
--   Explicitly, this says $(a^{2}+b^{2})(c^{2}+d^{2}) = (ac-bd)^{2}+(bc+ad)^{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36501 (a b c d : ℝ) : (a^2 + b^2) * (c^2 + d^2) = (a*c - b*d)^2 + (b*c + a*d)^2   :=  by sorry

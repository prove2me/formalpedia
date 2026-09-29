-- Prove2me | Theorems.Thm_lean_workbook_plus_31376
-- name    : lean_workbook_plus_31376
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/268a6dd7-ac3b-4ee9-8c9c-fd76b0043167
-- statement:
--   Prove that $f(x) = \cos(\arcsin x) - \sqrt{1-x^2}$ is a constant function
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31376 x y : cos (arcsin x) - Real.sqrt (1 - x ^ 2) = cos (arcsin y) - Real.sqrt (1 - y ^ 2)   :=  by sorry

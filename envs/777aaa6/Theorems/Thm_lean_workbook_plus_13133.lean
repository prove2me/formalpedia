-- Prove2me | Theorems.Thm_lean_workbook_plus_13133
-- name    : lean_workbook_plus_13133
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/86c8fd7d-6c89-4f58-af12-793c7b1e8bcc
-- statement:
--   Prove $x^3-y^3 = (x-y)(x^2+xy+y^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13133 (x y : ℝ) : x^3 - y^3 = (x - y) * (x^2 + x * y + y^2)   :=  by sorry

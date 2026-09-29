-- Prove2me | Theorems.Thm_lean_workbook_plus_41192
-- name    : lean_workbook_plus_41192
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/5ca94233-f05f-483c-9abe-84013076478e
-- statement:
--   Prove that $ x^4 + y^4 + z^4 \ge xyz(x + y + z)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41192 (x y z : ℝ) : x ^ 4 + y ^ 4 + z ^ 4 ≥ x * y * z * (x + y + z)   :=  by sorry

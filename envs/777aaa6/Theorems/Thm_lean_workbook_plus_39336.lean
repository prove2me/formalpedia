-- Prove2me | Theorems.Thm_lean_workbook_plus_39336
-- name    : lean_workbook_plus_39336
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/0fa48b21-6371-4fcc-9bde-ab4ae44eca58
-- statement:
--   Factorization identity: $(a + b + c)(ab + bc + ac) - abc = (a + b)(b + c)(a + c)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39336 (a b c : ℤ) : (a + b + c) * (a * b + b * c + a * c) - a * b * c = (a + b) * (b + c) * (a + c)   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_57196
-- name    : lean_workbook_plus_57196
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/07437783-774b-4891-99e5-f1e960b95857
-- statement:
--   $ xy + zy = xz$ has solutions parameterised by $ y = rs$ , $ x = r(r + s)$ $ z = s(r + s)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57196 (x y z r s : ℂ) : (x = r * (r + s) ∧ y = r * s ∧ z = s * (r + s)) → x * y + z * y = x * z   :=  by sorry

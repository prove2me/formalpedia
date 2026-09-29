-- Prove2me | Theorems.Thm_lean_workbook_plus_31215
-- name    : lean_workbook_plus_31215
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/6eb7627d-b3c8-4f18-807c-fdef8eacdc82
-- statement:
--   Derive $ e^{i(x+y)}=e^{ix}e^{iy}$ using trigonometric identities.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31215 : exp (i * (x + y)) = exp (i * x) * exp (i * y)   :=  by sorry

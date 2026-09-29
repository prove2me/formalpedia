-- Prove2me | Theorems.Thm_lean_workbook_plus_52393
-- name    : lean_workbook_plus_52393
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/01086881-4407-4d29-b781-6ba67e510a3c
-- statement:
--   It's $ \frac {\frac9{10}\cdot\frac1{100}}{\frac9{10}\cdot\frac1{100} + \frac1{10}\cdot\frac {99}{100}} = \boxed{\frac1{12}}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52393 :
  ((9:ℝ) / 10 * 1 / 100) / (9 / 10 * 1 / 100 + 1 / 10 * 99 / 100) = 1 / 12   :=  by sorry

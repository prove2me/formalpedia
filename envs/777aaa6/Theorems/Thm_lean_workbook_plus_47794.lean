-- Prove2me | Theorems.Thm_lean_workbook_plus_47794
-- name    : lean_workbook_plus_47794
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/e71cd7ff-24fb-4afb-9c0d-e48daff348bc
-- statement:
--   $\frac{15}{24}$ divided by 60 is $\frac{15}{1440}$ which I think is $\frac{1}{96}$ per min
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47794 (a : ℚ) (h : a = 15 / 24) : a / 60 = 1 / 96   :=  by sorry

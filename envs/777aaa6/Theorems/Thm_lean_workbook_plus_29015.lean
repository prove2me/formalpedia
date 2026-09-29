-- Prove2me | Theorems.Thm_lean_workbook_plus_29015
-- name    : lean_workbook_plus_29015
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/5634a31d-2632-4101-927c-12800e192659
-- statement:
--   The sum is also equal to $\left\lfloor \left( 1 - \frac{1}{2} \right) + \left( 1 - \frac{1}{3} \right) + \ldots + \left( 1 - \frac{1}{100} \right) \right\rfloor = \left\lfloor 99 - \left( \frac{1}{2} + \frac{1}{3} + \ldots + \frac{1}{100} \right) \right\rfloor$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29015 :
  ∑ k in (Finset.Icc 2 100), (1 - 1 / k) = 99 - ∑ k in (Finset.Icc 2 100), (1 / k)   :=  by sorry

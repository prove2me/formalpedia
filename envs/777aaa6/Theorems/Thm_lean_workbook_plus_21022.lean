-- Prove2me | Theorems.Thm_lean_workbook_plus_21022
-- name    : lean_workbook_plus_21022
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/01adfd83-1a81-4c92-aab5-cf2ef9002a10
-- statement:
--   In total we have, $\\sum_{n=1}^{10}n^2=\\frac{10(21)(11)}{6}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21022 :
  ∑ n in (Finset.Icc 1 10), n^2 = 10 * 21 * 11 / 6   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_53657
-- name    : lean_workbook_plus_53657
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/3d7a76c7-adea-455c-ac25-58ca32ce7d2e
-- statement:
--   prove that \n\n\\( \\displaystyle{\\sum_{i=1}^{4n+2009}i^7=\\frac{1}{8}\\, \\left( 4\\,n+2010 \\right) ^{8}-\\frac{1}{2}\\, \\left( 4\\,n+2010 \\right) ^{7}+\\frac {7}{12}\\, \\left( 4\\,n+2010 \\right) ^{6}-\\frac {7}{24}\\,\\ \\left( 4\\,n+2010 \\right) ^{4}+\\frac{1}{12}\\, \\left( 4\\,n+2010 \\right) ^{2}} \\)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53657 : ∀ n : ℕ, ∑ i in Finset.Icc 1 (4 * n + 2009), i ^ 7 = (1 / 8) * (4 * n + 2010) ^ 8 - (1 / 2) * (4 * n + 2010) ^ 7 + (7 / 12) * (4 * n + 2010) ^ 6 - (7 / 24) * (4 * n + 2010) ^ 4 + (1 / 12) * (4 * n + 2010) ^ 2   :=  by sorry

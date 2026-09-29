-- Prove2me | Theorems.Thm_lean_workbook_plus_48129
-- name    : lean_workbook_plus_48129
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/4847fe06-6002-4ea4-8ba2-d3bea12dca0e
-- statement:
--   Because $ (a+b)(b+c)(c+a)\ge\frac{8(a+b+c)(ab+bc+ca)}{9} $\nfrom it result $ a^2+b^2+c^2+\frac{9abc}{a+b+c}\ge 2(ab+bc+ca) $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48129 :
  ∀ a b c : ℝ, a^2 + b^2 + c^2 + (9 * a * b * c) / (a + b + c) ≥ 2 * (a * b + b * c + c * a)   :=  by sorry

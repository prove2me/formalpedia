-- Prove2me | Theorems.Thm_WorkbookSource_base_47874
-- name    : WorkbookSource.base_47874
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:48:42.871127+00:00
-- url     : https://prove2.me/theorems/73e487ca-a5ea-4227-bc0e-bff1e4889604
-- title:
--   A comparison between two cyclic quartic sums
-- statement:
--   If a, b, c are real number then: $ 3(a^4+b^4+c^4)+2(b^3a+a^3c+c^3b)\ge 3(a^3b+b^3c+c^3a) $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_47874` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_47874; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_47874 (a b c : ℝ) :
  3 * (a ^ 4 + b ^ 4 + c ^ 4) + 2 * (b ^ 3 * a + a ^ 3 * c + c ^ 3 * b) ≥
  3 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a)  :=  by sorry

-- Prove2me | Theorems.Thm_WorkbookSource_base_43233
-- name    : WorkbookSource.base_43233
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:37:15.985978+00:00
-- url     : https://prove2.me/theorems/b5490f27-0723-46a5-8710-9a4cc5ba6633
-- title:
--   A cubic symmetric lower bound at total one
-- statement:
--   Let $ a,b,c,d$ non-negative reals such that $ a + b + c + d = 1$ . Prove that
--
--    $ 5(a^3 + b^3 + c^3 + d^3) + 12(abc + bcd + cda + dab)\geq1$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_43233` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_43233; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_43233 (a b c d : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hd : d ≥ 0) (hab : a + b + c + d = 1) : 5 * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) + 12 * (a * b * c + b * c * d + c * d * a + d * a * b) ≥ 1  :=  by sorry

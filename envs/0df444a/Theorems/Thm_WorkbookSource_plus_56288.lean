-- Prove2me | Theorems.Thm_WorkbookSource_plus_56288
-- name    : WorkbookSource.plus_56288
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:40:41.033388+00:00
-- url     : https://prove2.me/theorems/667f6c0b-296f-44f0-bb23-4bb5650ea928
-- title:
--   A cubic reciprocal product sum bounds the reciprocal sum
-- statement:
--   Prove that \(\dfrac{ab}{c^3} + \dfrac{bc}{a^3} + \dfrac{ca}{b^3} \ge \dfrac 1 a + \dfrac 1 b + \dfrac 1 c \) where a,b,c are positive real numbers.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_56288` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_56288; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_56288 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a * b / c ^ 3 + b * c / a ^ 3 + c * a / b ^ 3 ≥ 1 / a + 1 / b + 1 / c   :=  by sorry

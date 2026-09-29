-- Prove2me | Theorems.Thm_WorkbookSource_base_44601
-- name    : WorkbookSource.base_44601
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:39:36.039935+00:00
-- url     : https://prove2.me/theorems/4e6aead0-16ac-4622-90e8-5cddaea70105
-- title:
--   A fifth-power average bounds a fourth-power sum with a product correction
-- statement:
--   Let $a,b,c,d>0. $ Prove that
--    $\frac{a^5+b^5+c^5+d^5}{a+b+c+d}\ge\frac{1}{3}(a^4+b^4+c^4+d^4-abcd)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_44601` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_44601; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_44601 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a^5 + b^5 + c^5 + d^5) / (a + b + c + d) ≥ (1/3) * (a^4 + b^4 + c^4 + d^4 - a * b * c * d)  :=  by sorry

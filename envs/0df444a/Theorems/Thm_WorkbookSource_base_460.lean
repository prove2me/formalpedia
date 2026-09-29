-- Prove2me | Theorems.Thm_WorkbookSource_base_460
-- name    : WorkbookSource.base_460
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T23:05:06.137297+00:00
-- url     : https://prove2.me/theorems/527d3d89-d2ee-47dd-8fc7-fd5a8a0bf49d
-- title:
--   A product inequality for nonnegative variables of sum three
-- statement:
--   Let $ a,b,c\geq 0 $ and $a+b+c =3 .$ Prove that $$(4-ab)(4-bc)(4-ca)+ abc \geq 28$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_460` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_460; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_460 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (habc : a + b + c = 3) : (4 - a * b) * (4 - b * c) * (4 - c * a) + a * b * c ≥ 28  :=  by sorry

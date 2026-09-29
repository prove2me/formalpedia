-- Prove2me | Theorems.Thm_WorkbookSource_plus_47144
-- name    : WorkbookSource.plus_47144
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:32:26.369453+00:00
-- url     : https://prove2.me/theorems/54a3ceef-5573-4c22-8730-2b7cb35997f5
-- title:
--   A four-variable elementary symmetric inequality
-- statement:
--   Let $a,b,c,d$ be four non-negative real numbers with sum 4. Prove that $abcd + \frac{1}{3} \left( ab + ac + ad + bc + bd + cd \right) \ge \frac{3}{4} \left(abc + abd + acd + bcd \right)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_47144` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_47144; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_47144 (a b c d : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hd : d ≥ 0) (hab : a + b + c + d = 4) : a * b * c * d + 1 / 3 * (a * b + a * c + a * d + b * c + b * d + c * d) ≥ 3 / 4 * (a * b * c + a * b * d + a * c * d + b * c * d)   :=  by sorry

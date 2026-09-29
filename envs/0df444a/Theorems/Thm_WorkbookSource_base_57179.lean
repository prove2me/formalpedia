-- Prove2me | Theorems.Thm_WorkbookSource_base_57179
-- name    : WorkbookSource.base_57179
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:47:47.538971+00:00
-- url     : https://prove2.me/theorems/2eae0c50-1085-430b-a065-862fceaca1a8
-- title:
--   A fifth-power ratio bounds a corrected cubic sum
-- statement:
--   Let $a,b,c>0. $ Prove that
--    $\frac{a^5+b^5+c^5}{a^2+b^2+c^2}\ge \frac{1}{2}(a^3+b^3+c^3-abc)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_57179` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_57179; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_57179 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^5 + b^5 + c^5) / (a^2 + b^2 + c^2) ≥ (1 / 2) * (a^3 + b^3 + c^3 - a * b * c)  :=  by sorry

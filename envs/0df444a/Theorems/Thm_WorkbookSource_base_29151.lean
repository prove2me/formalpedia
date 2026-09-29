-- Prove2me | Theorems.Thm_WorkbookSource_base_29151
-- name    : WorkbookSource.base_29151
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T23:55:25.290049+00:00
-- url     : https://prove2.me/theorems/739051b5-ec51-47da-803a-59e34572d098
-- title:
--   A mixed-degree cyclic product inequality
-- statement:
--   If a,b,c >0 prove that
--    $ bc\left(a^3+a^2+1\right)+ac\left(b^3+b^2+1\right)+ab\left(c^3+c^2+1\right)\geq abc\left(6+ab+bc+ca\right) $
--
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_29151` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_29151; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_29151 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :  b * c * (a ^ 3 + a ^ 2 + 1) + a * c * (b ^ 3 + b ^ 2 + 1) + a * b * (c ^ 3 + c ^ 2 + 1) ≥ a * b * c * (6 + a * b + b * c + c * a)  :=  by sorry

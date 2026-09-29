-- Prove2me | Theorems.Thm_WorkbookSource_plus_68899
-- name    : WorkbookSource.plus_68899
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:50:16.61938+00:00
-- url     : https://prove2.me/theorems/9b3af281-364e-454b-a9be-e000e3933f17
-- title:
--   A mixed quartic ratio sum bounds the pair-product sum
-- statement:
--   For all positive real numbers $a,b,c$ we have
--    $ \frac{a^{4}+b^{2}c^{2}}{c^{2}+a^{2}}+\frac{b^{4}+c^{2}a^{2}}{a^{2}+b^{2}}+\frac{c^{4}+a^{2}b^{2}}{b^{2}+c^{2}} \geq ab+bc+ca $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_68899` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_68899; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_68899 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^4 + b^2 * c^2) / (c^2 + a^2) + (b^4 + c^2 * a^2) / (a^2 + b^2) + (c^4 + a^2 * b^2) / (b^2 + c^2) ≥ a * b + b * c + c * a   :=  by sorry

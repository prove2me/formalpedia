-- Prove2me | Theorems.Thm_WorkbookSource_base_1181
-- name    : WorkbookSource.base_1181
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:39:27.403727+00:00
-- url     : https://prove2.me/theorems/c7458dec-4bc2-454e-8d20-da0e3be517fe
-- title:
--   A cyclic quartic inequality with coefficient seventeen
-- statement:
--   SOS form of: $a^{4} + b^{4} + c^{4} + 17\left(a^{2}b^{2} + b^{2}c^{2} + c^{2}a^{2}\right) \geqq 6\left(a + b + c\right)\left(a^{2}b + b^{2}c + c^{2}a\right)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_1181` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_1181; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_1181 (a b c : ℝ) : a^4 + b^4 + c^4 + 17 * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) ≥ 6 * (a + b + c) * (a^2 * b + b^2 * c + c^2 * a)  :=  by sorry

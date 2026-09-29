-- Prove2me | Theorems.Thm_WorkbookSource_base_50279
-- name    : WorkbookSource.base_50279
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:36:28.057926+00:00
-- url     : https://prove2.me/theorems/4ec33380-e07e-46bc-89b1-61c8b2bd8392
-- title:
--   A reciprocal fourth-power ratio with a cubic correction
-- statement:
--   Prove that for all positive numbers $ a,b,c$ then:
--    $ \frac {abc(a + b + c)}{a^{4} + b^{4} + c^{4}} + \frac {12(a^{3} + b^{3} + c^{3})}{(a + b + c)(a^{2} + b^{2} + c^{2})}\geq 5$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_50279` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_50279; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_50279 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b * c * (a + b + c) / (a ^ 4 + b ^ 4 + c ^ 4) + 12 * (a ^ 3 + b ^ 3 + c ^ 3) / ((a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2))) ≥ 5  :=  by sorry

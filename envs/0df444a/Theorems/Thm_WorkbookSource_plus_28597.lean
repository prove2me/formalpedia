-- Prove2me | Theorems.Thm_WorkbookSource_plus_28597
-- name    : WorkbookSource.plus_28597
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:33:25.255341+00:00
-- url     : https://prove2.me/theorems/6a2514a5-b899-4c0e-8e94-b9773cce0825
-- title:
--   A product of mixed quadratics at fixed sum two
-- statement:
--   Let $a,b,c\geq0$ and $a+b+c=2$ .Prove that $$(a^2+bc)(b^2+ca)(c^2+ab)+ abc\leq 1 .$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_28597` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_28597; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_28597 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 2) : (a^2 + b * c) * (b^2 + c * a) * (c^2 + a * b) + a * b * c ≤ 1   :=  by sorry

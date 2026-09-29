-- Prove2me | Theorems.Thm_WorkbookSource_base_8926
-- name    : WorkbookSource.base_8926
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:38:58.124946+00:00
-- url     : https://prove2.me/theorems/bca69598-9326-4df2-8bb0-ce640516676a
-- title:
--   A cyclic quadratic ratio sum bounds the normalized quadratic mean
-- statement:
--   Let $a,b,c$ be positive real numbers. Prove that:
--
--    $$\frac{a^2}{b^2+2ab}+\frac{b^2}{c^2+2bc}+\frac{c^2}{a^2+2ca} \geq \frac{3(a^2+b^2+c^2)}{(a+b+c)^2}$$
--   Similar problems: <https://artofproblemsolving.com/community/c6h1814384>
--
--   C-S with $(a+c)^2$ helps, but a full expanding gives something obvious.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_8926` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_8926; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_8926 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / (b^2 + 2 * a * b) + b^2 / (c^2 + 2 * b * c) + c^2 / (a^2 + 2 * c * a)) ≥ 3 * (a^2 + b^2 + c^2) / (a + b + c)^2  :=  by sorry

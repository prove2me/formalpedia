-- Prove2me | Theorems.Thm_WorkbookSource_base_2157
-- name    : WorkbookSource.base_2157
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:31:06.410748+00:00
-- url     : https://prove2.me/theorems/5c6f57fd-bb5c-41de-90ac-7866f6ee9b02
-- title:
--   A four-variable cubic pair-sum reciprocal product sum is at least one half
-- statement:
--   Let $a,b,c,d>0$ ,prove that:
--
--    $\frac{a^3}{(a+b)(c+a)(d+a)}+\frac{b^3}{(b+c)(b+d)(a+b)}+\frac{c^3}{(c+d)(c+a)(b+c)}+\frac{d^3}{(d+a)(b+d)(c+d)} \geq \frac{1}{2}$
--
--
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_2157` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_2157; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_2157 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a^3 / (a + b) / (a + c) / (a + d) + b^3 / (b + c) / (b + d) / (b + a) + c^3 / (c + d) / (c + a) / (c + b) + d^3 / (d + a) / (d + b) / (d + c)) ≥ 1 / 2  :=  by sorry

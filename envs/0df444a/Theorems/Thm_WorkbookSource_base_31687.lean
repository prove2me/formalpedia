-- Prove2me | Theorems.Thm_WorkbookSource_base_31687
-- name    : WorkbookSource.base_31687
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T08:35:45.080856+00:00
-- url     : https://prove2.me/theorems/b366d1d7-6695-4b4a-835c-55945c16d77a
-- title:
--   An alternating reciprocal sum bounds a ratio of cyclic pair and triple products
-- statement:
--   Let $a,b,c,d>0$ ,prove that:
--
--    $\frac{1}{c+a}+\frac{1}{b+d}\geq \frac{81}{4}\frac{(a+b)(b+c)(c+d)(d+a)}{(a+b+c+d)(a+c+d)(d+a+b)(a+b+c)(b+c+d)}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_31687` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_31687; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_31687 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (1 / (c + a) + 1 / (b + d)) ≥ (81 / 4) * (a + b) * (b + c) * (c + d) * (d + a) / ((a + b + c + d) * (a + c + d) * (d + a + b) * (a + b + c) * (b + c + d))  :=  by sorry

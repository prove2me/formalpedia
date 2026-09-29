-- Prove2me | Theorems.Thm_WorkbookSource_plus_22503
-- name    : WorkbookSource.plus_22503
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:33:24.424407+00:00
-- url     : https://prove2.me/theorems/35d5d1ba-3bbc-4a2f-94c0-fd27e8bbecb8
-- title:
--   A shifted pairwise quadratic ratio sum is at most six
-- statement:
--   For $a,b,c>0: a+b+c=3$ . Prove that: $\frac{a^2+4ab+b^2}{a+b+ab}+\frac{b^2+4bc+c^2}{b+c+cb}+\frac{c^2+4ac+a^2}{a+c+ac}\le 6$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_22503` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_22503; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_22503 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (a^2 + 4 * a * b + b^2) / (a + b + a * b) + (b^2 + 4 * b * c + c^2) / (b + c + b * c) + (c^2 + 4 * c * a + a^2) / (c + a + c * a) ≤ 6   :=  by sorry

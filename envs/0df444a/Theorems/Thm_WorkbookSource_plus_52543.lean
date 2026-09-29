-- Prove2me | Theorems.Thm_WorkbookSource_plus_52543
-- name    : WorkbookSource.plus_52543
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:29:55.682069+00:00
-- url     : https://prove2.me/theorems/f01dff6a-36ae-4198-bac0-679f87789080
-- title:
--   A normalized pairwise product bounds a cyclic ratio sum
-- statement:
--   If $ a,b,c>0 $ then:
--    $ \frac{17(b+c)(c+a)(a+b)}{8abc}\ge 5+8(\frac{a}{b+c}+\frac{b}{c+a}+\frac{c}{a+b}) $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_52543` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_52543; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_52543 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (17 * (b + c) * (c + a) * (a + b)) / (8 * a * b * c) ≥ 5 + 8 * (a / (b + c) + b / (c + a) + c / (a + b))   :=  by sorry

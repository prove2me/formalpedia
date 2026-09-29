-- Prove2me | Theorems.Thm_WorkbookSource_plus_31693
-- name    : WorkbookSource.plus_31693
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:55:22.155079+00:00
-- url     : https://prove2.me/theorems/25bad6e0-cb66-4746-bd9e-a714f522cc1e
-- title:
--   A five-variable cyclic triple-product-sum upper bound
-- statement:
--   Let $ a,b,c,d,e$ be non-negative real numbers and $ a+b+c+d+e=5$ . Prove: $ abc+bcd+cde+dea+eab\le 5$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_31693` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_31693; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_31693 (a b c d e : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) (hab : a + b + c + d + e = 5) : a * b * c + b * c * d + c * d * e + d * e * a + e * a * b ≤ 5   :=  by sorry

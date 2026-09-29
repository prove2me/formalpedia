-- Prove2me | Theorems.Thm_WorkbookSource_plus_59988
-- name    : WorkbookSource.plus_59988
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:32:33.985721+00:00
-- url     : https://prove2.me/theorems/6be9d412-355b-4f6a-8555-d0185750dcb1
-- title:
--   A parametric pairwise-product bound at unit sum
-- statement:
--   Let $a,b,c,d\geq 0$ and $a+b +c +d =1.$ Prove that $ab +kbc +cd \leq \dfrac{k}{4}$ Where $k\geq 1.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_59988` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_59988; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_59988 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (hab : a + b + c + d = 1) (k : ℝ) (hk : 1 ≤ k) : a * b + k * b * c + c * d ≤ k / 4   :=  by sorry

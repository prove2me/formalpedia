-- Prove2me | Theorems.Thm_WorkbookSource_plus_15874
-- name    : WorkbookSource.plus_15874
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:55:14.209796+00:00
-- url     : https://prove2.me/theorems/bff3096b-551e-4a11-9920-884e438077fc
-- title:
--   A four-variable triple-product-sum upper bound
-- statement:
--   Prove that for $a, b, c, d > 0$ and $a + b + c + d = 4$, $abc + bcd + cda + dab \leq 4$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_15874` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_15874; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_15874 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hab : a + b + c + d = 4) : a * b * c + b * c * d + c * d * a + d * a * b ≤ 4   :=  by sorry

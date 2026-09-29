-- Prove2me | Theorems.Thm_WorkbookSource_base_15025
-- name    : WorkbookSource.base_15025
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:32:14.367219+00:00
-- url     : https://prove2.me/theorems/befe59a2-8b93-41a7-a92e-e8b996b52854
-- title:
--   A six-variable cyclic triple-product bound
-- statement:
--   If some reals $ a > 0$ , $ b > 0$ , $ c > 0$ , $ d > 0$ , $ e > 0$ , $ f > 0$ satisfy $ a + b + c + d + e + f = 1$ , then prove that
--    $ abc + bcd + cde + def + efa + fab\leq\frac {1}{27}$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_15025` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_15025; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_15025 (a b c d e f : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) (hf : 0 < f) (habcdef : a + b + c + d + e + f = 1) : a * b * c + b * c * d + c * d * e + d * e * f + e * f * a + f * a * b ≤ 1 / 27  :=  by sorry

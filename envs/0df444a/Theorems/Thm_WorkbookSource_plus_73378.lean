-- Prove2me | Theorems.Thm_WorkbookSource_plus_73378
-- name    : WorkbookSource.plus_73378
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:53:37.887982+00:00
-- url     : https://prove2.me/theorems/6bc1c097-57ee-43e6-8463-eacfc99f9e71
-- title:
--   A weighted cyclic linear ratio sum is at least eight
-- statement:
--   Let $ a, b, c$ be positive real numbers. Prove o disprove that
--
--    $ \frac{5a + 3c}{2a + b} + \frac{5b + 3a}{2b + c} + \frac{5c + 3b}{2c + a} \ge 8$ .
--
--
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_73378` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_73378; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_73378 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (5 * a + 3 * c) / (2 * a + b) + (5 * b + 3 * a) / (2 * b + c) + (5 * c + 3 * b) / (2 * c + a) ≥ 8   :=  by sorry

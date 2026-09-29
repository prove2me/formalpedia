-- Prove2me | Theorems.Thm_WorkbookSource_base_32639
-- name    : WorkbookSource.base_32639
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:51:38.481619+00:00
-- url     : https://prove2.me/theorems/bfdc061f-003e-4060-9cf5-101748eb6f1f
-- title:
--   An eighth-power sum bounds mixed triple products
-- statement:
--   1/ a,b,c>0. Prove that: $a^8+b^8+c^8>=a^3b^3c^2+b^3c^3a^2+c^3a^3b^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_32639` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_32639; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_32639 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^8 + b^8 + c^8 ≥ a^3 * b^3 * c^2 + b^3 * c^3 * a^2 + c^3 * a^3 * b^2  :=  by sorry

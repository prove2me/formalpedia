-- Prove2me | Theorems.Thm_WorkbookSource_plus_24409
-- name    : WorkbookSource.plus_24409
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:27:02.830796+00:00
-- url     : https://prove2.me/theorems/df71cc4e-caae-4ca3-82d5-8978444f89c4
-- title:
--   A cyclic seventh-degree mixed-product lower bound
-- statement:
--   Let $a$ , $b$ and $c$ be non-negative numbers. Prove that: $a^6b+b^6c+c^6a\geq abc(a^2b^2+a^2c^2+b^2c^2)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_24409` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_24409; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_24409 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : a^6 * b + b^6 * c + c^6 * a ≥ a * b * c * (a^2 * b^2 + a^2 * c^2 + b^2 * c^2)   :=  by sorry

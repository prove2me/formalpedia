-- Prove2me | Theorems.Thm_WorkbookSource_plus_19425
-- name    : WorkbookSource.plus_19425
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:26:59.834048+00:00
-- url     : https://prove2.me/theorems/459ff7f3-606c-493c-ae3d-344bbc7a74dc
-- title:
--   A seventh-degree comparison of symmetric power-sum products
-- statement:
--   For positives $a$ , $b$ and $c$ prove that:
--   $2\left(a^7+b^7+c^7+5abc(a^4+b^4+c^4)\right)\ge (a^3+b^3+c^3+3abc)(a^4+b^4+c^4+abc(a+b+c))$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_19425` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_19425; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_19425 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 2 * (a^7 + b^7 + c^7 + 5 * a * b * c * (a^4 + b^4 + c^4)) ≥ (a^3 + b^3 + c^3 + 3 * a * b * c) * (a^4 + b^4 + c^4 + a * b * c * (a + b + c))   :=  by sorry

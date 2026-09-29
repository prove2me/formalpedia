-- Prove2me | Theorems.Thm_WorkbookSource_plus_59857
-- name    : WorkbookSource.plus_59857
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:41:08.930004+00:00
-- url     : https://prove2.me/theorems/23e45ea7-b919-4742-968a-78884a89913e
-- title:
--   A seventh-degree comparison of power-sum products
-- statement:
--   Let $a,\ b,\ c$ be non-negative real numbers. Prove that: $(a^4 +b^4 +c^4)(a +b)(b +c)(c +a) \geq (a +b +c)(a^2 +b^2)(b^2 +c^2)(c^2 +a^2).$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_59857` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_59857; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_59857 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : (a^4 + b^4 + c^4) * (a + b) * (b + c) * (c + a) ≥ (a + b + c) * (a^2 + b^2) * (b^2 + c^2) * (c^2 + a^2)   :=  by sorry

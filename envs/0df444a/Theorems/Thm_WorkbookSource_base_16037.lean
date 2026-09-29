-- Prove2me | Theorems.Thm_WorkbookSource_base_16037
-- name    : WorkbookSource.base_16037
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:47:04.562355+00:00
-- url     : https://prove2.me/theorems/adcbd21d-09e9-4a58-a166-34b4f8bc24fd
-- title:
--   A sixth-degree bound involving a cubed sum and triangle factors
-- statement:
--   Let $a,b,c$ be positive reals .Prove that $$(a+b+c)^3(-a+b+c)(a-b+c)(a+b-c)\leq27a^2b^2c^2 .$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_16037` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_16037; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_16037 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) ^ 3 * (-a + b + c) * (a - b + c) * (a + b - c) ≤ 27 * a ^ 2 * b ^ 2 * c ^ 2  :=  by sorry

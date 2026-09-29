-- Prove2me | Theorems.Thm_WorkbookSource_base_882
-- name    : WorkbookSource.base_882
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T23:03:37.532674+00:00
-- url     : https://prove2.me/theorems/a517da01-beab-4f0c-85bf-26554399745f
-- title:
--   A fourth-power bound for pairwise squared products
-- statement:
--   Prove that if $a,b,c\geq 0$ , then $(a+b+c)^4\geq16(a^2b^2+b^2c^2+c^2a^2)$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_882` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_882; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_882 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : (a + b + c) ^ 4 ≥ 16 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2)  :=  by sorry

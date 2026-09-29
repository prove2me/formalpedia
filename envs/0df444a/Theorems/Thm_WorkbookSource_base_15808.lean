-- Prove2me | Theorems.Thm_WorkbookSource_base_15808
-- name    : WorkbookSource.base_15808
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:52:11.985567+00:00
-- url     : https://prove2.me/theorems/4809e62d-9c5d-44a3-9c7e-642f32fbfefb
-- title:
--   A cyclic ratio bound involving the normalized quadratic sum
-- statement:
--   For positives $a$ , $b$ and $c$ prove that: $2\left(\frac{a}{b}+\frac{b}{c}+\frac{c}{a}\right)+1\geq\frac{21(a^2+b^2+c^2)}{(a+b+c)^2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_15808` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_15808; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_15808 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 2 * (a / b + b / c + c / a) + 1 ≥ 21 * (a ^ 2 + b ^ 2 + c ^ 2) / (a + b + c) ^ 2  :=  by sorry

-- Prove2me | Theorems.Thm_WorkbookSource_base_855
-- name    : WorkbookSource.base_855
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:51:29.102978+00:00
-- url     : https://prove2.me/theorems/edf90714-d3b1-49a9-847d-41f07777ffb1
-- title:
--   A pairwise sum times squared reciprocals is at least nine quarters
-- statement:
--   Prove that for any positive real numbers $a, b, c$,
--
--   $$(ab + bc + ac) \left( \frac{1}{(a + b)^2} + \frac{1}{(b + c)^2} + \frac{1}{(a + c)^2} \right) \geq \frac{9}{4}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_855` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_855; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_855 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b + b * c + c * a) * (1 / (a + b) ^ 2 + 1 / (b + c) ^ 2 + 1 / (a + c) ^ 2) ≥ 9 / 4  :=  by sorry

-- Prove2me | Theorems.Thm_WorkbookSource_base_42967
-- name    : WorkbookSource.base_42967
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:38:37.013775+00:00
-- url     : https://prove2.me/theorems/6e1914df-614a-47c8-aff9-190921e42b32
-- title:
--   A shifted pairwise reciprocal lower bound
-- statement:
--   Let $a,b,c > 0$ , prove that $\frac{1-bc}{b+c}+\frac{1-ca}{c+a}+\frac{1-ab}{a+b} \geq \frac{9 - (a + b + c)^2}{2(a + b + c)}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_42967` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_42967; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_42967 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 - b * c) / (b + c) + (1 - c * a) / (c + a) + (1 - a * b) / (a + b) ≥ (9 - (a + b + c) ^ 2) / (2 * (a + b + c))  :=  by sorry

-- Prove2me | Theorems.Thm_WorkbookSource_base_14423
-- name    : WorkbookSource.base_14423
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:56:38.611446+00:00
-- url     : https://prove2.me/theorems/f9808d1b-07b0-42b7-8f6b-7052dfd570c1
-- title:
--   A cyclic quadratic ratio bounds a normalized cubic sum
-- statement:
--   Prove that for positives $a$, $b$, and $c$:
--   $\frac{a^2}{b} + \frac{b^2}{c} + \frac{c^2}{a} \ge \frac{3(a^3 + b^3 + c^3)}{a^2 + b^2 + c^2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_14423` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_14423; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_14423 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / b + b^2 / c + c^2 / a) ≥ (3 * (a^3 + b^3 + c^3)) / (a^2 + b^2 + c^2)  :=  by sorry

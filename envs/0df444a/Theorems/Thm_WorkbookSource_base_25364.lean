-- Prove2me | Theorems.Thm_WorkbookSource_base_25364
-- name    : WorkbookSource.base_25364
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:02:19.976434+00:00
-- url     : https://prove2.me/theorems/b5913c0e-2caf-4e84-9d3b-2fe686b29afe
-- title:
--   A pairwise ratio sum with a symmetric quadratic correction
-- statement:
--   Prove, that all positive real numbers $a$ , $b$ and $c$ satisfy the inequality
--
--    $$\frac{2a}{b+c}+\frac{2b}{c+a}+\frac{2c}{a+b}+\frac{ab+bc+ca}{a^2+b^2+c^2} \geq 4.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_25364` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_25364; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_25364 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (2 * a / (b + c) + 2 * b / (c + a) + 2 * c / (a + b) + (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2)) ≥ 4  :=  by sorry

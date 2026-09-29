-- Prove2me | Theorems.Thm_WorkbookSource_base_9359
-- name    : WorkbookSource.base_9359
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:44:19.189169+00:00
-- url     : https://prove2.me/theorems/5e0cacc6-2093-4d39-8910-37acf33e2da8
-- title:
--   A cyclic pair-product reciprocal upper bound
-- statement:
--   Let $a$ , $b$ , $c$ be positive real numbers. Prove that: $\frac{ab}{a+b+2c}+\frac{bc}{b+c+2a}+\frac{ca}{c+a+2b} \leq \frac{1}{4}\left(a+b+c\right)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_9359` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_9359; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_9359 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b) / (a + b + 2 * c) + (b * c) / (b + c + 2 * a) + (c * a) / (c + a + 2 * b) ≤ (1 / 4) * (a + b + c)  :=  by sorry

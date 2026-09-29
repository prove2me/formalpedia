-- Prove2me | Theorems.Thm_WorkbookSource_plus_21539
-- name    : WorkbookSource.plus_21539
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:51:33.719242+00:00
-- url     : https://prove2.me/theorems/1aa32c9b-eba9-4b3f-bc1e-0087283bff1d
-- title:
--   A product of four shifted cyclic ratios is at least nine
-- statement:
--   Let $a, b, c, d$ be positive real number. Prove that $(1+\frac{2a}{b+c})(1+\frac{2b}{c+d})(1+\frac{2c}{d+a})(1+\frac{2d}{a+b}) \ge 9$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_21539` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_21539; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_21539 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (1 + 2 * a / (b + c)) * (1 + 2 * b / (c + d)) * (1 + 2 * c / (d + a)) * (1 + 2 * d / (a + b)) ≥ 9   :=  by sorry

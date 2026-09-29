-- Prove2me | Theorems.Thm_WorkbookSource_base_5486
-- name    : WorkbookSource.base_5486
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:16:08.963299+00:00
-- url     : https://prove2.me/theorems/1406d860-f312-4fb9-965e-b40ec08b1bcd
-- title:
--   A cyclic cubic-over-quadratic sum bounds the total
-- statement:
--   Let a, b, c be three positive reals. Prove the inequality
--
--   $\frac{a^2\left( b+c\right) }{b^2+bc+c^2}+\frac{b^2\left( c+a\right) }{c^2+ca+a^2}+\frac{c^2\left( a+b\right) }{a^2+ab+b^2}\geq \frac{2}{3}\left( a+b+c\right)$ .
--
--
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_5486` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_5486; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_5486 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a^2 * (b + c) / (b^2 + b * c + c^2) + b^2 * (c + a) / (c^2 + c * a + a^2) + c^2 * (a + b) / (a^2 + a * b + b^2)) ≥ 2 / 3 * (a + b + c)  :=  by sorry

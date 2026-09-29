-- Prove2me | Theorems.Thm_WorkbookSource_plus_61764
-- name    : WorkbookSource.plus_61764
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T08:58:25.671431+00:00
-- url     : https://prove2.me/theorems/b764c0bd-dd5e-41d2-8ff3-9851d8dd467d
-- title:
--   A quadratic and triple-product sum has a product lower bound at fixed total four
-- statement:
--   Prove that for $a, b, c, d > 0$ and $a + b + c + d = 4$, $a^2 + b^2 + c^2 + d^2 + abc + bcd + cda + dab \geq \frac{1}{2}(abcd + 15)$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_61764` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_61764; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_61764 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hab : a + b + c + d = 4) : a^2 + b^2 + c^2 + d^2 + a * b * c + b * c * d + c * d * a + d * a * b ≥ 1 / 2 * (a * b * c * d + 15)   :=  by sorry

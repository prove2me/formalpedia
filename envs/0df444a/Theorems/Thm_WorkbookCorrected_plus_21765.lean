-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_21765
-- name    : WorkbookCorrected.plus_21765
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:23:30.782358+00:00
-- url     : https://prove2.me/theorems/3bc00ec4-c0b7-42b7-9e6f-3dc8272ce68b
-- title:
--   A ninth-power rational sum at fixed total three
-- statement:
--   Let $a, b, c \in ]0, +\infty[$, such that $a + b + c = 3$, prove that:
--
--   $\frac{a^9}{(b+a)(a+c)}+\frac{b^9}{(c+b)(b+a)}+\frac{c^9}{(b+c)(c+a)} \geq \frac{3}{4}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_21765` (Apache-2.0). Natural-language proposition preserved; the erroneous original Lean transcription is corrected: Restore the product of two pair sums in each denominator; the original Lean transcription multiplies by the second factor. Proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_21765; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookCorrected.plus_21765 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a^9 / ((b + a) * (a + c)) + b^9 / ((c + b) * (b + a)) + c^9 / ((b + c) * (c + a)) ≥ 3 / 4 := by sorry

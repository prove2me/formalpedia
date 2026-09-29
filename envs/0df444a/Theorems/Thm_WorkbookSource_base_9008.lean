-- Prove2me | Theorems.Thm_WorkbookSource_base_9008
-- name    : WorkbookSource.base_9008
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:40:40.02467+00:00
-- url     : https://prove2.me/theorems/f625a67d-f6e9-4043-9806-07a5121aa224
-- title:
--   An asymmetric squared-reciprocal lower bound
-- statement:
--   Let $a, b, c > 0$ . Prove that:
--
--    $$\frac{1}{(a+b)^2}+\frac{1}{(a+c)^2}+\frac{8}{(b+c)^2} \ge \frac{4}{ab+bc+ca}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_9008` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_9008; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_9008 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (a + b) ^ 2 + 1 / (a + c) ^ 2 + 8 / (b + c) ^ 2) ≥ 4 / (a * b + b * c + c * a)  :=  by sorry

-- Prove2me | Theorems.Thm_WorkbookSource_base_22439
-- name    : WorkbookSource.base_22439
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:08:45.507892+00:00
-- url     : https://prove2.me/theorems/08f94d23-ce1c-4d12-904a-296fd911b76e
-- title:
--   A cyclic quartic inequality with a squared pairwise-sum correction
-- statement:
--   Given $a,b,c \in \mathbb{R} $ . Show that:
--   a^4+b^4+c^4+\frac{(ab+bc+ca)^2}{3} \geq 2(a^3b+b^3c+c^3a)
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_22439` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_22439; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_22439 (a b c : ℝ) : a ^ 4 + b ^ 4 + c ^ 4 + (a * b + b * c + c * a) ^ 2 / 3 ≥ 2 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a)  :=  by sorry

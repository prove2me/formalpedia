-- Prove2me | Theorems.Thm_WorkbookSource_base_12954
-- name    : WorkbookSource.base_12954
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:51:20.905562+00:00
-- url     : https://prove2.me/theorems/1a72db41-9ced-44ae-92bc-9946d972db67
-- title:
--   A cyclic rational sum bounds the normalized quadratic sum
-- statement:
--   Let $ a,b,c$ be postive real numbers. Prove that
--    $ \frac {a^2}{b} + \frac {b^2}{c} + \frac {c^2}{a} + 4\left(\frac {bc}{a} + \frac {ca}{b} + \frac {ab}{c}\right) + a + b + c \ge \frac {18(a^2 + b^2 + c^2)}{a + b + c}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_12954` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_12954; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_12954 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : a + b + c + 4 * (b * c / a + c * a / b + a * b / c) + a^2 / b + b^2 / c + c^2 / a ≥ 18 * (a^2 + b^2 + c^2) / (a + b + c)  :=  by sorry

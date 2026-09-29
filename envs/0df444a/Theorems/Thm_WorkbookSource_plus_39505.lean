-- Prove2me | Theorems.Thm_WorkbookSource_plus_39505
-- name    : WorkbookSource.plus_39505
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:02:40.172576+00:00
-- url     : https://prove2.me/theorems/caf4e7c6-9eb3-4e96-aea4-44c73a819004
-- title:
--   A mixed quadratic reciprocal sum has a symmetric upper bound
-- statement:
--   For $a, b, c>0$ , prove that
--    $\frac{1}{a^2+2bc}+\frac{1}{b^2+2ca}+\frac{1}{c^2+2ab}\leq\frac{ab+bc+ca}{a^2bc+ab^2c+abc^2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_39505` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_39505; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_39505 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (a ^ 2 + 2 * b * c) + 1 / (b ^ 2 + 2 * c * a) + 1 / (c ^ 2 + 2 * a * b)) ≤ (a * b + b * c + c * a) / (a ^ 2 * b * c + a * b ^ 2 * c + a * b * c ^ 2)   :=  by sorry

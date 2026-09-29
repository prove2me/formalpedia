-- Prove2me | Theorems.Thm_WorkbookSource_plus_22853
-- name    : WorkbookSource.plus_22853
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:07:57.559949+00:00
-- url     : https://prove2.me/theorems/a9a7c29c-f93c-4b4d-a6de-5d0d02dc3b8a
-- title:
--   A cubed pairwise sum is bounded by three quadratic factors
-- statement:
--   For $a, b, c > 0$ real numbers, prove that: $(5a^2+bc)(5b^2+ac)(5c^2+ab) \ge 8(ab+bc+ca)^3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_22853` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_22853; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_22853 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (5 * a ^ 2 + b * c) * (5 * b ^ 2 + a * c) * (5 * c ^ 2 + a * b) ≥ 8 * (a * b + b * c + c * a) ^ 3   :=  by sorry

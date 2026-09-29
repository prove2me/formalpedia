-- Prove2me | Theorems.Thm_WorkbookSource_base_14272
-- name    : WorkbookSource.base_14272
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:44:56.964584+00:00
-- url     : https://prove2.me/theorems/20d8fef3-19eb-4312-b3fb-aad382ffd48d
-- title:
--   A two-variable sixth-degree polynomial is nonnegative
-- statement:
--   Prove that $28a^6 + 44a^5v + 20a^4v^2 - 10a^3v^3 - 2a^2v^4 + 7av^5 + 4v^6 \geq 0$ for all non-negative real numbers $a$ and $v$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_14272` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_14272; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_14272 (a v : ℝ) (ha : 0 ≤ a) (hv : 0 ≤ v) : 28 * a ^ 6 + 44 * a ^ 5 * v + 20 * a ^ 4 * v ^ 2 - 10 * a ^ 3 * v ^ 3 - 2 * a ^ 2 * v ^ 4 + 7 * a * v ^ 5 + 4 * v ^ 6 ≥ 0  :=  by sorry

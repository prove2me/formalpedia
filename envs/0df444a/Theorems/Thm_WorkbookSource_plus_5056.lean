-- Prove2me | Theorems.Thm_WorkbookSource_plus_5056
-- name    : WorkbookSource.plus_5056
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:41:16.976206+00:00
-- url     : https://prove2.me/theorems/a7826c00-2e9d-4497-9930-00aecabef0d3
-- title:
--   A mixed product bound on a sphere
-- statement:
--   $3=a^2+b^2+c^2 \geq 2ab+2c +(c-1)^2-1 \to ab+c \leq 2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_5056` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_5056; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_5056 (a b c : ℝ) (h : 3 = a ^ 2 + b ^ 2 + c ^ 2) : a * b + c ≤ 2   :=  by sorry

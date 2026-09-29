-- Prove2me | Theorems.Thm_lean_workbook_plus_17776
-- name    : lean_workbook_plus_17776
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/82fc9169-0b27-49cf-b320-d0b964eea14a
-- statement:
--   $d\mid 2n^{2}$ implies $2n^2=dk$ for positive integer $k$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17776 (d : ℕ) (n : ℕ) (h : d ∣ 2 * n ^ 2) : ∃ k : ℕ, 2 * n ^ 2 = d * k   :=  by sorry

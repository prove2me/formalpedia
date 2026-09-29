-- Prove2me | Theorems.Thm_lean_workbook_plus_12763
-- name    : lean_workbook_plus_12763
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/5167e27e-008b-4e92-afce-e3a85b74c8a9
-- statement:
--   Is $\left \lbrace \frac{n!}{\pi} \pmod 1:n\in \mathbb{N}\right \rbrace$ dense in $[0,1]$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12763 : ∀ x : ℝ, x ∈ closure {n! / π % 1 | n : ℕ}   :=  by sorry

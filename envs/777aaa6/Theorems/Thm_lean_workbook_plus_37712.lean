-- Prove2me | Theorems.Thm_lean_workbook_plus_37712
-- name    : lean_workbook_plus_37712
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/4b697a74-9ca5-4441-97e4-cc70f64a3941
-- statement:
--   If $n$ is a square, then $\sqrt{n}-\left\lfloor\sqrt{n}\right\rfloor=0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37712 (n : ℕ) (h : ∃ k, k^2 = n) : √n - ⌊√n⌋ = 0   :=  by sorry

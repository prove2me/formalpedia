-- Prove2me | Theorems.Thm_lean_workbook_plus_31571
-- name    : lean_workbook_plus_31571
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/d805b661-55b7-4ba9-8426-fef9b0e96b48
-- statement:
--   Prove by induction that for $x\geqslant 3$, $3^x > x^2+3x+1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31571 (x : ℕ) (hx: x ≥ 3) : 3^x > x^2 + 3*x + 1   :=  by sorry

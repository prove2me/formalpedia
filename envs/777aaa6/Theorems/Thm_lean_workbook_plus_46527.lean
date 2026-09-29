-- Prove2me | Theorems.Thm_lean_workbook_plus_46527
-- name    : lean_workbook_plus_46527
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/629f14b5-9d22-40f3-a8aa-705f2787842b
-- statement:
--   just put n=1 in $p$ $(n)$ = $10n$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46527 (p : ℕ → ℕ) (hp : p = fun (n : ℕ) => 10 * n) : p 1 = 10   :=  by sorry

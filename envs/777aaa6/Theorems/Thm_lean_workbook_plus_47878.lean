-- Prove2me | Theorems.Thm_lean_workbook_plus_47878
-- name    : lean_workbook_plus_47878
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/64772044-b5d1-416f-99ae-9d581fb734c5
-- statement:
--   Prove that if $p|q-1$ and $q|p-1$, then $p=q$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47878 (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (h : p ∣ q - 1) (h' : q ∣ p - 1) : p = q   :=  by sorry

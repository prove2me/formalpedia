-- Prove2me | Theorems.Thm_lean_workbook_plus_8638
-- name    : lean_workbook_plus_8638
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/a89b7a72-4227-4b64-863c-9edf81b933ec
-- statement:
--   Let $p\ge 5$ be a prime. Show that $4|p+1$ or $4|p-1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8638 (p : ℕ) (h : p.Prime) (h5 : p ≥ 5) : 4 ∣ p + 1 ∨ 4 ∣ p - 1   :=  by sorry

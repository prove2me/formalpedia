-- Prove2me | Theorems.Thm_lean_workbook_plus_10747
-- name    : lean_workbook_plus_10747
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/e9cd3ea1-bd05-4e08-8711-e4c7f1624a63
-- statement:
--   Prove that $(n-2)(n-1)n(n+1)(n+2)(n+3)+3\equiv 3 \pmod {10}.$ for $\forall {n}\in\mathbb{N}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10747 : ∀ n : ℕ, ((n-2)*(n-1)*n*(n+1)*(n+2)*(n+3)+3) % 10 = 3   :=  by sorry

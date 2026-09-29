-- Prove2me | Theorems.Thm_lean_workbook_plus_59775
-- name    : lean_workbook_plus_59775
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/5e83b8a5-eb16-46cc-9afc-4e3564c3ce90
-- statement:
--   Show that there are no functions $f:\mathbb{N}\to \mathbb{N}$ such that $2f(n)> f(n-1)+f(n+1)\quad \forall n>1.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59775 (f : ℕ → ℕ) (hf: ∀ n:ℕ, n > 1 → 2 * f n > f (n-1) + f (n+1)) : False   :=  by sorry

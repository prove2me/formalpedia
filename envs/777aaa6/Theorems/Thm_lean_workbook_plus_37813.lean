-- Prove2me | Theorems.Thm_lean_workbook_plus_37813
-- name    : lean_workbook_plus_37813
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/5e9122e4-eddc-425a-a201-104d2584e311
-- statement:
--   Find all functions $f: \mathbb Z \to \mathbb Z$ which satisfy $f(m+ f(n)) = f(m) + n$ for all integers $m$ and $n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37813 : ∃ f : ℤ → ℤ, f (m + f n) = f m + n   :=  by sorry

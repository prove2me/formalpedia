-- Prove2me | Theorems.Thm_lean_workbook_plus_57945
-- name    : lean_workbook_plus_57945
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/0639d0f0-7bae-4f10-bdc4-c8faf6ae10e1
-- statement:
--   Show that for odd $n$, $f(n) = \frac{n+1}{2}$ and for even $n$, $f(n) = 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57945 (n : ℕ) (f : ℕ → ℕ) (hf: f = fun n => if n % 2 = 1 then (n + 1) / 2 else 0) : f n = if n % 2 = 1 then (n + 1) / 2 else 0   :=  by sorry

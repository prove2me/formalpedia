-- Prove2me | Theorems.Thm_lean_workbook_plus_59191
-- name    : lean_workbook_plus_59191
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/5c6c722e-27e9-43c7-a926-8af32b697fa2
-- statement:
--   Prove that there doesn't exist a function $f:\mathbb{N} \rightarrow \mathbb{N}$ , such that $(m+f(n))^2 \geq 3f(m)^2+n^2$ for all $m, n \in \mathbb{N}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59191 (f : ℕ → ℕ) : ¬ ∀ m n, (m + f n)^2 ≥ 3 * (f m)^2 + n^2   :=  by sorry

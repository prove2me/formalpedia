-- Prove2me | Theorems.Thm_lean_workbook_plus_14271
-- name    : lean_workbook_plus_14271
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/302a05d3-0499-4681-912b-8a45937d2380
-- statement:
--   3. $f(x) = x$ for all $x$ , or $f(x) = |x|$ for all $x$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14271 (f : ℝ → ℝ) (hf: f = id ∨ f = abs) : ∀ x, f x = x ∨ ∀ x, f x = |x|   :=  by sorry

-- Prove2me | Theorems.Thm_WorkbookSource_problem_14812
-- name    : WorkbookSource.problem_14812
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T15:03:11.300148+00:00
-- url     : https://prove2.me/theorems/a18436d7-abef-4871-b500-f82e2c031631
-- title:
--   Two functional identities agree on the image
-- statement:
--   Prove that if $ f: \mathbb{R} \to \mathbb{R}$ is a monotonous function satisfying $ f(f(x)) = f( - f(x)) = f(x)^2$, then $ f(x) = f(-x)$ for all $ x\in f(\mathbb{R})$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_14812` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_14812; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_14812 (f : ℝ → ℝ) (h₁ : Monotone f) (h₂ : ∀ x, f (f x) = (f x)^2) (h₃ : ∀ x, f (-f x) = (f x)^2) : ∀ x ∈ Set.range f, f x = f (-x)  :=  by sorry

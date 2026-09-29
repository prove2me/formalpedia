-- Prove2me | Theorems.Thm_lean_workbook_plus_59850
-- name    : lean_workbook_plus_59850
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/a860997b-55e4-4d2d-b210-6f672fc353e1
-- statement:
--   We say that $f(x)$ from $A\to B$ is surjective if $f(A)=B$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59850 {f : ℕ → ℕ} : (∀ b, ∃ a, f a = b) ↔ Set.range f = Set.univ   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_75315
-- name    : lean_workbook_plus_75315
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/0aae3c66-b997-4be3-be01-04e6318ebc25
-- statement:
--   b) $f : \mathbb{Q} \rightarrow \mathbb{Q}$ so that $\mid f(x) - f(y) \mid > 1, \forall x, y \in \mathbb{Q}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75315 : ∃ f : ℚ → ℚ, ∀ x y : ℚ, abs (f x - f y) > 1   :=  by sorry

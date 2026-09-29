-- Prove2me | Theorems.Thm_WorkbookSyntax_plus_69836
-- name    : WorkbookSyntax.plus_69836
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:09:17.896108+00:00
-- url     : https://prove2.me/theorems/3a713593-d879-4efa-88cc-0732946f6a00
-- title:
--   Lean-Workbook Syntax 69836: A nonpositive sum under interval bounds
-- statement:
--   If $0\le x_i\le a$ for $0\le i<n$, then $\sum_{i=0}^{n-1}x_i(x_i-a)\le0$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_69836` (Apache-2.0), [original record](https://prove2.me/theorems/d568f50d-9c56-4740-8ce0-0f9a9f590582). This corrected declaration replaces the obsolete finite sum/product binder `in` with `∈` and restores required imports or namespaces. Ranges, casts, quantifiers, and mathematical expressions are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_69836; immutable original Prove2Me node d568f50d-9c56-4740-8ce0-0f9a9f590582

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

theorem WorkbookSyntax.plus_69836 (n : ℕ) (a : ℝ) (x : ℕ → ℝ) (h₁ : ∀ i ∈ Finset.range n, 0 ≤ x i) (h₂ : ∀ i ∈ Finset.range n, x i ≤ a) : ∑ i ∈ Finset.range n, x i * (x i - a) ≤ 0   :=  by sorry

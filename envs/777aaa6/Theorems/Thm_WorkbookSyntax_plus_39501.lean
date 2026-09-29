-- Prove2me | Theorems.Thm_WorkbookSyntax_plus_39501
-- name    : WorkbookSyntax.plus_39501
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:22:02.431067+00:00
-- url     : https://prove2.me/theorems/17e10459-3cad-4ead-8f41-a62d25c2ba3b
-- title:
--   Lean-Workbook Syntax 39501: Four reciprocal-square partial-sum bounds
-- statement:
--   For $n\in\{1,2,3,4\}$, $\sum_{k=1}^{n}1/k^2<5/3$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_39501` (Apache-2.0), [original record](https://prove2.me/theorems/7b7d9270-3f08-4e64-bf54-85615acfc0f6). This corrected declaration replaces the obsolete finite sum/product binder `in` with `∈` and restores required imports or namespaces. Ranges, casts, quantifiers, and mathematical expressions are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_39501; immutable original Prove2Me node 7b7d9270-3f08-4e64-bf54-85615acfc0f6

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Intervals

theorem WorkbookSyntax.plus_39501 : ∀ n : ℕ, n ∈ ({1, 2, 3, 4} : Finset ℕ) → ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / k ^ 2 < 5 / 3   :=  by sorry

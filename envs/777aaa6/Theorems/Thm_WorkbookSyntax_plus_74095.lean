-- Prove2me | Theorems.Thm_WorkbookSyntax_plus_74095
-- name    : WorkbookSyntax.plus_74095
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:37:39.823069+00:00
-- url     : https://prove2.me/theorems/0a165ffd-29af-40fc-8a3f-eba49ace1830
-- title:
--   Lean-Workbook Syntax 74095: A nonnegative finite sum of shifted squares
-- statement:
--   For real numbers $a_0,\ldots,a_{n-1}$, $4\sum_{i=0}^{n-1}(a_i-1/2)^2\ge0$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_74095` (Apache-2.0), [original record](https://prove2.me/theorems/423d2167-b7c3-4de8-8b37-2f6ef07a4148). This corrected declaration replaces the obsolete finite sum/product binder `in` with `∈` and restores required imports or namespaces. Ranges, casts, quantifiers, and mathematical expressions are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_74095; immutable original Prove2Me node 423d2167-b7c3-4de8-8b37-2f6ef07a4148

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

theorem WorkbookSyntax.plus_74095 (n : ℕ) (a : ℕ → ℝ) : 4 * ∑ i ∈ Finset.range n, (a i - 1 / 2)^2 ≥ 0   :=  by sorry

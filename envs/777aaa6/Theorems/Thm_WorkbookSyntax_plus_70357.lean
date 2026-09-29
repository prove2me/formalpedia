-- Prove2me | Theorems.Thm_WorkbookSyntax_plus_70357
-- name    : WorkbookSyntax.plus_70357
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:09:28.83581+00:00
-- url     : https://prove2.me/theorems/e5343819-5a35-4ed6-a55c-75386ee95078
-- title:
--   Lean-Workbook Syntax 70357: The complex binomial theorem with unit constant term
-- statement:
--   For every natural $n$ and complex $z$, $\sum_{r=0}^{n}\binom{n}{r}z^r=(1+z)^n$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_70357` (Apache-2.0), [original record](https://prove2.me/theorems/db0cc206-d101-4e78-bf54-ed436e6e8d3e). This corrected declaration replaces the obsolete finite sum/product binder `in` with `∈` and restores required imports or namespaces. Ranges, casts, quantifiers, and mathematical expressions are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_70357; immutable original Prove2Me node db0cc206-d101-4e78-bf54-ed436e6e8d3e

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Choose.Sum
open Nat

theorem WorkbookSyntax.plus_70357 (n : ℕ) (z : ℂ) : ∑ r ∈ Finset.range (n + 1), choose n r * z ^ r = (1 + z) ^ n   :=  by sorry

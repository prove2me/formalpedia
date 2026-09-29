-- Prove2me | Theorems.Thm_WorkbookSyntax_plus_67809
-- name    : WorkbookSyntax.plus_67809
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:08:41.336114+00:00
-- url     : https://prove2.me/theorems/a303a1ad-96a9-4c48-ada5-d2fe8f6582b0
-- title:
--   Lean-Workbook Syntax 67809: A finite binomial convolution
-- statement:
--   $\sum_{k=3}^{51}\binom{k}{3}\binom{52-k}{1}=\binom{53}{5}$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_67809` (Apache-2.0), [original record](https://prove2.me/theorems/ede51057-48fc-4e90-995a-8cc37eda7a47). This corrected declaration replaces the obsolete finite sum/product binder `in` with `∈` and restores required imports or namespaces. Ranges, casts, quantifiers, and mathematical expressions are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_67809; immutable original Prove2Me node ede51057-48fc-4e90-995a-8cc37eda7a47

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic

theorem WorkbookSyntax.plus_67809 (n : ℕ) : ∑ k ∈ Finset.Icc 3 51, (Nat.choose k 3 * Nat.choose (52 - k) 1) = Nat.choose 53 5   :=  by sorry

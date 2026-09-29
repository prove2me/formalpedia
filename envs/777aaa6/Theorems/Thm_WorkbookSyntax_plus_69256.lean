-- Prove2me | Theorems.Thm_WorkbookSyntax_plus_69256
-- name    : WorkbookSyntax.plus_69256
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:09:11.932102+00:00
-- url     : https://prove2.me/theorems/e52fdfff-6461-4b3b-b123-cfcbe09c68ed
-- title:
--   Lean-Workbook Syntax 69256: The hockey-stick binomial identity
-- statement:
--   For natural numbers $n,m$, $\sum_{k=0}^{m}\binom{n+k}{k}=\binom{n+m+1}{m}$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_69256` (Apache-2.0), [original record](https://prove2.me/theorems/663e0e9d-b5f5-4950-83b1-3861ed59ed32). This corrected declaration replaces the obsolete finite sum/product binder `in` with `∈` and restores required imports or namespaces. Ranges, casts, quantifiers, and mathematical expressions are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_69256; immutable original Prove2Me node 663e0e9d-b5f5-4950-83b1-3861ed59ed32

import Mathlib.Data.Nat.Choose.Sum
open Nat

theorem WorkbookSyntax.plus_69256 (n m : ℕ) : ∑ k ∈ Finset.range (m+1), choose (n + k) k = choose (n + m + 1) m   :=  by sorry

-- Prove2me | Theorems.Thm_WorkbookSyntax_plus_67158
-- name    : WorkbookSyntax.plus_67158
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:08:26.303849+00:00
-- url     : https://prove2.me/theorems/3bb7a96a-9a54-4876-b121-b590d2b55336
-- title:
--   Lean-Workbook Syntax 67158: Congruence between even and odd products
-- statement:
--   $\prod_{i=0}^{999}(2i+2)-\prod_{i=0}^{999}(2i+1)\equiv0\pmod{2001}$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_67158` (Apache-2.0), [original record](https://prove2.me/theorems/946c3638-2b50-4056-a47c-76d07ffbe1c8). This corrected declaration replaces the obsolete finite sum/product binder `in` with `∈` and restores required imports or namespaces. Ranges, casts, quantifiers, and mathematical expressions are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_67158; immutable original Prove2Me node 946c3638-2b50-4056-a47c-76d07ffbe1c8

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Int.ModEq

theorem WorkbookSyntax.plus_67158 : (∏ i ∈ Finset.range 1000, (2 * i + 2)) - (∏ i ∈ Finset.range 1000, (2 * i + 1)) ≡ 0 [ZMOD 2001]   :=  by sorry

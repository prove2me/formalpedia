-- Prove2me | Theorems.Thm_WorkbookSyntax_plus_55924
-- name    : WorkbookSyntax.plus_55924
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:10:32.603994+00:00
-- url     : https://prove2.me/theorems/d7de3466-c0f3-49a5-bffb-d8c69bef8dd5
-- title:
--   Lean-Workbook Syntax 55924: Seven consecutive cubes sum to a multiple of seven
-- statement:
--   For every integer $a$, $\sum_{i=0}^{6}(a+i)^3\equiv0\pmod7$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_55924` (Apache-2.0), [original record](https://prove2.me/theorems/b6aa43c0-59b3-4344-b30a-a2d83e6b7022). This corrected declaration replaces the obsolete finite sum/product binder `in` with `∈` and restores required imports or namespaces. Ranges, casts, quantifiers, and mathematical expressions are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_55924; immutable original Prove2Me node b6aa43c0-59b3-4344-b30a-a2d83e6b7022

import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.BigOperators.Ring.Finset

theorem WorkbookSyntax.plus_55924 (a : ℤ) :
    ∑ i ∈ Finset.range 7, (a + i) ^ 3 ≡ 0 [ZMOD 7]   :=  by sorry

-- Prove2me | Theorems.Thm_WorkbookSyntax_plus_60317
-- name    : WorkbookSyntax.plus_60317
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:19:51.834004+00:00
-- url     : https://prove2.me/theorems/f2bb05fd-4ded-4ad1-8114-7340aad771cb
-- title:
--   Lean-Workbook Syntax 60317: A finite telescoping reciprocal sum
-- statement:
--   $\sum_{k=1}^{49}1/[k(k+1)]=49/50$. The Lean declaration also includes $k=0$, whose term is zero under totalized division, so the finite sum has the same value.
--
--   Source: Lean-Workbook row `lean_workbook_plus_60317` (Apache-2.0), [original record](https://prove2.me/theorems/326f22e4-0be6-4f1e-ba00-7b31e5bedbb4). This corrected declaration replaces the obsolete finite sum/product binder `in` with `∈` and restores required imports or namespaces. Ranges, casts, quantifiers, and mathematical expressions are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_60317; immutable original Prove2Me node 326f22e4-0be6-4f1e-ba00-7b31e5bedbb4

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

theorem WorkbookSyntax.plus_60317 :
  ∑ k ∈ (Finset.range 50), (1 : ℝ) / (k * (k + 1)) = 49 / 50   :=  by sorry

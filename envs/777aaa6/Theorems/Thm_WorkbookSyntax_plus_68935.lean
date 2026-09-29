-- Prove2me | Theorems.Thm_WorkbookSyntax_plus_68935
-- name    : WorkbookSyntax.plus_68935
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:09:00.029203+00:00
-- url     : https://prove2.me/theorems/39370c47-0cee-481b-9df6-325a666a62ea
-- title:
--   Lean-Workbook Syntax 68935: A sum of consecutive integer products
-- statement:
--   $\sum_{k=1}^{99}k(k+1)=333300$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_68935` (Apache-2.0), [original record](https://prove2.me/theorems/20c3542c-3d3f-4905-827d-b3954fe9f616). This corrected declaration replaces the obsolete finite sum/product binder `in` with `∈` and restores required imports or namespaces. Ranges, casts, quantifiers, and mathematical expressions are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_68935; immutable original Prove2Me node 20c3542c-3d3f-4905-827d-b3954fe9f616

import Mathlib.Algebra.BigOperators.Intervals

theorem WorkbookSyntax.plus_68935 :
  ∑ k ∈ (Finset.Icc 1 99), (k * (k + 1)) = 333300   :=  by sorry

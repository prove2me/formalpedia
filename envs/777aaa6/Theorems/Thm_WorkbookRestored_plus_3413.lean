-- Prove2me | Theorems.Thm_WorkbookRestored_plus_3413
-- name    : WorkbookRestored.plus_3413
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:43:25.646849+00:00
-- url     : https://prove2.me/theorems/981ef9cb-a15a-4f25-af60-13c59ce7fc54
-- title:
--   The formula for choosing two elements
-- statement:
--   For every natural number $x$, $$\binom x2=\frac{x^2-x}{2}.$$
--
--   This restores the missing imports or namespaces of [the original node](https://prove2.me/theorems/0dbee549-c42f-4a38-a3de-06084b532386), retaining its formal proposition. Source: Lean-Workbook row `lean_workbook_plus_3413` (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_3413; original Prove2Me node 0dbee549-c42f-4a38-a3de-06084b532386; Apache-2.0

import Mathlib.Data.Nat.Choose.Basic
open Nat

theorem WorkbookRestored.plus_3413 : ∀ x : ℕ, choose x 2 = (x^2 - x) / 2   :=  by sorry

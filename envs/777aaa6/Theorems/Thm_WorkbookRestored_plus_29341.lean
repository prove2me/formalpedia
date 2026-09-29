-- Prove2me | Theorems.Thm_WorkbookRestored_plus_29341
-- name    : WorkbookRestored.plus_29341
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:14:16.22869+00:00
-- url     : https://prove2.me/theorems/0815beb6-6341-4504-bb41-1f6ff5c7d7a5
-- title:
--   Polynomial value differences are divisible by input differences
-- statement:
--   For an integer polynomial $P$ and distinct integers $a,b$, $a-b$ divides $P(a)-P(b)$.
--
--   This restores the missing imports or namespaces of [the original node](https://prove2.me/theorems/576b1508-4e49-420b-bbc9-fa06cec2b04d), retaining its formal proposition. Source: Lean-Workbook row `lean_workbook_plus_29341` (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_29341; original Prove2Me node 576b1508-4e49-420b-bbc9-fa06cec2b04d; Apache-2.0

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
open Polynomial

theorem WorkbookRestored.plus_29341 (P : Polynomial ℤ) {a b : ℤ} (h : a ≠ b) : a - b ∣ P.eval a - P.eval b   :=  by sorry

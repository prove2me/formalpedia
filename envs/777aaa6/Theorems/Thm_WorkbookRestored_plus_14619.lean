-- Prove2me | Theorems.Thm_WorkbookRestored_plus_14619
-- name    : WorkbookRestored.plus_14619
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:13:57.213999+00:00
-- url     : https://prove2.me/theorems/ccfc9b6b-515b-4f50-aac8-8d8adfe1b013
-- title:
--   Real polynomials are determined by their values
-- statement:
--   If real polynomials $p,q$ satisfy $p(x)=q(x)$ for every real $x$, then $p=q$.
--
--   This restores the missing imports or namespaces of [the original node](https://prove2.me/theorems/9d3361c5-b1e7-4e1f-9860-02ca9b5c7fcc), retaining its formal proposition. Source: Lean-Workbook row `lean_workbook_plus_14619` (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_14619; original Prove2Me node 9d3361c5-b1e7-4e1f-9860-02ca9b5c7fcc; Apache-2.0

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
open Polynomial

theorem WorkbookRestored.plus_14619 (p q : Polynomial ℝ) (h : ∀ x, p.eval x = q.eval x) : p = q   :=  by sorry

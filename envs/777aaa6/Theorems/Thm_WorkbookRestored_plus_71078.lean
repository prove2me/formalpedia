-- Prove2me | Theorems.Thm_WorkbookRestored_plus_71078
-- name    : WorkbookRestored.plus_71078
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:37:23.752116+00:00
-- url     : https://prove2.me/theorems/50e797b0-5915-43f3-b3a6-957411719f64
-- title:
--   Lean-Workbook Plus 71078: A polynomial with nonpositive coefficients is nonpositive
-- statement:
--   If every coefficient of a real polynomial $P$ is nonpositive, then $P(x)\le0$ for every $x\ge0$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_71078` (Apache-2.0), [original record](https://prove2.me/theorems/d22585c9-4e0b-4875-9f59-8d1f5367afd6). This repair only restores required imports and namespaces; the mathematical declaration is unchanged.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_71078; immutable original Prove2Me node d22585c9-4e0b-4875-9f59-8d1f5367afd6

import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.Real.Basic

theorem WorkbookRestored.plus_71078 (P : Polynomial ℝ) (hP : ∀ n, P.coeff n ≤ 0) (x : ℝ) (hx : 0 ≤ x) : P.eval x ≤ 0   :=  by sorry

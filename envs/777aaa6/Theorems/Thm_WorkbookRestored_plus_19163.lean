-- Prove2me | Theorems.Thm_WorkbookRestored_plus_19163
-- name    : WorkbookRestored.plus_19163
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:14:09.83519+00:00
-- url     : https://prove2.me/theorems/ba5b8e3f-66b9-4b9d-a4cc-aadca00db961
-- title:
--   Existence of a piecewise power function
-- statement:
--   For $a>0$ and $t\ge0$, there is a real function $g$ such that $g(x)=x^t$ for $x>0$, $g(0)=0$, and $g(x)=-a(-x)^t$ for $x<0$.
--
--   This restores the missing imports or namespaces of [the original node](https://prove2.me/theorems/d4eab463-c6a2-49a8-bd9a-cd8ae76e9f14), retaining its formal proposition. Source: Lean-Workbook row `lean_workbook_plus_19163` (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_19163; original Prove2Me node d4eab463-c6a2-49a8-bd9a-cd8ae76e9f14; Apache-2.0

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real

theorem WorkbookRestored.plus_19163 (a t : ℝ) (ha : a > 0) (ht : t ≥ 0) : ∃ g : ℝ → ℝ, ∀ x > 0, g x = x ^ t ∧ g 0 = 0 ∧ ∀ x < 0, g x = -a * (-x) ^ t   :=  by sorry

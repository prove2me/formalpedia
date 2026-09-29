-- Prove2me | Theorems.Thm_WorkbookRestored_plus_13994
-- name    : WorkbookRestored.plus_13994
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:13:50.767098+00:00
-- url     : https://prove2.me/theorems/85c97237-96e6-4f31-810e-a01f4c1c7b4d
-- title:
--   Strict increase of a sum of two exponential functions
-- statement:
--   The function $f(t)=4^t+9^t$ is strictly increasing on $\mathbb R$.
--
--   This restores the missing imports or namespaces of [the original node](https://prove2.me/theorems/00a504a1-8706-47b3-b5ec-1bb39e0967c0), retaining its formal proposition. Source: Lean-Workbook row `lean_workbook_plus_13994` (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_13994; original Prove2Me node 00a504a1-8706-47b3-b5ec-1bb39e0967c0; Apache-2.0

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real

theorem WorkbookRestored.plus_13994 (f : ℝ → ℝ) (h : f = fun t ↦ 4^t + 9^t) : ∀ t₁ t₂, t₁ < t₂ → f t₁ < f t₂   :=  by sorry

-- Prove2me | Theorems.Thm_WorkbookRestored_plus_43574
-- name    : WorkbookRestored.plus_43574
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:39:24.831309+00:00
-- url     : https://prove2.me/theorems/3474a985-dce6-45f2-8f08-5140054e2ac4
-- title:
--   Solving a linear system with pi
-- statement:
--   If real $I,J$ satisfy $I+J=4$ and $I-J=\pi$, then $I=(4+\pi)/2$ and $J=(4-\pi)/2$.
--
--   This restores the missing imports or namespaces of [the original node](https://prove2.me/theorems/6d52e182-3dd7-4736-bf4b-81aaa0318cd1), retaining its formal proposition. Source: Lean-Workbook row `lean_workbook_plus_43574` (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_43574; original Prove2Me node 6d52e182-3dd7-4736-bf4b-81aaa0318cd1; Apache-2.0

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Nat

theorem WorkbookRestored.plus_43574 (I J : ℝ) (h₁ : I + J = 4) (h₂ : I - J = Real.pi) : I = (4 + Real.pi) / 2 ∧ J = (4 - Real.pi) / 2   :=  by sorry

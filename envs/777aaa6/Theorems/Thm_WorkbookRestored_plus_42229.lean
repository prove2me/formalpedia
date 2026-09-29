-- Prove2me | Theorems.Thm_WorkbookRestored_plus_42229
-- name    : WorkbookRestored.plus_42229
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:39:23.409503+00:00
-- url     : https://prove2.me/theorems/dd6cf3dd-62dc-441e-bd54-81d1025e31f2
-- title:
--   Self-inverse nonzero residues modulo a prime
-- statement:
--   For a prime $p$ and nonzero residue $a\in\mathbb Z/p\mathbb Z$, $a=a^{-1}$ if and only if $a=1$ or $a=p-1$.
--
--   This restores the missing imports or namespaces of [the original node](https://prove2.me/theorems/e2eab018-45bd-45c6-9c75-6e8909248e28), retaining its formal proposition. Source: Lean-Workbook row `lean_workbook_plus_42229` (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_42229; original Prove2Me node e2eab018-45bd-45c6-9c75-6e8909248e28; Apache-2.0

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.ZMod.Basic
open Nat

theorem WorkbookRestored.plus_42229 (p : ℕ) (hp : p.Prime) (a : ZMod p) (ha : a ≠ 0) : a = a⁻¹ ↔ a = 1 ∨ a = p-1   :=  by sorry

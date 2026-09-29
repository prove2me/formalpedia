-- Prove2me | Theorems.Thm_WorkbookRestored_plus_18068
-- name    : WorkbookRestored.plus_18068
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:14:03.441161+00:00
-- url     : https://prove2.me/theorems/577a7171-05b6-4877-b968-cbd67c0b4950
-- title:
--   Nonzero residues modulo a prime have multiplicative inverses
-- statement:
--   If $p$ is prime and $a\ne0$ in $\mathbb Z/p\mathbb Z$, then $aa^{-1}=1$.
--
--   This restores the missing imports or namespaces of [the original node](https://prove2.me/theorems/5b742349-73db-4567-a88b-8f6519934828), retaining its formal proposition. Source: Lean-Workbook row `lean_workbook_plus_18068` (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_18068; original Prove2Me node 5b742349-73db-4567-a88b-8f6519934828; Apache-2.0

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.ZMod.Basic

theorem WorkbookRestored.plus_18068 (p : ℕ) (hp : p.Prime) (a : ZMod p) (ha : a ≠ 0) : a * a⁻¹ = 1   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_82024
-- name    : lean_workbook_plus_82024
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/24d92c08-f92e-4f98-81b9-f95c9c2611bd
-- statement:
--   Prove that $-1$ is a quadratic residue mod $p$ if and only if $(p - 1) / 4$ is an integer.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82024 (p : ℕ) (hp : p.Prime) : ((-1 : ZMod p) ^ 2 = 1) ↔ (p - 1) / 4 = ↑((p - 1) / 4)   :=  by sorry

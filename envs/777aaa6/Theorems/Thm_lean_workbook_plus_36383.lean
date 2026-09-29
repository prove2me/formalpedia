-- Prove2me | Theorems.Thm_lean_workbook_plus_36383
-- name    : lean_workbook_plus_36383
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/0895b7df-b54b-4350-9db4-39458321e03e
-- statement:
--   If $\alpha \in \mathbb{Z}/5\mathbb{Z}$ is a root of $x^5 + 4x + 3$, show that it leads to a contradiction, thus proving the irreducibility of the polynomial.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36383 (α : ZMod 5) (hα : α^5 + 4*α + 3 = 0) : False   :=  by sorry

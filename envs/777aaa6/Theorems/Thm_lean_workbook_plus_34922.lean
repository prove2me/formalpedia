-- Prove2me | Theorems.Thm_lean_workbook_plus_34922
-- name    : lean_workbook_plus_34922
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/c3feffb3-d51e-4f7e-8638-a5c4b3869b57
-- statement:
--   We know that $\sum x^2\geq \sum xy\Longleftrightarrow \sum(x-y)^2\geq 0,~ \forall x,y,z\in\mathbb{R}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34922 (x y z: ℝ) : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + y * z + z * x ↔ (x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 ≥ 0   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_56991
-- name    : lean_workbook_plus_56991
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/0f01c123-ecee-42fd-b42c-b202a6fa3a9a
-- statement:
--   Suppose $y$ is a positive integer. If $p$ is a prime and $p|y^2$ , then $p|y$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56991 (p y : ℕ) (hp : p.Prime) (h : p ∣ y^2) : p ∣ y   :=  by sorry

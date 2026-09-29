-- Prove2me | Theorems.Thm_lean_workbook_plus_34668
-- name    : lean_workbook_plus_34668
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/410f5dfb-25e0-42e1-b638-74f1192929ce
-- statement:
--   We have $p|(q-1)(q^2+q+1)$ and $p$ is a prime so $p|(q-1)$ or $p|(q^2+q+1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34668 (p q : ℕ) (hp : p.Prime) : p ∣ (q - 1) * (q ^ 2 + q + 1) → p ∣ q - 1 ∨ p ∣ q ^ 2 + q + 1   :=  by sorry

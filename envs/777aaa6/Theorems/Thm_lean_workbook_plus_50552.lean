-- Prove2me | Theorems.Thm_lean_workbook_plus_50552
-- name    : lean_workbook_plus_50552
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/4ef28870-6235-48a6-9a7f-73a12992c2c2
-- statement:
--   Prove that $\left ( a-b \right )^{5}+\left ( b-c \right )^{5}+\left ( c-a \right )^{5}$ is divisible by $5\left ( a-b \right )\left ( b-c \right )\left ( c-a \right )$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50552 {a b c : ℤ} : 5 * (a - b) * (b - c) * (c - a) ∣ (a - b)^5 + (b - c)^5 + (c - a)^5   :=  by sorry

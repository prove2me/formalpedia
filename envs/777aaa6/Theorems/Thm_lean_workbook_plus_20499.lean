-- Prove2me | Theorems.Thm_lean_workbook_plus_20499
-- name    : lean_workbook_plus_20499
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/be8f188d-8eec-47d8-9dbb-da0a18fe3e21
-- statement:
--   Prove or disprove: $\left(3n-20\left\lfloor\frac{n}{10}\right\rfloor\right)\equiv 0\pmod{7}$ for all $n \in \mathbb{N}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20499 : ∀ n : ℕ, (3 * n - 20 * (n / 10)) % 7 = 0   :=  by sorry

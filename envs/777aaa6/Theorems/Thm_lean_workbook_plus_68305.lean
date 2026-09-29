-- Prove2me | Theorems.Thm_lean_workbook_plus_68305
-- name    : lean_workbook_plus_68305
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/ce8d61c3-234e-4205-85a9-9493d1b5db0d
-- statement:
--   Prove that: If $p$ is prime form $4k+1$ then $\exists a \in \mathbb{N}, a<p$ and $a^2+1\mid p$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68305 (p : ℕ) (hp : p.Prime) (h : p ≡ 1 [ZMOD 4]) : ∃ a : ℕ, a < p ∧ a^2 + 1 ∣ p   :=  by sorry

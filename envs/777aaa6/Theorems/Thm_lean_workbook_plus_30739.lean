-- Prove2me | Theorems.Thm_lean_workbook_plus_30739
-- name    : lean_workbook_plus_30739
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/8b3c8304-61e7-499c-9312-4bf868b34aed
-- statement:
--   Consider $n =2$ and suppose that $\gcd(a_{1}, a_{2}) = 1$ , then there exist $M_{1}, M_{2} \in \mathbb{Z}$ such that $a_{1}M_{1} + a_{2}M_{2} = 1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30739 (a1 a2 : ℤ) (h1 : Nat.gcd a1.natAbs a2.natAbs = 1): ∃ M1 M2 : ℤ, a1 * M1 + a2 * M2 = 1   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_27618
-- name    : lean_workbook_plus_27618
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/9a8bd433-dcfd-4a40-852e-fe67b025d8d7
-- statement:
--   Given $x = 4k + n$, where $n, k \in \mathbb{Z}$, show that $x^2 \equiv n^2 \pmod{8}$ if $x \equiv n \pmod{4}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27618 (x n k : ℤ) (h₁ : x ≡ n [ZMOD 4]) : x ^ 2 ≡ n ^ 2 [ZMOD 8]   :=  by sorry

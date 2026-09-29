-- Prove2me | Theorems.Thm_lean_workbook_plus_2164
-- name    : lean_workbook_plus_2164
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/37d57277-645b-45c9-821b-4a6f7ac3c437
-- statement:
--   For all prime $p \neq 2$ , there exists some $n \in \mathbb N$ for which $p | 2^n-1$ . This is true. Since $\gcd(2, p) = 1$ , we have that $2^{\varphi(p)} = 1\pmod p$ . Then let $n = p - 1$ so $2^{p-1} = 1 \pmod p$ , thus $p | 2^{p-1} - 1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2164 (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : ∃ n : ℕ, p ∣ 2 ^ n - 1   :=  by sorry

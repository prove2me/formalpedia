-- Prove2me | Theorems.Thm_lean_workbook_plus_34897
-- name    : lean_workbook_plus_34897
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/83b4c13b-45e3-4e17-af64-7b012b45b9db
-- statement:
--   Find all functions $f:\mathbb{N}\rightarrow\mathbb{N}$ such that for any positive integers $a,b$ and $c$ the number $a-b+(b+c-f(b))c+2f(b)+f(3c-2)$ is a prime number only and only if the number $2a+(f(a)-a+3)c+f(f(b))+f(c^2)-f(a)-2$ is a prime number.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34897 (f : ℕ → ℕ) (hf: ∀ a b c : ℕ, Nat.Prime (a - b + (b + c - f b) * c + 2 * f b + f (3 * c - 2)) ↔ Nat.Prime (2 * a + (f a - a + 3 * c) + f (f b) + f (c ^ 2) - f a - 2)) : ∀ a b c : ℕ, Nat.Prime (a - b + (b + c - f b) * c + 2 * f b + f (3 * c - 2)) ↔ Nat.Prime (2 * a + (f a - a + 3 * c) + f (f b) + f (c ^ 2) - f a - 2)   :=  by sorry

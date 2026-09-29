-- Prove2me | Theorems.Thm_lean_workbook_plus_40434
-- name    : lean_workbook_plus_40434
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/385fd0d9-2237-4a69-bb16-d13783128dbc
-- statement:
--   We have that any solution to the equation must be true for an infinite subset $n \in \mathbb{N}$ , so we take the two smallest solutions, $n = p, n = q, p < q$ . We have $a + y^p = kb^p$ and $a + y^q = mb^q$ for $k, m \in \mathbb{N}$ . Subtracting, we find $y^p(y^{q-p} - 1) = b^p(k + mb^{q-p})$ . Taking both sides $\bmod b^p$ , and knowing that $b \not| y$ , we have $y^{q-p} - 1 \equiv 0 \bmod b^p$ . This tells us that $q - p$ must be of the form $c \phi(b^p)$ , for some $c \in \mathbb{N}$ , by Euler's Theorem.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40434  (a b y : ℕ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < y)
  (h₁ : b ≠ 1)
  (h₂ : ∀ n : ℕ, 1 ≤ n → (a + y^n) % (b^n) = 0) :
  ∃ p q : ℕ, p < q ∧ (q - p) % (Nat.totient (b^p)) = 0   :=  by sorry

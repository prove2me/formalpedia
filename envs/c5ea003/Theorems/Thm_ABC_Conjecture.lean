-- Prove2me | Theorems.Thm_ABC_Conjecture
-- name    : ABC_Conjecture
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-06-25T18:45:10.003493+00:00
-- url     : https://prove2.me/theorems/bdbf649d-5850-489d-9b33-5e2ca5684b06
-- statement:
--   **abc conjecture.** For every real $\varepsilon>0$ there are only finitely many triples $(a,b,c)$ of positive integers with $a+b=c$ and $a,b,c$ pairwise coprime such that $\operatorname{rad}(abc)^{1+\varepsilon}<c$, where $\operatorname{rad}(n)$ is the product of the distinct prime factors of $n$. (Statement following the DeepMind formal-conjectures library.)
-- source:
--   https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/ABC.lean

import Mathlib

open scoped BigOperators

noncomputable def radicalDM (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

theorem ABC_Conjecture (ε : ℝ) (hε : 0 < ε) :
    {abc : ℕ × ℕ × ℕ |
        0 < abc.1 ∧ 0 < abc.2.1 ∧ 0 < abc.2.2 ∧
        ({abc.1, abc.2.1, abc.2.2} : Set ℕ).Pairwise Nat.Coprime ∧
        abc.1 + abc.2.1 = abc.2.2 ∧
        (radicalDM (abc.1 * abc.2.1 * abc.2.2) : ℝ) ^ (1 + ε) < abc.2.2}.Finite := by sorry

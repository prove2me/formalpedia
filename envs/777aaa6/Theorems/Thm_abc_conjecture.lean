-- Prove2me | Theorems.Thm_abc_conjecture
-- name    : abc_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T18:25:29.52297+00:00
-- url     : https://prove2.me/theorems/b3f44bd9-a5de-45f7-b1eb-9e596c9f3875
-- statement:
--   **ABC Conjecture**: For every $\varepsilon > 0$, there are only finitely many triples $(a,b,c)$ of coprime positive integers with $a + b = c$ and $c > \operatorname{rad}(abc)^{1+\varepsilon}$, where $\operatorname{rad}(n) = \prod_{p \mid n} p$ is the radical of $n$.
--
--   Proposed by Oesterlé and Masser (1985). Implies asymptotic FLT, Szpiro's conjecture, and dozens of other deep results. Mochizuki claimed a proof via IUT theory in 2012, but it remains unverified by the community.
-- source:
--   https://en.wikipedia.org/wiki/Abc_conjecture

import Mathlib

noncomputable def radical (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

theorem abc_conjecture :
    ∀ ε : ℝ, 0 < ε →
      Set.Finite {abc : ℕ × ℕ × ℕ |
        let a := abc.1; let b := abc.2.1; let c := abc.2.2
        0 < a ∧ 0 < b ∧ 0 < c ∧
        Nat.Coprime a b ∧ Nat.Coprime b c ∧ Nat.Coprime a c ∧
        a + b = c ∧
        (c : ℝ) > (radical (a * b * c) : ℝ) ^ (1 + ε)} := by
  sorry

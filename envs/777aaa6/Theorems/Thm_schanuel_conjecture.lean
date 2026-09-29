-- Prove2me | Theorems.Thm_schanuel_conjecture
-- name    : schanuel_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T18:50:06.976821+00:00
-- url     : https://prove2.me/theorems/90081b4f-8e20-483b-bc6c-a2748d74c11c
-- statement:
--   **Schanuel's Conjecture**: If $z_1, \ldots, z_n \in \mathbb{C}$ are linearly independent over $\mathbb{Q}$, then the transcendence degree of $\mathbb{Q}(z_1, \ldots, z_n, e^{z_1}, \ldots, e^{z_n})$ over $\mathbb{Q}$ is at least $n$.
--
--   Equivalently: at least $n$ of the $2n$ numbers $z_1, \ldots, z_n, e^{z_1}, \ldots, e^{z_n}$ are algebraically independent over $\mathbb{Q}$.
--
--   Proposed by Schanuel in the 1960s (unpublished, circulated by Lang). Implies Lindemann–Weierstrass, Baker's theorem, and that $e + \pi$ is transcendental. Would settle most open questions about algebraic relations among exponentials.
--
--   **Source**: Lang, S. (1966). Introduction to Transcendental Numbers. Addison-Wesley. Also: Waldschmidt, M. (2006). Diophantine approximation, LNM 1819, Springer.
-- source:
--   https://en.wikipedia.org/wiki/Schanuel%27s_conjecture

import Mathlib

theorem schanuel_conjecture (n : ℕ) (z : Fin n → ℂ)
    (hlin : LinearIndependent ℚ z) :
    ∃ (s : Fin n → ℂ),
      AlgebraicIndependent ℚ s ∧
      ∀ i, s i ∈ Set.range z ∪ Set.range (fun i => Complex.exp (z i)) := by
  sorry

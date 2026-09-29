-- Prove2me | Theorems.Thm_green_tao_theorem__70969d
-- name    : green_tao_theorem
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-10T20:54:19.209891+00:00
-- url     : https://prove2.me/theorems/70969d21-edfb-4bee-a5b4-9b9387d459cc
-- title:
--   Green–Tao theorem: the primes contain $k$-term arithmetic progressions
-- statement:
--   **Green–Tao theorem (2004).** For every $k \ge 1$ there are natural numbers $a$ and $d \ge 1$ such that
--
--   $$a,\; a+d,\; a+2d,\; \dots,\; a+(k-1)d$$
--
--   are all prime; that is, the primes contain arithmetic progressions of every finite length.
--
--   The requirement $d \ge 1$ excludes the degenerate progression in which all terms coincide, so the $k$ listed terms are pairwise distinct.
--
--   This is the arithmetic form of the theorem of Green and Tao. It is stated here in the same shape as the existing platform theorem `green_tao_theorem` in the other Lean environments, so that reductions in this environment can cite it.
-- source:
--   B. Green and T. Tao, The primes contain arbitrarily long arithmetic progressions, Annals of Mathematics 167 (2008), 481-547, Theorem 1.1, arXiv:math/0404188, https://arxiv.org/abs/math/0404188

import Mathlib

theorem green_tao_theorem (k : ℕ) (hk : 1 ≤ k) :
    ∃ a d : ℕ, 1 ≤ d ∧ ∀ j : Fin k, Nat.Prime (a + j.val * d) := by
  sorry

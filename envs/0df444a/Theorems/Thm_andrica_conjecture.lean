-- Prove2me | Theorems.Thm_andrica_conjecture
-- name    : andrica_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T18:58:06.129632+00:00
-- url     : https://prove2.me/theorems/b31f6050-0323-4da7-9191-eb1963c04d85
-- statement:
--   **Andrica's Conjecture**: For all $n \geq 1$, $\sqrt{p_{n+1}} - \sqrt{p_n} < 1$, where $p_n$ denotes the $n$-th prime.
--
--   Proposed by Dorin Andrica in 1985. Verified for all primes up to $6.4 \times 10^{18}$ (Imran Ghory, 2004). The maximum known value of $\sqrt{p_{n+1}} - \sqrt{p_n}$ is approximately $0.670$ (at $n=1$, where $p_1=2$, $p_2=3$, giving $\sqrt{3}-\sqrt{2} \approx 0.317$). Implied by Legendre's conjecture, and implies $p_{n+1} - p_n = O(\sqrt{p_n})$.
--
--   **Source**: Andrica, D. (1985). Note on a conjecture in prime number theory. Studia Univ. Babes-Bolyai Math. 31(4), 44–48.
-- source:
--   https://en.wikipedia.org/wiki/Andrica%27s_conjecture

import Mathlib

theorem andrica_conjecture (n : ℕ) :
    Real.sqrt (Nat.nth Nat.Prime (n + 1) : ℝ) - Real.sqrt (Nat.nth Nat.Prime n : ℝ) < 1 := by
  sorry

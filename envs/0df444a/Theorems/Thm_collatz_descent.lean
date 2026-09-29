-- Prove2me | Theorems.Thm_collatz_descent
-- name    : collatz_descent
-- status  : Open
-- author  : @Zexuan Liu
-- created : 2026-09-08T03:52:31.486221+00:00
-- url     : https://prove2.me/theorems/574df5fa-afb5-46e8-b2c0-21635aee4a73
-- title:
--   Collatz descent principle: every $n > 1$ eventually drops below $n$
-- statement:
--   Let $C$ denote the Collatz step map, $C(n)=n/2$ for even $n$ and $C(n)=3n+1$ for odd $n$. The **descent principle** asserts that every starting value larger than $1$ has a finite stopping time: for every $n > 1$ there exists $m \in \mathbb{N}$ with
--
--   $$C^{m}(n) < n .$$
--
--   Equivalently, no orbit started above $1$ stays at or above its starting value forever.
--
--   This is the standard reformulation of the Collatz conjecture as a well-foundedness statement. It implies the conjecture: by strong induction on $n$, the value $n=1$ reaches $1$ in zero steps, and for $n>1$ the descent principle produces a strictly smaller point $C^{m}(n)$ of the orbit, which is still positive because positivity is preserved along orbits, so the induction hypothesis applies to it and the two segments of the orbit compose. Conversely the conjecture implies the descent principle, since an orbit that reaches $1$ from $n > 1$ has passed below $n$.
--
--   The advantage of this form is that it is local: it asks only for a bounded piece of each orbit rather than for the global behaviour, and it splits cleanly along residue classes modulo $4$. The classes $n \equiv 0, 2 \pmod 4$ are settled by a single halving step and the class $n \equiv 1 \pmod 4$ with $n > 1$ by three steps, leaving $n \equiv 3 \pmod 4$ as the open case.
--
--   **Formalization Note.** The index $m$ is not constrained to be positive because $m = 0$ cannot witness the conclusion: $n < n$ is false.
-- source:
--   https://en.wikipedia.org/wiki/Collatz_conjecture; supporting lemma for the prove2.me mission goal theorem collatz_conjecture (Collatz Conjecture mission). Jeffrey C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), 3-23, https://websites.umich.edu/~lagarias/3x%2B1.html, Section 2 (stopping time; the conjecture is equivalent to every n > 1 having finite stopping time)

import Mathlib
import Definitions.Def_collatzStepMap

theorem collatz_descent (n : ℕ) (hn : 1 < n) : ∃ m : ℕ, collatzStep^[m] n < n := by
  sorry

-- Prove2me | Theorems.Thm_edenic_semiprime_diff_squares
-- name    : edenic_semiprime_diff_squares
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-26T16:48:13.771133+00:00
-- url     : https://prove2.me/theorems/a0b0583d-34fa-56d4-8c06-78a0b72fa448
-- title:
--   Difference-of-squares representations of an Edenic semiprime
-- statement:
--   For every Edenic semiprime $n = p(p+2)$ and all $u, v \in \mathbb{N}$,
--   $$u^2 - v^2 = n \;\Longrightarrow\; \bigl(v = 1\bigr) \;\lor\; \bigl(2u = n+1 \;\land\; 2v = n-1\bigr).$$
--
--   A difference of squares factors as $u^2 - v^2 = (u+v)(u-v)$, so a representation of $n$ corresponds to a factorization $n = a b$ with $a = u+v \ge b = u-v \ge 1$ (note $u > v$, since $n > 0$). The positive divisors of $n = p(p+2)$ — a product of two distinct primes — are $1$, $p$, $p+2$ and $n$, so the factorizations with $a \ge b$ are exactly $(a,b) = (n,1)$ and $(a,b) = (p+2, p)$. Both components are odd ($n$ is odd), so $u = \tfrac{a+b}{2}$ and $v = \tfrac{a-b}{2}$ are integers:
--
--   - $(n, 1)$ gives $u = \tfrac{n+1}{2}$, $v = \tfrac{n-1}{2}$ — exactly the second disjunct $2u = n+1$, $2v = n-1$; since $v = u - 1$, this writes $n$ as a difference of *consecutive* squares;
--   - $(p+2, p)$ gives $u = \tfrac{(p+2)+p}{2} = p+1$ and $v = \tfrac{(p+2)-p}{2} = 1$ — the first disjunct, i.e. $(p+1)^2 - 1 = p^2+2p = n$.
--
--   So every representation of an Edenic semiprime as a difference of two squares is one of precisely these two shapes. For $n = 15$: $8^2 - 7^2 = 15$ and $4^2 - 1^2 = 15$; for $n = 35$: $18^2 - 17^2 = 35$ and $6^2 - 1^2 = 35$.
--
--   **Formalization.** Unfold the definition; derive $v < u$ by contradiction (if $u \le v$ then `Nat.mul_le_mul` gives $u^2 \le v^2$, and `Nat.sub_eq_zero_iff_le` makes the difference $0$, contradicting $n > 0$), factor with `Nat.sq_sub_sq`, and split the divisibility $p \mid (u+v)(u-v)$ with `Nat.Prime.dvd_mul`. In the branch $p \mid u+v$: write $u+v = p s$ via `exists_eq_mul_right_of_dvd`, cancel the common factor $p$ with `Nat.mul_left_cancel` to get $u - v \mid p+2$, and split with `Nat.Prime.eq_one_or_self_of_dvd` — $u-v = 1$ yields the half form by `omega`, while $u - v = p+2$ contradicts $u - v \le u + v$. In the branch $p \mid u-v$: cancel to $(u+v) s = p+2$, note $s \mid p+2$, and split again — $s = 1$ forces $v = 1$ by `omega`, while $s = p+2$ gives $u+v = 1$, impossible.
--
--   **Reuse.** Direct — no imports beyond the definition. The first disjunct recovers `edenic_semiprime_succ_is_square` (with $v = 1$, $n + 1 = u^2$), while the second exhibits every member of the family as a difference of consecutive squares.
-- source:
--   Original result; elementary consequence of the platform definition `IsEdenicSemiprime` (product of a twin prime pair), p2m:theorem/94d96afa-0c8a-5e9f-a2f0-b0cc98d5b1e2. Standard context: Hardy--Wright, An Introduction to the Theory of Numbers, 6th ed., on prime pairs; https://en.wikipedia.org/wiki/Prime_k-tuple

import Mathlib
import Definitions.Def_IsEdenicSemiprime

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem edenic_semiprime_diff_squares (n : ℕ) (h : IsEdenicSemiprime n) :
    ∀ u v, u ^ 2 - v ^ 2 = n → v = 1 ∨ (2 * u = n + 1 ∧ 2 * v = n - 1) := by
  sorry

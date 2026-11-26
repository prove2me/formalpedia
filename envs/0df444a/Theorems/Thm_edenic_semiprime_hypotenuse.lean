-- Prove2me | Theorems.Thm_edenic_semiprime_hypotenuse
-- name    : edenic_semiprime_hypotenuse
-- status  : Open
-- author  : @mwm
-- created : 2026-11-26T11:30:03.234653+00:00
-- url     : https://prove2.me/theorems/3e14c885-763a-4fd9-beb3-9b5d28fd322f
-- title:
--   An Edenic semiprime is the hypotenuse of a Pythagorean triple
-- statement:
--   For every Edenic semiprime $n = p(p+2)$ there exist positive integers $a, b$ with
--   $$a^2 + b^2 = n^2,$$
--   i.e. $n$ is the hypotenuse of a Pythagorean triple with both legs nonzero.
--
--   Write $n = p(p+2)$ with $p$, $p+2$ prime. As in `edenic_semiprime_neg_one_nonresidue`, one twin is $\equiv 1 \pmod 4$ — call it $q$ — and the other is $m$, so $n = qm$. Since $q \equiv 1 \pmod 4$ is prime, Fermat's two-square theorem (`Nat.Prime.sq_add_sq`) gives $q = a_0^2 + b_0^2$. Both summands are nonzero: if, say, $b_0 = 0$ then $q = a_0^2$ (or $q = 1$), contradicting primality (`Nat.not_prime_mul`). They are also unequal: $q$ is odd, so $a_0 = b_0$ would give $q = 2a_0^2$, hence $2 \mid q$ (`Nat.dvd_prime`). Symmetrizing the pair so $b < a$ therefore makes $a^2 - b^2 > 0$.
--
--   Now use the Brahmagupta identity: from $q = a^2 + b^2$,
--   $$q^2 = (a^2 + b^2)^2 = (a^2 - b^2)^2 + (2ab)^2 ,$$
--   and multiplying by $m^2$,
--   $$n^2 = (qm)^2 = \bigl((a^2 - b^2)m\bigr)^2 + \bigl(2abm\bigr)^2 .$$
--   Both legs are positive: $a^2 - b^2 > 0$ since $b < a$, $2ab > 0$ since $a, b > 0$, and $m \ge 2$ is prime. This exhibits $n^2$ as a sum of two positive squares, i.e. $n$ is the hypotenuse of a primitive-or-not triple with nonzero legs.
--
--   Sanity check: $n = 15$ takes $q = 5 = 1^2 + 2^2$, $m = 3$, giving legs $|1^2 - 2^2| \cdot 3 = 9$ and $2 \cdot 1 \cdot 2 \cdot 3 = 12$ — the familiar $9^2 + 12^2 = 225 = 15^2$ (the $3$-$4$-$5$ triple scaled by $3$); $n = 35 = 5 \cdot 7$ takes $q = 5 = 1^2 + 2^2$, $m = 7$: legs $|1 - 4| \cdot 7 = 21$ and $2 \cdot 1 \cdot 2 \cdot 7 = 28$, i.e. $21^2 + 28^2 = 441 + 784 = 1225 = 35^2$.
--
--   **Formalization.** Split $p \bmod 4$ with `omega` to isolate the twin $q \equiv 1 \pmod 4$ with $n = qm$; feed `q % 4 ≠ 3` to `Nat.Prime.sq_add_sq` under `Fact q.Prime`; derive $a_0, b_0 \neq 0$ from primality (`Nat.not_prime_mul`) and $a_0 \neq b_0$ from oddness (`Nat.dvd_prime`); normalize to $b < a$ via `le_total` so `mul_self_lt_mul_self` yields $b^2 < a^2$ (hence no truncation in $a^2 - b^2$, via `Int.ofNat_sub`); transport the Brahmagupta identity through $\mathbb{Z}$ with `push_cast`/`ring`; and assemble the legs `((a^2 - b^2) * m, 2 * a * b * m)` with positivity from `Nat.mul_pos`.
--
--   **Reuse.** Direct (no imports beyond the definition). Companion to `edenic_semiprime_neg_one_nonresidue` (the congruence obstruction modulo $n$) and `edenic_semiprime_not_sum_two_squares` (which forbids $n$ itself, as opposed to $n^2$, from being a sum of two squares).
-- source:
--   Original result; elementary consequence of the platform definition `IsEdenicSemiprime` (product of a twin prime pair), p2m:theorem/94d96afa-0c8a-5e9f-a2f0-b0cc98d5b1e2. Standard context: Hardy--Wright, An Introduction to the Theory of Numbers, 6th ed., on prime pairs; https://en.wikipedia.org/wiki/Prime_k-tuple

import Mathlib
import Definitions.Def_IsEdenicSemiprime

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem edenic_semiprime_hypotenuse (n : ℕ) (h : IsEdenicSemiprime n) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a ^ 2 + b ^ 2 = n ^ 2 := by
  sorry

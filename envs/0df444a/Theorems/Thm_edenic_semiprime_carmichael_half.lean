-- Prove2me | Theorems.Thm_edenic_semiprime_carmichael_half
-- name    : edenic_semiprime_carmichael_half
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-26T16:48:14.714977+00:00
-- url     : https://prove2.me/theorems/d8c19cc7-5eab-468a-af1c-25731d5f53c0
-- title:
--   An Edenic semiprime fails the Korselt divisibility p + 1 ∣ n − 1
-- statement:
--   For every Edenic semiprime $n = p(p+2)$ there is a witnessing twin pair:
--   $$\exists\, p,\quad p \text{ prime} \;\land\; p+2 \text{ prime} \;\land\; n = p(p+2) \;\land\; \lnot\,(p+1 \mid n-1).$$
--
--   Korselt's criterion characterizes Carmichael numbers: $n$ is Carmichael if and only if $n$ is squarefree and $q - 1 \mid n - 1$ for every prime $q$ dividing $n$. For an Edenic semiprime the prime divisors are the twins $p$ and $p+2$, so the criterion would require both $p - 1 \mid n-1$ and $p+1 \mid n-1$. This target shows the second of these divisibilities *always fails* — "half" of the Korselt test — so no Edenic semiprime can be a Carmichael number, whatever the status of the first condition.
--
--   The failure is structural. From $n + 1 = (p+1)^2$ (the identity behind `edenic_semiprime_succ_is_square`) we get $n - 1 = (p+1)^2 - 2$. If $p+1$ divided both $n-1$ and $(p+1)^2 = n+1$, it would divide their difference $2$; but $p \ge 3$ (the pair $(2,4)$ is not twin primes) gives $p + 1 \ge 4 > 2$. Note the sharp contrast: $p+1$ *does* divide $n+1$ (it is a square of $p+1$) yet never divides $n-1$.
--
--   **Formalization.** Unfold the definition to the specific pair with `refine ⟨p, hp, hp2, rfl, ?_⟩`; under the assumption $p+1 \mid n-1$, the identity $p(p+2)+1 = (p+1)^2$ (`ring`) provides $p+1 \mid n+1$ via `Nat.dvd_mul_right`, and `Nat.dvd_sub` subtracts to $p+1 \mid 2$; `Nat.le_of_dvd` then gives $p+1 \le 2$, contradicting $p \ge 3$ (from `Nat.Prime.two_le` and $p \ne 2$) by `omega`.
--
--   **Reuse.** Direct — no imports beyond the definition. Shares the key identity $n+1 = (p+1)^2$ with `edenic_semiprime_succ_div_36` and `edenic_semiprime_succ_is_square`; a divisibility-flavored sibling of `edenic_semiprime_not_perfect`, another "no special number" obstruction for the family.
-- source:
--   Original result; elementary consequence of the platform definition `IsEdenicSemiprime` (product of a twin prime pair), p2m:theorem/94d96afa-0c8a-5e9f-a2f0-b0cc98d5b1e2. Standard context: Hardy--Wright, An Introduction to the Theory of Numbers, 6th ed., on prime pairs; https://en.wikipedia.org/wiki/Prime_k-tuple

import Mathlib
import Definitions.Def_IsEdenicSemiprime

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem edenic_semiprime_carmichael_half (n : ℕ) (h : IsEdenicSemiprime n) :
    ∃ p, p.Prime ∧ (p + 2).Prime ∧ n = p * (p + 2) ∧ ¬(p + 1 ∣ n - 1) := by
  sorry

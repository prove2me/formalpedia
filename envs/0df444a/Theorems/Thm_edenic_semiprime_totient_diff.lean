-- Prove2me | Theorems.Thm_edenic_semiprime_totient_diff
-- name    : edenic_semiprime_totient_diff
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-25T23:06:11.263075+00:00
-- url     : https://prove2.me/theorems/999a82fc-bb2f-5565-8bbb-c357bbe13388
-- title:
--   The totient deficit of an Edenic semiprime is 2p+1
-- statement:
--   For an Edenic semiprime $n = p(p+2)$ with witness $p$,
--   $$n - \varphi(n) = 2p + 1 .$$
--
--   Euler's totient is multiplicative on coprime arguments (`Nat.totient_mul`) and $\varphi(q) = q-1$ for prime $q$ (`Nat.totient_prime`). The twin factors are coprime (`twin_primes_coprime`), so
--   $$\varphi(n) = \varphi(p)\,\varphi(p+2) = (p-1)(p+1) = p^2 - 1 ,$$
--   and since $n = p^2 + 2p$,
--   $$n - \varphi(n) = (p^2 + 2p) - (p^2 - 1) = 2p + 1 .$$
--
--   So the "totient defect" $n - \varphi(n)$ — the count of integers in $[1,n]$ sharing a factor with $n$ — grows exactly linearly in the lower twin prime: $7$ for $n = 15$, $13$ for $n = 35$, $27$ for $n = 143$. Compare the generic bound $n - \varphi(n) \ge \sqrt n$ for composite $n$; here the defect is much smaller than $n$ itself, reflecting that $n$ has only two prime factors.
--
--   **Formalization.** Rewrite $\varphi(n)$ through `Nat.totient_mul`/`Nat.totient_prime` (normalizing $(p+2)-1$ to $p+1$), then the identity $p(p+2) - (p-1)(p+1) = 2p+1$ is proved by substituting $p = s+1$ (so no truncated subtraction remains) and closing with `ring`/`Nat.add_sub_cancel_left`.
--
--   **Reuse.** Direct. Companion to `edenic_semiprime_totient` (which states $\varphi(n) = (p-1)(p+1)$ as the witness); this variant packages the subtracted form $n - \varphi(n)$.
-- source:
--   Original result; elementary consequence of the platform definition `IsEdenicSemiprime` (product of a twin prime pair), p2m:theorem/94d96afa-0c8a-5e9f-a2f0-b0cc98d5b1e2. Standard context: Hardy--Wright, An Introduction to the Theory of Numbers, 6th ed., on prime pairs; https://en.wikipedia.org/wiki/Prime_k-tuple

import Mathlib
import Definitions.Def_IsEdenicSemiprime

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem edenic_semiprime_totient_diff (n : ℕ) (h : IsEdenicSemiprime n) :
    ∃ p, p.Prime ∧ (p + 2).Prime ∧ n = p * (p + 2) ∧ n - n.totient = 2 * p + 1 := by
  sorry

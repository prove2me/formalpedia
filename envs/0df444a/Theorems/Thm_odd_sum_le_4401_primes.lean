-- Prove2me | Theorems.Thm_odd_sum_le_4401_primes
-- name    : odd_sum_le_4401_primes
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T07:27:46.256561+00:00
-- url     : https://prove2.me/theorems/943210a2-1eaa-4873-886f-ebe8cb606da7
-- title:
--   Every odd number greater than 1 is the sum of at most 4401 primes
-- statement:
--   Every odd integer greater than $1$ is the sum of at most $4401$ primes.
--
--   $$\forall\ n>1\ \text{odd},\quad \exists\ \text{primes } p_1,\dots,p_k,\ k \le 4401,\quad n = p_1 + \dots + p_k.$$
--
--   This improves the platform's proved entry `odd_sum_le_6101_primes` in the odd-Goldbach campaign by replacing the multiplicative Schnirelmann iteration $\sigma(hA)\ge 1-(1-\sigma(A))^h$ (which needed $m=1525$ and a kernel-checked bound $(2199/2200)^{1525}<1/2$) with the additive Mann iteration $\sigma(hA)\ge\min(1, h\,\sigma(A))$ from Mann's theorem $\sigma(D+E)\ge\min(1,\sigma(D)+\sigma(E))$. Combined with the sharper density input $\sigma(A)\ge 1/2200$ for the two-odd-prime sumset $A=B+B$, $B=\{(p-3)/2 : p$ an odd prime$\}$, taking $h=1100$ gives $\sigma(1100A)\ge 1/2$, and the cover lemma (sum of two sets whose Schnirelmann densities add to at least $1$, both containing $0$, is everything) yields $1100A+1100A=\mathbb{N}$. Each element of $1100A$ is $2200$ odd primes summing to $2t+13200$, so every odd $n\ge 13203$ is $3$ plus $4400$ odd primes. The remaining odd $n$ are handled by explicit padding with $3$s and $2$s: $8803\le n\le 13201$ uses exactly $4401$ such primes, and $3\le n\le 8801$ uses at most $4400$.
--
--   The campaign context: Schnirelmann (1930) proved some finite bound; the platform has proved $100001$, $97041$, $6101$; the literature contains $6$ (Ramare) and $5$ (Tao), and $3$ (Helfgott) is optimal since $27$ is neither prime nor $2$ plus a prime. This entry lands the first improvement below $6101$ on the platform, via Mann's theorem — the exact $\alpha+\beta$ tool Schnirelmann's original approach lacked.
--
--   **Formalization Note** The primes form a `Multiset ℕ`; the three-case numerical decomposition ($n \ge 13203$, $8803 \le n \le 13201$, $n \le 8801$) is by `Nat` arithmetic (`omega`), and the analytic inputs are the platform theorems `Schnir.density_A_2200` and `Schnirelmann.mann` plus Mathlib's `add_eq_univ_of_one_le_schnirelmannDensity_add_schnirelmannDensity`.
-- source:
--   Schnirelmann-type route with Mann's theorem (H. B. Mann, Ann. of Math. 43 (1942), 523-527; iteration form); density input sigma(A) >= 1/2200 from the accepted solution dfb232e4 of odd_sum_le_6101_primes; structure mirrors the proved odd_sum_le_6101_primes and odd_sum_le_100001_primes entries of the odd-Goldbach campaign

import Mathlib

theorem odd_sum_le_4401_primes (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 4401 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by sorry

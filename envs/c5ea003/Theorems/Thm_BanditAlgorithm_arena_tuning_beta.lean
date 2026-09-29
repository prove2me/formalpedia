-- Prove2me | Theorems.Thm_BanditAlgorithm_arena_tuning_beta
-- name    : BanditAlgorithm.arena_tuning_beta
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-04T04:09:16.570425+00:00
-- url     : https://prove2.me/theorems/0043d996-6577-4a84-92b5-e5e0e375fcff
-- title:
--   Main term dominates $\sqrt{DSAn}/12500$ in the MDP minimax lower bound
-- statement:
--   With the notation of the parameter tuning of the minimax lower bound for average-reward Markov decision processes (Lattimore--Szepesv\'ari, *Bandit Algorithms*, Theorem 38.7) — horizon $n$, number of alternatives $k$, mean episode length $\lambda$, mean sojourn $\rho$, truncation level $N$, denominator $\mathrm{den}$, and $R=\sqrt{k\lambda/(2(n+\rho))}$ — the main term of the regret bound is
--   $$\text{main}=\tfrac{3969}{65536}\,\rho N R.$$
--
--   This lemma states that a sixth of the main term already dominates the target rate: $$\frac{\text{main}}{6}\;\ge\;\frac{1}{12500}\sqrt{D\,S\,A\,n},$$ where $D$ is the diameter budget and $SA$ the product of the numbers of states and actions.  Combined with the companion statement that the additive transient is at most $5/6$ of the main term, this yields a regret bound of order $\sqrt{DSAn}$ with the explicit constant $1/12500$.
--
--   The structural hypotheses are $n+\rho\le\frac{25}{24}n$, $14\lambda+\frac{1024}{105}\mathrm{den}\le\frac{4}{25}n$, $n-14\lambda\le N\,\mathrm{den}$, and $2899\,DSA\,\mathrm{den}^2\le 10^7\rho^2k\lambda$.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), https://tor-lattimore.com/downloads/book/book.pdf, section 38.7 (printed pp. 529-532, PDF pp. 538-541), Step 2 of the proof of Theorem 38.7; the parameter tuning after eq. (38.24).

import Mathlib.Data.Real.Sqrt

theorem BanditAlgorithm.arena_tuning_beta
    (n k lam rho den N R D SA : ℝ)
    (hn : 0 < n) (hk : 0 < k) (hlam : 0 < lam) (hden : 0 < den) (hrho : 1 ≤ rho)
    (hD : 0 < D) (hSA : 0 < SA)
    (hR0 : 0 ≤ R) (hR2 : R ^ 2 = k * lam / (2 * (n + rho)))
    (hN0 : 0 ≤ N) (hNden : n - 14 * lam ≤ N * den)
    (hnr : n + rho ≤ 25 / 24 * n)
    (hg : 14 * lam + 1024 / 105 * den ≤ 4 / 25 * n)
    (hB : 2899 * (D * SA) * den ^ 2 ≤ 10 ^ 7 * rho ^ 2 * (k * lam)) :
    1 / 12500 * Real.sqrt (D * SA * n) ≤ 3969 / 65536 * rho * N * R / 6 := by sorry

-- Prove2me | Theorems.Thm_BanditAlgorithm_cesaro_average_forgets_transient
-- name    : BanditAlgorithm.cesaro_average_forgets_transient
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-01T15:45:31.019913+00:00
-- url     : https://prove2.me/theorems/5afac874-669d-4f5a-b819-fe354d2d6b5c
-- title:
--   Cesàro averages forget a transient: $\frac1n N(n)\to a$
-- statement:
--   Let $N$ follow a target sequence $p$ to within $C$, in the sense that $|N(n)-\sum_{s<n}p(s)|\le C$ for every $n$, and suppose $|p(s)-a|\le B$ for all $s$ and $|p(s)-a|\le\delta$ for all $s\ge M$. Then for every $n\ge 1$
--   $$\Big|\frac{N(n)}{n}-a\Big|\ \le\ \frac{C+MB}{n}+\delta .$$
--
--   The transient before round $M$ contributes $MB/n$ and nothing more: an average forgets a bad prefix at rate $1/n$, whatever happens in it.
--
--   Read in the contrapositive — which is how it is used — the estimate says that if the average is *not* within $\xi$ of $a$ at round $n$, then the target cannot have settled before round $\asymp\xi n$. That is what allows a weighted failure series for the average to be traded for a higher-moment failure series for the target: a single late failure of the target can spoil only the $O(n)$ rounds below it, so exchanging the two sums replaces a linear weight by a quadratic one.
--
--   This is the deterministic step in the tracking half of Garivier and Kaufmann's Proposition 13, isolated from the bandit setting: $p$, $N$ and $a$ are arbitrary reals.
-- source:
--   Garivier & Kaufmann, Optimal Best Arm Identification with Fixed Confidence, COLT 2016, the Cesaro step in the proof of Proposition 13; Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Lemma 33.8.

import Definitions.Def_TrackAndStop

open Finset

theorem BanditAlgorithm.cesaro_average_forgets_transient
    {p N : ℕ → ℝ} {a C B δ : ℝ} {M : ℕ}
    (hC : ∀ n : ℕ, |N n - ∑ s ∈ Finset.range n, p s| ≤ C)
    (hB : ∀ s : ℕ, |p s - a| ≤ B) (hδ : 0 ≤ δ)
    (htail : ∀ s : ℕ, M ≤ s → |p s - a| ≤ δ)
    {n : ℕ} (hn : 0 < n) :
    |N n / (n : ℝ) - a| ≤ (C + (M : ℝ) * B) / (n : ℝ) + δ := by
  sorry

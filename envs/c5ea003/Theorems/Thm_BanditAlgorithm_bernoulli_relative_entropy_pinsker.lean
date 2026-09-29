-- Prove2me | Theorems.Thm_BanditAlgorithm_bernoulli_relative_entropy_pinsker
-- name    : BanditAlgorithm.bernoulli_relative_entropy_pinsker
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-26T01:49:53.276726+00:00
-- url     : https://prove2.me/theorems/ce2927bb-d231-4315-ad7b-f2f12531da6f
-- statement:
--   (Pinsker's inequality for Bernoulli distributions, L&S Lemma 10.2(b)) For $p \in [0,1]$ and $q \in (0,1)$:
--
--   $$d(p,q) \ge 2(p-q)^2.$$
--
--   (The book states Lemma 10.2 for $p,q \in [0,1]$; at $q \in \{0,1\}$ the inequality is the contentless $\infty \ge 2(p-q)^2$, resp. $0 \ge 0$, which the real-valued junk convention cannot express, hence $q \in (0,1)$. Lemma 10.2's other parts — convexity of $d(\cdot,q)$ and $d(p,\cdot)$ with unique minimizers at $q$ resp. $p$, and part (c): $p \le q-\varepsilon \le q \Rightarrow d(p,q-\varepsilon) \le d(p,q) - 2\varepsilon^2$ — are recorded in the Lemma 10.2 milestone.)
-- source:
--   L&S Lemma 10.2, p.135

import Definitions.Def_bernoulliRelativeEntropy

theorem BanditAlgorithm.bernoulli_relative_entropy_pinsker (p q : ℝ)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    2 * (p - q) ^ 2 ≤ bernoulliRelativeEntropy p q := by
  sorry

-- Prove2me | Theorems.Thm_BanditAlgorithm_alloc_settling_of_tracking_and_target_accuracy
-- name    : BanditAlgorithm.alloc_settling_of_tracking_and_target_accuracy
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-01T20:31:24.067051+00:00
-- url     : https://prove2.me/theorems/e3d2215b-3fa5-4f8f-b47c-63115519dd2a
-- title:
--   Tracking a target allocation settles the empirical allocation
-- statement:
--   Fix a Gaussian bandit with means $\mu$ and a sampling rule, and suppose that on a full-measure set $G$ of trajectories the rule tracks a *target* $p_\omega(s)\in\mathcal P_{k-1}$, in the sense that the pull counts follow its partial sums to within a constant,
--   $$\Big|T_i(n)-\sum_{s<n}p_\omega(s)_i\Big|\le C\qquad (n\ge 0,\ i\in[k]),$$
--   and that the target is within $\xi/2$ of a limit $\alpha$ from a fixed round $S_0$ on as soon as the empirical means are $\varepsilon$-accurate. Suppose also that the rule explores enough that $T_j(t)\ge\sqrt t-2k$ almost surely. Then for every $\xi>0$ the empirical allocation is eventually within $\xi$ of $\alpha$ almost surely, and
--   $$\sum_{n\ge 0}(n+1)\,\mathbb P\big(\exists i,\ |T_i(n)/n-\alpha_i|>\xi\big)<\infty .$$
--
--   This is the allocation half of Garivier and Kaufmann's Proposition 13, separated from the rule that realises it: nothing here is special to D-Tracking, only tracking and continuity of the plug-in map are used. The two hypotheses are deterministic properties of the rule; all of the probabilistic content enters through the accuracy of the means.
--
--   The proof trades a moment for a delay. A Cesàro average forgets its transient at rate $1/n$, so an allocation failure at round $n$ cannot be caused by anything before round $\asymp\xi n/4$: it forces a failure of the *means* at some round $m\ge\lceil(\xi/4)n\rceil$. Exchanging the two sums charges each mean failure at $m$ for the $O(m)$ allocation rounds below it, which converts the weight $n+1$ into $(m+1)^2$ — and the quadratically weighted mean-failure series converges because the forced-exploration floor makes each term sub-exponential in $\sqrt m$.
--
--   The almost-sure half is then Borel–Cantelli applied to the same series, so no separate consistency argument for the estimates is needed.
-- source:
--   Garivier & Kaufmann, Optimal Best Arm Identification with Fixed Confidence, COLT 2016, Proposition 13 (allocation half), with the tracking argument of Lemma 8; Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Theorem 33.6 and Lemma 33.8.

import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal Filter

theorem BanditAlgorithm.alloc_settling_of_tracking_and_target_accuracy
    {k : ℕ} [NeZero k] (μvec : Fin k → ℝ)
    (pol : BanditAlgorithm.BanditPolicy k)
    (p : (ℕ → Fin k × ℝ) → ℕ → Fin k → ℝ) (α : Fin k → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (G : Set (ℕ → Fin k × ℝ))
    (hG : BanditAlgorithm.banditTrajMeasure
      (BanditAlgorithm.gaussianBandit μvec) pol Gᶜ = 0)
    (hα0 : ∀ i, 0 ≤ α i) (hα1 : ∀ i, α i ≤ 1)
    (hp0 : ∀ ω s i, 0 ≤ p ω s i) (hp1 : ∀ ω s i, p ω s i ≤ 1)
    (htrack : ∀ ω ∈ G, ∀ (n : ℕ) (i : Fin k),
      |(BanditAlgorithm.trajPullCount i n ω : ℝ)
        - ∑ s ∈ Finset.range n, p ω s i| ≤ C)
    (hcount : ∀ᵐ ω ∂(BanditAlgorithm.banditTrajMeasure
        (BanditAlgorithm.gaussianBandit μvec) pol),
      ∀ (t : ℕ) (j : Fin k),
        Real.sqrt (t : ℝ) - 2 * (k : ℝ) ≤ (BanditAlgorithm.trajPullCount j t ω : ℝ))
    {ξ : ℝ} (hξ : 0 < ξ) {ε : ℝ} (hε : 0 < ε) {S₀ : ℕ}
    (hmod : ∀ ω ∈ G, ∀ s : ℕ, S₀ ≤ s →
      (∀ l, |BanditAlgorithm.trajEmpiricalMean l s ω - μvec l| ≤ ε) →
      ∀ j, |p ω s j - α j| ≤ ξ / 2) :
    (∀ᵐ ω ∂(BanditAlgorithm.banditTrajMeasure
        (BanditAlgorithm.gaussianBandit μvec) pol),
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          (0 < n ∧ ∀ i, |BanditAlgorithm.trajAllocation i n ω - α i| ≤ ξ))
      ∧ ∑' n : ℕ, ((n : ℝ≥0∞) + 1) *
          BanditAlgorithm.banditTrajMeasure
            (BanditAlgorithm.gaussianBandit μvec) pol
            {ω : ℕ → Fin k × ℝ |
              0 < n ∧ ∀ i, |BanditAlgorithm.trajAllocation i n ω - α i| ≤ ξ}ᶜ ≠ ⊤ := by
  sorry

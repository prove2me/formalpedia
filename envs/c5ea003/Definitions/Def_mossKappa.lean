-- Prove2me | Definitions.Def_mossKappa
-- name    : mossKappa
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-07-29T02:05:15.099528+00:00
-- url     : https://prove2.me/theorems/1477c1d3-3b81-46eb-9e80-2f66eb0ac63e
-- title:
--   MOSS index count $\kappa_i$ and optimal-arm index shortfall
-- statement:
--   Two quantities from the MOSS analysis of Lattimore--Szepesvári, *Bandit Algorithms*, proof of Theorem 9.1 (printed pp. 125--126).
--
--   **The index count $\kappa_i$.** For a suboptimal arm $i$, the source counts the sample sizes at which the arm's own MOSS index, formed from its first $s$ observations, is still optimistic enough to justify a pull:
--
--   $$\kappa_i \;=\; \sum_{s=1}^{n} \mathbb 1\!\left\{\hat\mu_{i,s} + \sqrt{\tfrac{4}{s}\log^+\!\Big(\tfrac{n}{ks}\Big)} \;\ge\; \mu_i + \tfrac{\Delta_i}{2}\right\}.$$
--
--   This is `mossKappa`. The book's armwise estimate is stated for $\kappa_i$, not for the pull count $T_i(n)$; the two are linked only on a good event (see below).
--
--   **The optimal arm's index shortfall.** The source writes $\Delta$ (renamed here to `mossOptimalShortfall`, to avoid collision with the suboptimality gaps $\Delta_i$) for how far the MOSS index of an optimal arm $i^*$ ever falls below that arm's true mean over the horizon:
--
--   $$\tilde\Delta \;=\; \left(\mu^{*} - \min_{1 \le s \le n}\left(\hat\mu_{i^{*},s} + \sqrt{\tfrac{4}{s}\log^+\!\Big(\tfrac{n}{ks}\Big)}\right)\right)^{+}.$$
--
--   Arms whose gap is much larger than $\tilde\Delta$ are not played often — precisely, $T_i(n) \le \kappa_i$ holds on the event $\{2\tilde\Delta < \Delta_i\}$ — while arms with gaps below $\tilde\Delta$ may be played linearly often, a cost controlled globally by $\mathbb E[2n\tilde\Delta] \le 16\sqrt{kn}$.
--
--   Two auxiliaries are included: `armPullRounds`, the increasing list of rounds at which an arm was played, and `armEmpiricalMeanAt i s`, the average of the rewards from that arm's first $s$ pulls (junk value $0$ at $s=0$), which is the $\hat\mu_{i,s}$ appearing above.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), proof of Theorem 9.1, printed pp. 125-126 / PDF pp. 133-134: the definition of the random variable Delta (optimal-arm index shortfall) on p. 125 and the definition of kappa_i on p. 126. https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_mossPolicy

/-!
Lattimore & Szepesvári, *Bandit Algorithms* (CUP 2020), proof of Theorem 9.1,
printed pp. 125-126.

Two quantities used by the MOSS analysis of the large-gap arms.

`mossOptimalShortfall` is the random variable written `∆` in the source
(renamed to avoid collision with the suboptimality gaps `∆ i`): the amount by
which the MOSS index of an optimal arm drops below that arm's true mean over
the horizon,
`(μ* − min_{s ≤ n} (μ̂_{i*,s} + sqrt ((4/s) log⁺ (n/(k s)))))⁺`.

`mossKappa` is the count `κ_i` of sample sizes `s ≤ n` at which arm `i`'s own
MOSS index, formed from its first `s` samples, is still at least
`μ_i + ∆_i/2`. The source bounds `∆_i E[κ_i]` armwise, and `T_i(n) ≤ κ_i`
holds on the event `2 * mossOptimalShortfall < ∆_i`.
-/

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

/-- The rounds at which arm `i` was played, in increasing order. -/
def armPullRounds {k n : ℕ} (i : Fin k) (h : BanditHistory k n) : List (Fin n) :=
  {t | (h t).1 = i}.toFinset.sort (· ≤ ·)

/-- The empirical mean `μ̂_{i,s}` of arm `i` after its first `s` pulls in the
history `h`: the average of the rewards collected at the first `s` rounds where
arm `i` was played (junk value `0` when `s = 0`). -/
noncomputable def armEmpiricalMeanAt {k n : ℕ} (i : Fin k) (s : ℕ)
    (h : BanditHistory k n) : ℝ :=
  (((armPullRounds i h).take s).map (fun t ↦ (h t).2)).sum / (s : ℝ)

/-- The MOSS index of arm `i` built from its first `s` samples,
`μ̂_{i,s} + sqrt ((4/s) * log⁺ (horizon / (k s)))`
(L&S proof of Theorem 9.1, p. 126). -/
noncomputable def mossIndexAt {k n : ℕ} (horizon : ℕ) (i : Fin k) (s : ℕ)
    (h : BanditHistory k n) : ℝ :=
  armEmpiricalMeanAt i s h +
    Real.sqrt ((4 / (s : ℝ)) * logPlus ((horizon : ℝ) / ((k : ℝ) * (s : ℝ))))

/-- `κ_i`: the number of sample sizes `s ∈ {1, …, n}` at which arm `i`'s MOSS
index formed from its first `s` samples is at least `μ_i + ∆_i/2`
(L&S proof of Theorem 9.1, p. 126). -/
noncomputable def mossKappa {k n : ℕ} (ν : StochasticBandit k) (i : Fin k)
    (h : BanditHistory k n) : ℕ :=
  ((Finset.Icc 1 n).filter
    (fun s ↦ banditArmMean ν i + banditGap ν i / 2 ≤ mossIndexAt n i s h)).card

/-- The shortfall `∆` of an optimal arm's MOSS index below its true mean
(L&S proof of Theorem 9.1, p. 125):
`(μ_{i*} − min_{1 ≤ s ≤ n} (μ̂_{i*,s} + sqrt ((4/s) log⁺ (n/(k s)))))⁺`. -/
noncomputable def mossOptimalShortfall {k n : ℕ} (ν : StochasticBandit k)
    (iStar : Fin k) (h : BanditHistory k n) : ℝ :=
  max 0 (banditArmMean ν iStar - ⨅ s : Fin n, mossIndexAt n iStar ((s : ℕ) + 1) h)

end BanditAlgorithm



-- Prove2me | Theorems.Thm_WiretapFeedback_activeStein
-- name    : WiretapFeedback.activeStein
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:02:50.313539+00:00
-- url     : https://prove2.me/theorems/406b89d2-f232-4653-aa52-b6342ab0f28f
-- title:
--   Theorem 4 — adaptive Stein lemma for discriminating two channels
-- statement:
--   Let $W,V:\mathcal X\to\mathcal O$ be discrete memoryless channels on finite alphabets, and let $\beta_\epsilon(W,V,n)$ be the optimal type-II error probability of $n$-length active hypothesis testing with type-I error at most $\epsilon$. For every $0<\epsilon<1$,
--   $$
--   \lim_{n\to\infty}-\frac1n\log\beta_\epsilon(W,V,n)=\max_{P_X}D(W\|V|P_X)=\max_x D(W_x\|V_x),
--   $$
--   where $W_x$ and $V_x$ denote the $x$-th rows of $W$ and $V$. Both equalities hold in $[0,+\infty]$.
--
--   The result is cited in the paper from Hayashi (IEEE Trans. Inf. Theory 55, 2009) and not proved there. It says that feedback and adaptivity do not improve the Stein exponent for discriminating two classical channels. In the proof of Theorem 1 it turns the finite-blocklength bound of Theorem 6 into an asymptotic rate bound.
--
--   **Formalization Note** Logarithms are base 2 and $-\log\beta$ is extended-real valued, so the infinite case (some $W_x$ not absolutely continuous with respect to $V_x$, where $\beta$ vanishes for large $n$) is included. The maxima are suprema in the extended reals (they are attained).
--
--   Differences from the source:
--   - encoding: log (base fixed by ⌊2^{nR}⌋), −log β real-valued → Real.logb 2; −log β as negLog2 in EReal (+∞ at β = 0); reason: Lean convention; β = 0 is reachable and −log 0 = +∞ is the page's value
--   - encoding: lim and max of [0, +∞]-valued quantities → Tendsto in EReal; max as ⨆ over FinDist X and over X; reason: Lean convention; the maxima are attained (finite set, compact simplex)
--   - encoding: D(W‖V|P_X) = Σ_x P_X(x) D(W_x‖V_x) → condDiv W V P_X = D(P_X W ‖ P_X V); reason: chain rule identity with 0·∞ = 0; same value for every P_X
--   - encoding: active test with (possibly randomized) e_t : 𝓕^t → X, f_t : O^t → 𝓕, t = 1, …, n → FeedbackStrategy with local randomness of arbitrary type, arbitrary feedback alphabet, 0-based rounds; reason: Lean convention; the same class of active tests
-- source:
--   Hayashi–Tyagi–Watanabe, Strong Converse for a Degraded Wiretap Channel via Active Hypothesis Testing, arXiv:1410.0443v1, §III, p.3, Theorem 4

import Mathlib
import Definitions.Def_WiretapFeedback_negLog2
import Definitions.Def_WiretapFeedback_activeBeta
import Definitions.Def_WiretapFeedback_condDiv

open Filter Topology

namespace WiretapFeedback

/-- **Theorem 4** (Hayashi–Tyagi–Watanabe, arXiv:1410.0443v1, p. 3; cited there from Hayashi,
*Discrimination of two channels by adaptive methods*, IEEE Trans. IT 55 (2009), not proved in the
paper). For channels `W, V : X → O` on finite alphabets and `0 < ϵ < 1`,
`lim_n −(1/n) log β_ϵ(W, V, n) = max_{P_X} D(W‖V|P_X) = max_x D(W_x‖V_x)`.

**Formalization Note** Base-2 logarithms; `−log β` is `negLog2` (`+∞` at `β = 0`), and the limit,
the maxima and the divergences are in `EReal`, so the infinite case (some `W_x` not absolutely
continuous with respect to `V_x`) is included. `max` is `⨆` (attained on the finite set /
compact simplex). `D(W‖V|P_X)` is `condDiv`, the joint form `D(P_X W‖P_X V)`. Both equalities of
the display are stated. -/
theorem activeStein {X O : Type} [Fintype X] [Fintype O] (W V : WildeQIT.Channel X O) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun n : ℕ => (((1 : ℝ) / n : ℝ) : EReal) * negLog2 (activeBeta ε W V n)) atTop
        (𝓝 (⨆ p : WildeQIT.FinDist X, condDiv W V p)) ∧
      (⨆ p : WildeQIT.FinDist X, condDiv W V p) = ⨆ x : X, WildeQIT.relEntropy (W x) (V x).prob := by sorry

end WiretapFeedback

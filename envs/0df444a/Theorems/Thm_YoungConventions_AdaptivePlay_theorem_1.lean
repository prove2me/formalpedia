-- Prove2me | Theorems.Thm_YoungConventions_AdaptivePlay_theorem_1
-- name    : YoungConventions.AdaptivePlay.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:04:22.99998+00:00
-- url     : https://prove2.me/theorems/1b98d84c-622c-4672-b522-c0bb8fa35de2
-- title:
--   Theorem 1 — in a weakly acyclic game, adaptive play with $k \le m/(L_\Gamma+2)$ converges almost surely to a convention
-- statement:
--   Let $\Gamma$ be a weakly acyclic game with finitely many players, finite nonempty strategy sets $S_i$ and real payoffs. Let $L_\Gamma$ be the largest, over all strategy tuples, of the length of a shortest best-reply path to a strict Nash equilibrium. Let the sample size $k$ and the memory $m$ satisfy
--   $$1 \le k \le \frac{m}{L_\Gamma + 2}.$$
--   Then for every best-reply distribution $p$ and every initial state $h$, adaptive play $P^0$ converges almost surely to a convention:
--   $$\lim_{t \to \infty} \; \sum_{h' \text{ a convention}} \big((P^0)^t\big)_{hh'} \;=\; 1 .$$
--
--   The theorem shows that in weakly acyclic games, players who best-reply to small random samples of recent history eventually lock in to a strict pure Nash equilibrium, which then persists as a convention. Incomplete sampling ($k$ small relative to $m$) is what lets the process break out of cycles of miscoordination.
--
--   **Formalization Note** "Converges almost surely to a convention" is expressed through the $t$-step transition probabilities: the probability of being in a convention at time $t$ tends to $1$. Since conventions are absorbing, this is equivalent to almost-sure eventual absorption in a convention, from every initial state. The condition $k \le m/(L_\Gamma + 2)$ is written $k(L_\Gamma + 2) \le m$ in the natural numbers. The theorem quantifies over every best-reply distribution, so the sampling law is not fixed.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, Theorem 1, p. 64 (PDF p. 9)

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_WeaklyAcyclic
import Definitions.Def_YoungConventions_AdaptivePlay_LGamma
import Definitions.Def_YoungConventions_AdaptivePlay_IsBestReplyDistribution
import Definitions.Def_YoungConventions_AdaptivePlay_adaptivePlay
import Definitions.Def_YoungConventions_AdaptivePlay_IsConvention

open Filter Topology Classical

namespace YoungConventions.AdaptivePlay

/-- **Theorem 1** (Young 1993, *The Evolution of Conventions*, Econometrica 61:57–84, Theorem 1,
p. 64, PDF p. 9): "Let `Γ` be a weakly acyclic `n`-person game. If `k ≤ m/(L_Γ + 2)`, then adaptive
play converges almost surely to a convention."

Let `Γ` be a finite game (finite set of players, finite nonempty strategy sets, real payoffs) that
is weakly acyclic, let `L_Γ` be the maximum over strategy tuples of the length of a shortest
best-reply path to a strict Nash equilibrium, and let `1 ≤ k` and `k(L_Γ + 2) ≤ m`. For every
best-reply distribution `p` and every initial state `h`, the probability that adaptive play `P⁰`
started at `h` is in a convention at time `t` tends to `1` as `t → ∞`.

**Formalization Note.** (1) "Converges almost surely to a convention" is encoded through the
`t`-step transition probabilities: `∑_{h′ convention} (P⁰)ᵗ_{hh′} → 1`. Because conventions are
absorbing (`absorbing_iff_convention`), the event "in a convention at time `t`" increases in `t`,
and its probability tending to `1` is equivalent to almost-sure eventual absorption in a
convention, for every initial state. (2) `k ≤ m/(L_Γ + 2)` is written `k * (L_Γ + 2) ≤ m` in `ℕ`
(equivalent, no truncating division); together with `1 ≤ k` it gives the paper's `1 ≤ k ≤ m`.
(3) The theorem quantifies over every best-reply distribution: the sampling law is not fixed. -/
theorem theorem_1 {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    (u : ι → (∀ i, S i) → ℝ) (hu : WeaklyAcyclic u)
    (k m : ℕ) [NeZero m] (hk : 1 ≤ k) (hkm : k * (LGamma u + 2) ≤ m)
    (p : ∀ i, History S m → S i → ℝ) (hp : IsBestReplyDistribution u k p)
    (h : History S m) :
    Tendsto (fun t : ℕ => ∑ h' ∈ Finset.univ.filter (fun h' : History S m => IsConvention u h'),
      (adaptivePlay p ^ t) h h') atTop (𝓝 1) := by sorry

end YoungConventions.AdaptivePlay

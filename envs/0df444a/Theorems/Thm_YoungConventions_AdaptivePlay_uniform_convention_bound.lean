-- Prove2me | Theorems.Thm_YoungConventions_AdaptivePlay_uniform_convention_bound
-- name    : YoungConventions.AdaptivePlay.uniform_convention_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:05:38.779388+00:00
-- url     : https://prove2.me/theorems/2e1c846e-c707-4901-a122-5d2afff9dd49
-- title:
--   Proof of Theorem 1, p. 65 — a convention within $M = kL_\Gamma + m$ periods with probability $\ge p > 0$
-- statement:
--   Let $\Gamma$ be a weakly acyclic finite game, let $1 \le k$ with $k \le m/(L_\Gamma + 2)$, and let $p$ be a best-reply distribution with sample size $k$. Put $M = kL_\Gamma + m$. Then there is $q > 0$ such that from every initial state $h$, adaptive play is in a convention after $M$ periods with probability at least $q$:
--   $$\sum_{h' \text{ a convention}} \big((P^0)^{M}\big)_{hh'} \;\ge\; q \qquad \text{for all } h \in H .$$
--
--   This is the uniform lower bound from which the proof of Theorem 1 derives almost-sure convergence. The bound $q$ (the paper's $p = \min_h p_h$) depends on the game, $k$, $m$ and the best-reply distribution, but not on the initial state.
--
--   **Formalization Note** The paper says "within $M$ periods". Since conventions are absorbing, this is the same as "at time $M$". The hypothesis $k \le m/(L_\Gamma + 2)$ is stated as $k(L_\Gamma + 2) \le m$ in the natural numbers.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, proof of Theorem 1, pp. 64–65 (PDF pp. 9–10)

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_WeaklyAcyclic
import Definitions.Def_YoungConventions_AdaptivePlay_LGamma
import Definitions.Def_YoungConventions_AdaptivePlay_IsBestReplyDistribution
import Definitions.Def_YoungConventions_AdaptivePlay_adaptivePlay
import Definitions.Def_YoungConventions_AdaptivePlay_IsConvention

open Classical

namespace YoungConventions.AdaptivePlay

/-- **A convention is reached within `M = kL_Γ + m` periods with probability bounded away from
zero, uniformly in the initial state** (Young 1993, *The Evolution of Conventions*, Econometrica
61:57–84, proof of Theorem 1, pp. 64–65, PDF pp. 9–10): "Since `r ≤ L_Γ`, we have established that,
given an initial state `h`, there is a probability `p_h > 0` of converging to an absorbing state
within `M = kL_Γ + m` periods. Letting `p = min_{h∈H} p_h > 0`, it follows that from any initial
state the process converges with probability at least `p` to an absorbing state within at most `M`
periods."

Let the game be weakly acyclic, `1 ≤ k` and `k(L_Γ + 2) ≤ m`, and let `p` be a best-reply
distribution. Then there is `q > 0` such that for every initial state `h`,
$$ \sum_{h' \text{ a convention}} (P^0)^{kL_\Gamma + m}_{h h'} \;\ge\; q. $$

**Formalization Note.** The paper's "within `M` periods" is stated as "at time `M`"; the two agree
because conventions are absorbing (`absorbing_iff_convention`). The constant `q` (the paper's `p`)
may depend on the game, `k`, `m` and the best-reply distribution, but not on `h`. The hypothesis
`k ≤ m/(L_Γ + 2)` is written `k * (L_Γ + 2) ≤ m` in `ℕ`, which is equivalent and avoids truncating
division. -/
theorem uniform_convention_bound {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    (u : ι → (∀ i, S i) → ℝ) (hu : WeaklyAcyclic u)
    (k m : ℕ) [NeZero m] (hk : 1 ≤ k) (hkm : k * (LGamma u + 2) ≤ m)
    (p : ∀ i, History S m → S i → ℝ) (hp : IsBestReplyDistribution u k p) :
    ∃ q : ℝ, 0 < q ∧ ∀ h : History S m,
      q ≤ ∑ h' ∈ Finset.univ.filter (fun h' : History S m => IsConvention u h'),
        (adaptivePlay p ^ (k * LGamma u + m)) h h' := by sorry

end YoungConventions.AdaptivePlay

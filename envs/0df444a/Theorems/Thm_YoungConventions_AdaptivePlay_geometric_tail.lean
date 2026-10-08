-- Prove2me | Theorems.Thm_YoungConventions_AdaptivePlay_geometric_tail
-- name    : YoungConventions.AdaptivePlay.geometric_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:03:32.452912+00:00
-- url     : https://prove2.me/theorems/0a5f7180-a46e-4495-93e8-a51824b87d7c
-- title:
--   Proof of Theorem 1, p. 64 — the probability of no convention after $rM$ periods is at most $(1-p)^r$
-- statement:
--   Let $\Gamma$ be a finite game, $1 \le k \le m$, and $p$ a best-reply distribution with sample size $k$. Suppose that for some $M \in \mathbb N$ and $q \in \mathbb R$, adaptive play is in a convention after $M$ periods with probability at least $q$ from every initial state:
--   $$\sum_{h' \text{ a convention}} \big((P^0)^{M}\big)_{hh'} \ge q \qquad \text{for all } h \in H .$$
--   Then for every initial state $h$ and every $r \in \mathbb N$,
--   $$\sum_{h' \text{ not a convention}} \big((P^0)^{rM}\big)_{hh'} \;\le\; (1 - q)^r .$$
--
--   With $q > 0$ the right side tends to $0$ as $r \to \infty$. Combined with the uniform bound, this gives Theorem 1.
--
--   **Formalization Note** No sign condition on $q$ or $M$ is needed.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, proof of Theorem 1, p. 64 (PDF p. 9)

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_IsBestReplyDistribution
import Definitions.Def_YoungConventions_AdaptivePlay_adaptivePlay
import Definitions.Def_YoungConventions_AdaptivePlay_IsConvention

open Classical

namespace YoungConventions.AdaptivePlay

/-- **Geometric tail of the time to reach a convention** (Young 1993, *The Evolution of
Conventions*, Econometrica 61:57–84, proof of Theorem 1, p. 64, PDF p. 9): "We shall show that
there exists a positive integer `M`, and a positive probability `p`, such that from any state `h`,
the probability is at least `p` that adaptive play converges within `M` periods to a convention.
`M` and `p` are time-independent and state-independent. Hence the probability of *not* reaching a
convention after at least `rM` periods is at most `(1 − p)^r`, which goes to zero as `r → ∞`."

Let `1 ≤ k ≤ m` and let `p` be a best-reply distribution. If `M ∈ ℕ` and `q ∈ ℝ` are such that from
every state `h` the probability of being in a convention after `M` steps is at least `q`, then for
every state `h` and every `r ∈ ℕ`,
$$ \sum_{h' \text{ not a convention}} (P^0)^{rM}_{h h'} \;\le\; (1 - q)^r. $$

**Formalization Note.** No sign condition on `q` or `M` is needed (for `M = 0` the hypothesis
forces `q ≤ 0` unless every state is a convention). The proof uses that conventions are absorbing,
which holds for every best-reply distribution with `1 ≤ k ≤ m`. -/
theorem geometric_tail {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    (u : ι → (∀ i, S i) → ℝ) (k m : ℕ) [NeZero m] (hk : 1 ≤ k) (hkm : k ≤ m)
    (p : ∀ i, History S m → S i → ℝ) (hp : IsBestReplyDistribution u k p)
    (M : ℕ) (q : ℝ)
    (hq : ∀ h : History S m,
      q ≤ ∑ h' ∈ Finset.univ.filter (fun h' : History S m => IsConvention u h'),
        (adaptivePlay p ^ M) h h')
    (h : History S m) (r : ℕ) :
    ∑ h' ∈ Finset.univ.filter (fun h' : History S m => ¬ IsConvention u h'),
        (adaptivePlay p ^ (r * M)) h h' ≤ (1 - q) ^ r := by sorry

end YoungConventions.AdaptivePlay

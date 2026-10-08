-- Prove2me | Theorems.Thm_YoungConventions_AdaptivePlay_absorbing_iff_convention
-- name    : YoungConventions.AdaptivePlay.absorbing_iff_convention
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:03:34.784109+00:00
-- url     : https://prove2.me/theorems/1b50e245-0319-4265-bfd1-be64c20946eb
-- title:
--   §4, p. 62 — the absorbing states of adaptive play are exactly the conventions
-- statement:
--   Let $\Gamma$ be a game with finitely many players and finite nonempty strategy sets. Let $1 \le k \le m$, let $p$ be any best-reply distribution with sample size $k$, and let $P^0$ be adaptive play with memory $m$. For every state $h \in H$,
--   $$P^0_{hh} = 1 \iff h \text{ is a convention.}$$
--
--   So the only states in which adaptive play can come to rest are $m$-fold repetitions of a strict pure Nash equilibrium. Convergence of adaptive play therefore means convergence to a convention.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §4, p. 62 (PDF p. 7)

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_IsBestReplyDistribution
import Definitions.Def_YoungConventions_AdaptivePlay_adaptivePlay
import Definitions.Def_YoungConventions_AdaptivePlay_IsConvention

namespace YoungConventions.AdaptivePlay

/-- **Absorbing states of adaptive play are exactly the conventions** (Young 1993, *The Evolution
of Conventions*, Econometrica 61:57–84, §4, p. 62, PDF p. 7): "Let us begin by observing that `h`
is an absorbing state of this process if and only if it consists of a strict pure strategy Nash
equilibrium played `m` times in succession."

For every finite game, every `1 ≤ k ≤ m`, every best-reply distribution `p` and every state `h`:
`P⁰_{hh} = 1` if and only if `h` is a convention.

**Formalization Note.** "Absorbing" is `P⁰_{hh} = 1`. The theorem holds for every best-reply
distribution, not only uniform sampling. -/
theorem absorbing_iff_convention {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    (u : ι → (∀ i, S i) → ℝ) (k m : ℕ) [NeZero m] (hk : 1 ≤ k) (hkm : k ≤ m)
    (p : ∀ i, History S m → S i → ℝ) (hp : IsBestReplyDistribution u k p)
    (h : History S m) :
    adaptivePlay p h h = 1 ↔ IsConvention u h := by sorry

end YoungConventions.AdaptivePlay

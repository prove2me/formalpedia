-- Prove2me | Theorems.Thm_YoungConventions_RiskDominance_corollary
-- name    : YoungConventions.RiskDominance.corollary
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T18:05:15.753489+00:00
-- url     : https://prove2.me/theorems/f9fd221a-7ea9-4892-bf7f-cf8247a8cae9
-- title:
--   Corollary — in weakly acyclic games the stable states are the conventions of minimum stochastic potential
-- statement:
--   Let $\Gamma$ be a weakly acyclic finite game, let $k\ge1$ and $m$ satisfy $k\le m/(L_\Gamma+2)$, let $p$ be a best-reply distribution for sample size $k$, and let $(\lambda,q)$ be an admissible experimentation. Then a state $h$ is stochastically stable relative to $P^\varepsilon$ if and only if
--   $$h \text{ is a convention and } \gamma(\{h\})\le\gamma(\{h'\})\ \text{ for every convention } h'.$$
--
--   Under these hypotheses the recurrent communication classes of $P^0$ are exactly the singletons of the conventions (by Theorem 1), so the stochastic potential of a convention is the potential of its singleton class.
--
--   **Formalization Note** $k\le m/(L_\Gamma+2)$ is written $k(L_\Gamma+2)\le m$ in natural numbers.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §6, p. 70, Corollary

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_History
import Definitions.Def_YoungConventions_RiskDominance_IsBestReplyDistribution
import Definitions.Def_YoungConventions_RiskDominance_IsExperimentation
import Definitions.Def_YoungConventions_RiskDominance_IsStochasticallyStable
import Definitions.Def_YoungConventions_RiskDominance_stochasticPotential
import Definitions.Def_YoungConventions_RiskDominance_IsWeaklyAcyclic
import Definitions.Def_YoungConventions_RiskDominance_bestReplyRadius
import Definitions.Def_YoungConventions_RiskDominance_IsConvention

open Filter Topology

namespace YoungConventions.RiskDominance

/-- **Corollary (to Theorems 1 and 2).** Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §6, p. 70 (PDF p. 15): "If `Γ` is weakly acyclic and
`k ≤ m/(L_Γ + 2)`, the stochastically stable states of adaptive play are the convention(s) of minimum
stochastic potential."

For every weakly acyclic finite game, `1 ≤ k` with `k(L_Γ + 2) ≤ m`, best-reply distribution `p` and
admissible `(λ, q)`: a state `h` is stochastically stable iff `h` is a convention and
`γ({h}) ≤ γ({h′})` for every convention `h′`.

**Formalization Note.** `k ≤ m/(L_Γ + 2)` is `k * (L_Γ + 2) ≤ m` in `ℕ`. The stochastic potential is
taken of the singleton class `{h}`: under these hypotheses the recurrent communication classes of
`P⁰` are exactly the singletons of the conventions (Theorem 1, p. 70: "the recurrent classes
correspond one-to-one with the strict pure strategy Nash equilibria"), which is part of the content
of the corollary. -/
theorem corollary {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, Fintype (S i)]
    [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    (u : ι → ((i : ι) → S i) → ℝ) (hwa : IsWeaklyAcyclic u)
    (k m : ℕ) [NeZero m] (hk : 1 ≤ k) (hkm : k * (bestReplyRadius u + 2) ≤ m)
    (p q : (i : ι) → YoungConventions.AdaptivePlay.History S m → S i → ℝ) (lam : ι → ℝ)
    (hp : IsBestReplyDistribution u k p) (hq : IsExperimentation lam q) (h : YoungConventions.AdaptivePlay.History S m) :
    IsStochasticallyStable p q lam h ↔
      IsConvention u h ∧ ∀ h' : YoungConventions.AdaptivePlay.History S m, IsConvention u h' →
        stochasticPotential u k p {h} ≤ stochasticPotential u k p {h'} := by sorry

end YoungConventions.RiskDominance

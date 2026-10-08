-- Prove2me | Theorems.Thm_YoungConventions_RiskDominance_theorem_2
-- name    : YoungConventions.RiskDominance.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T18:04:52.513001+00:00
-- url     : https://prove2.me/theorems/a6f678c8-453a-4d72-b53f-e6d6f108d945
-- title:
--   Theorem 2 — stochastically stable states are the recurrent classes of $P^0$ with minimum stochastic potential
-- statement:
--   Let $\Gamma$ be a finite $n$-person game with nonempty strategy sets, let $1\le k\le m$, let $p$ be a best-reply distribution for sample size $k$, and let $(\lambda,q)$ be an admissible experimentation ($\lambda_i>0$, $q_i(\cdot\mid h)$ of full support).
--   Write $H_1,\dots,H_J$ for the recurrent communication classes of $P^0$ and $\gamma_i$ for the stochastic potential of $H_i$ (computed from the least resistances $r_{ij}$, i.e. from mistake counts). Then:
--   1. a state $h$ is stochastically stable relative to $P^\varepsilon$ if and only if
--   $$h\in H_j\ \text{ for some } j \text{ with }\ \gamma_j\le\gamma_i\ \text{ for all } i;$$
--   2. these states are independent of the experimentation probabilities and distributions: for any other admissible $(\lambda',q')$, a state is stochastically stable for $(\lambda,q)$ if and only if it is for $(\lambda',q')$.
--
--   This is the computational tool of the paper: stochastic stability, a statement about stationary distributions as $\varepsilon\to0$, is decided by a combinatorial minimization over trees.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §6, p. 69, Theorem 2

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_History
import Definitions.Def_YoungConventions_RiskDominance_IsBestReplyDistribution
import Definitions.Def_YoungConventions_RiskDominance_IsExperimentation
import Definitions.Def_YoungConventions_RiskDominance_unperturbed
import Definitions.Def_YoungConventions_RiskDominance_IsStochasticallyStable
import Definitions.Def_YoungConventions_RiskDominance_recurrentClasses
import Definitions.Def_YoungConventions_RiskDominance_stochasticPotential

open Filter Topology

namespace YoungConventions.RiskDominance

/-- **Theorem 2.** Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §6, p. 69 (PDF p. 14): "Let `Γ` be an `n`-person game on a finite strategy
space. The stochastically stable states of adaptive play `P^ε` are the states contained in the
recurrent communication classes of `P⁰` with minimum stochastic potential. These states are
independent of the experimentation probabilities `λᵢ` and the experimentation distributions `qᵢ` so
long as they have full support."

For every finite game, `1 ≤ k ≤ m`, best-reply distribution `p` and admissible `(λ, q)`:
1. a state `h` is stochastically stable for `P^ε` iff `h` lies in a recurrent communication class
   `C` of `P⁰` with `γ(C) ≤ γ(C′)` for every recurrent communication class `C′`;
2. for any other admissible `(λ′, q′)`, the stochastically stable states for `(λ, q)` and for
   `(λ′, q′)` are the same.

**Formalization Note.** Stochastic stability is defined from the stationary distributions of `P^ε`
(`IsStochasticallyStable`), the stochastic potential from the mistake counts
(`stochasticPotential`); the theorem is the bridge between the two. Part 2 is the theorem's second
sentence made explicit ("full support" is part of `IsExperimentation`). -/
theorem theorem_2 {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, Fintype (S i)]
    [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    (u : ι → ((i : ι) → S i) → ℝ) (k m : ℕ) [NeZero m] (hk : 1 ≤ k) (hkm : k ≤ m)
    (p q : (i : ι) → YoungConventions.AdaptivePlay.History S m → S i → ℝ) (lam : ι → ℝ)
    (hp : IsBestReplyDistribution u k p) (hq : IsExperimentation lam q) :
    (∀ h : YoungConventions.AdaptivePlay.History S m, IsStochasticallyStable p q lam h ↔
      ∃ C ∈ recurrentClasses (unperturbed p), h ∈ C ∧
        ∀ C' ∈ recurrentClasses (unperturbed p),
          stochasticPotential u k p C ≤ stochasticPotential u k p C') ∧
    (∀ (q' : (i : ι) → YoungConventions.AdaptivePlay.History S m → S i → ℝ) (lam' : ι → ℝ), IsExperimentation lam' q' →
      ∀ h : YoungConventions.AdaptivePlay.History S m, IsStochasticallyStable p q lam h ↔ IsStochasticallyStable p q' lam' h) := by sorry

end YoungConventions.RiskDominance

-- Prove2me | Theorems.Thm_YoungConventions_Perturbed_lemma_1
-- name    : YoungConventions.Perturbed.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:01:17.803485+00:00
-- url     : https://prove2.me/theorems/f6aa7379-70ba-4afc-8965-6713197e4b1d
-- title:
--   Lemma 1 — $\mu^\varepsilon \to \mu^0$ stationary for $P^0$, and $\mu^0_x > 0$ iff $\gamma(x)$ is minimal
-- statement:
--   Let $(P^\varepsilon)_{\varepsilon \in (0,a]}$ be a regular perturbation of the Markov chain $P^0$ on the finite set $X$, and let $\mu^\varepsilon$ be the stationary distribution of $P^\varepsilon$ for each $\varepsilon \in (0,a]$. Then the limit
--   $$\mu^0 = \lim_{\varepsilon \to 0} \mu^\varepsilon$$
--   exists and is a stationary distribution of $P^0$. Moreover, for every $x \in X$,
--   $$\mu^0_x > 0 \iff \gamma(x) \le \gamma(y) \text{ for all } y \in X,$$
--   where $\gamma$ is the potential (9): the least total resistance of an $x$-tree in the graph $G$.
--
--   Lemma 1 characterizes the stochastically stable states through spanning trees on the whole state space; Lemma 2 reduces this to the much smaller graph of recurrent classes.
--
--   **Formalization Note** "Let $\mu^\varepsilon$ be its stationary distribution" is encoded by quantifying over every family $(\mu^\varepsilon)$ with $\mu^\varepsilon$ stationary for $P^\varepsilon$ for all $\varepsilon \in (0,a]$; by (6) it is unique. The limit is one-sided ($\varepsilon \to 0^+$) and coordinatewise. Potentials are compared in the extended reals; they are finite for a regular perturbation.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, Appendix, Lemma 1, p. 78 (PDF p. 23); proof pp. 79–80

import Mathlib
import Definitions.Def_YoungConventions_Perturbed_FiniteChain
import Definitions.Def_YoungConventions_Perturbed_InTree
import Definitions.Def_YoungConventions_Perturbed_RegularPerturbation
import Definitions.Def_YoungConventions_Perturbed_StochasticPotential

open Filter Topology Finset

namespace YoungConventions.Perturbed

/-- Lemma 1 (Young 1993, Econometrica 61:57–84, Appendix, p. 78, PDF p. 23; proof pp. 79–80).

Let `P^ε` (`ε ∈ (0, a]`) be a regular perturbation of the Markov chain `P⁰` on the finite set
`X`, and let `μ^ε` be its stationary distribution. Then `μ⁰ = lim_{ε→0} μ^ε` exists and is a
stationary distribution of `P⁰`. Moreover `μ⁰_x > 0` iff `γ(x) ≤ γ(y)` for all `y ∈ X`, where
`γ` is the potential (9) (`statePotential`).

**Formalization Note.** "Let `μ^ε` be its stationary distribution" is encoded by quantifying over
every family `μ` with `μ ε` stationary for `P ε` for all `ε ∈ (0, a]`; by (6) this distribution
is unique, so this is the paper's reading. The limit is one-sided (`ε → 0⁺`) and pointwise in
`x`, which on the finite `X` is convergence of the vector `μ^ε`. -/
theorem lemma_1 {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (P0 : Matrix X X ℝ) (hP0 : P0 ∈ Matrix.rowStochastic ℝ X)
    (P : ℝ → Matrix X X ℝ) (a : ℝ) (hP : IsRegularPerturbation P0 P a)
    (μ : ℝ → X → ℝ) (hμ : ∀ ε ∈ Set.Ioc 0 a, IsStationaryDist (P ε) (μ ε)) :
    ∃ μ0 : X → ℝ,
      (∀ x, Tendsto (fun ε : ℝ => μ ε x) (𝓝[>] 0) (𝓝 (μ0 x))) ∧
      IsStationaryDist P0 μ0 ∧
      ∀ x, (0 < μ0 x ↔ ∀ y, statePotential P x ≤ statePotential P y) := by sorry

end YoungConventions.Perturbed

-- Prove2me | Theorems.Thm_YoungConventions_Perturbed_theorem_4
-- name    : YoungConventions.Perturbed.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:02:06.826813+00:00
-- url     : https://prove2.me/theorems/993a0033-a88e-416f-9472-e059c9cbb3fe
-- title:
--   Theorem 4 — stochastically stable states are the recurrent classes of minimum stochastic potential
-- statement:
--   Let $P^0$ be a Markov chain on the finite state space $X$ with recurrent communication classes $X_1, \dots, X_J$. Let $(P^\varepsilon)_{\varepsilon \in (0,a]}$ be a regular perturbation of $P^0$ (conditions (6)–(8)), and let $\mu^\varepsilon$ be the unique stationary distribution of $P^\varepsilon$ for every $\varepsilon \in (0, a]$. Then:
--
--   1. as $\varepsilon \to 0$, $\mu^\varepsilon$ converges to a stationary distribution $\mu^0$ of $P^0$;
--   2. a state $x$ is **stochastically stable**, $\mu^0_x > 0$, if and only if $x$ is contained in a recurrent class $X_j$ that minimizes the stochastic potential:
--   $$\mu^0_x > 0 \iff \exists j:\ x \in X_j \ \text{ and } \ \gamma_j = \min_{1 \le i \le J} \gamma_i.$$
--
--   Here $\gamma_j$ is the least total resistance of a $j$-tree in the complete directed graph on the classes whose edge $(i, i')$ has weight $r_{ii'}$, the least resistance of a path from $X_i$ to $X_{i'}$ in the graph $G$ of transitions that are positive for small $\varepsilon$, weighted by their resistances.
--
--   The theorem is the finite-state analogue of the Freidlin–Wentzell theory of small random perturbations, and it is the general result of which Theorem 2 of the paper (stochastic stability under adaptive play with mistakes) is a special case: the selected classes depend only on the orders of magnitude of the perturbations.
--
--   **Formalization Note** "Its unique stationary distribution" is encoded by quantifying over every family $(\mu^\varepsilon)$ with $\mu^\varepsilon$ stationary for $P^\varepsilon$ for all $\varepsilon \in (0,a]$; by (6) it is unique. The limit is one-sided and coordinatewise. The recurrent classes are those of $P^0$, computed from $P^0$ (not taken as data), and $\gamma_j$ is computed in the extended reals on the graph of classes.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, Appendix, Theorem 4, p. 78 (PDF p. 23)

import Mathlib
import Definitions.Def_YoungConventions_Perturbed_FiniteChain
import Definitions.Def_YoungConventions_Perturbed_InTree
import Definitions.Def_YoungConventions_Perturbed_RegularPerturbation
import Definitions.Def_YoungConventions_Perturbed_StochasticPotential

open Filter Topology Finset

namespace YoungConventions.Perturbed

/-- Theorem 4 (Young 1993, Econometrica 61:57–84, Appendix, p. 78, PDF p. 23).

Let `P⁰` be a Markov chain on the finite state space `X` with recurrent communication classes
`X₁, …, X_J`. Let `P^ε` (`ε ∈ (0, a]`) be a regular perturbation of `P⁰`, and let `μ^ε` be its
unique stationary distribution for every small positive `ε`. Then
(i) as `ε → 0`, `μ^ε` converges to a stationary distribution `μ⁰` of `P⁰`;
(ii) `x` is stochastically stable (`μ⁰_x > 0`) iff `x` is contained in a recurrent class `X_j`
that minimizes the stochastic potential `γ_j`.

**Formalization Note.** "Its unique stationary distribution" is encoded by quantifying over every
family `μ` with `μ ε` stationary for `P ε` for all `ε ∈ (0, a]` (unique by (6)). The limit is
one-sided and pointwise. The recurrent classes are those of `P⁰` (`recurrentClasses P0`, indexed
by `RecClass P0`), and `γ_j` is `classPotential`, computed on the graph of classes with the least
path resistances `r_ij`; it is not defined through the state potentials `γ(x)`. -/
theorem theorem_4 {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (P0 : Matrix X X ℝ) (hP0 : P0 ∈ Matrix.rowStochastic ℝ X)
    (P : ℝ → Matrix X X ℝ) (a : ℝ) (hP : IsRegularPerturbation P0 P a)
    (μ : ℝ → X → ℝ) (hμ : ∀ ε ∈ Set.Ioc 0 a, IsStationaryDist (P ε) (μ ε)) :
    ∃ μ0 : X → ℝ,
      (∀ x, Tendsto (fun ε : ℝ => μ ε x) (𝓝[>] 0) (𝓝 (μ0 x))) ∧
      IsStationaryDist P0 μ0 ∧
      ∀ x, (0 < μ0 x ↔ ∃ j : RecClass P0, x ∈ j.1 ∧
        ∀ j' : RecClass P0, classPotential P0 P j ≤ classPotential P0 P j') := by sorry

end YoungConventions.Perturbed

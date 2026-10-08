-- Prove2me | Theorems.Thm_YoungConventions_Perturbed_lemma_2
-- name    : YoungConventions.Perturbed.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:01:26.630993+00:00
-- url     : https://prove2.me/theorems/ecc0b86c-f532-40c9-90f6-432a245bef12
-- title:
--   Lemma 2 — $\gamma(x) = \gamma_j$ for every state $x$ of the recurrent class $X_j$
-- statement:
--   Let $(P^\varepsilon)_{\varepsilon \in (0,a]}$ be a regular perturbation of the Markov chain $P^0$ on the finite set $X$, with recurrent communication classes $X_1, \dots, X_J$. For every class $X_j$ and every state $x \in X_j$,
--   $$\gamma(x) = \gamma_j,$$
--   where $\gamma(x)$ is the least resistance of an $x$-tree in the state graph $G$ (equation (9)) and $\gamma_j$ is the stochastic potential of $X_j$: the least resistance of a $j$-tree in the graph $\mathcal G$ on the classes, whose edge $(i, i')$ has weight $r_{ii'}$, the least resistance of a path in $G$ from $X_i$ to $X_{i'}$.
--
--   Lemma 2 reduces the arborescence problem on the full state space to one on the (typically much smaller) graph of recurrent classes; with Lemma 1 it yields Theorem 4.
--
--   **Formalization Note** $\gamma_j$ is defined directly on $\mathcal G$, so the statement is not definitional. Both sides are extended reals and are finite for a regular perturbation.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, Appendix, Lemma 2, p. 80 (PDF p. 25); proof pp. 80–83

import Mathlib
import Definitions.Def_YoungConventions_Perturbed_FiniteChain
import Definitions.Def_YoungConventions_Perturbed_InTree
import Definitions.Def_YoungConventions_Perturbed_RegularPerturbation
import Definitions.Def_YoungConventions_Perturbed_StochasticPotential

open Filter Topology Finset

namespace YoungConventions.Perturbed

/-- Lemma 2 (Young 1993, Econometrica 61:57–84, Appendix, p. 80, PDF p. 25; proof pp. 80–83).

Let `P^ε` be a regular perturbation of the Markov chain `P⁰` on the finite set `X`. For every
recurrent communication class `X_j` of `P⁰` and every `x ∈ X_j`, the potential `γ(x)` of (9)
(least resistance of an `x`-tree in the state graph `G`) equals the stochastic potential `γ_j`
of `X_j` (least resistance of a `j`-tree in the graph `𝒢` of recurrent classes, with edge weights
`r_ij`). -/
theorem lemma_2 {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (P0 : Matrix X X ℝ) (hP0 : P0 ∈ Matrix.rowStochastic ℝ X)
    (P : ℝ → Matrix X X ℝ) (a : ℝ) (hP : IsRegularPerturbation P0 P a)
    (j : RecClass P0) (x : X) (hx : x ∈ j.1) :
    statePotential P x = classPotential P0 P j := by sorry

end YoungConventions.Perturbed

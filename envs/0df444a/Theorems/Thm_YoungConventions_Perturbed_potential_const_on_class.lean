-- Prove2me | Theorems.Thm_YoungConventions_Perturbed_potential_const_on_class
-- name    : YoungConventions.Perturbed.potential_const_on_class
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:01:53.788665+00:00
-- url     : https://prove2.me/theorems/b407d04c-40c9-4854-a53b-c8e219ccbd11
-- title:
--   All states of a recurrent class of $P^0$ have the same potential $\gamma$ (p. 80)
-- statement:
--   Let $(P^\varepsilon)_{\varepsilon \in (0,a]}$ be a regular perturbation of the Markov chain $P^0$ on the finite set $X$. If $x$ and $y$ belong to the same recurrent communication class of $P^0$, then
--   $$\gamma(x) = \gamma(y),$$
--   where $\gamma$ is the potential (9).
--
--   Together with Lemma 1 this shows that stochastic stability is a property of whole recurrent classes.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, Appendix, p. 80 (PDF p. 25)

import Mathlib
import Definitions.Def_YoungConventions_Perturbed_FiniteChain
import Definitions.Def_YoungConventions_Perturbed_InTree
import Definitions.Def_YoungConventions_Perturbed_RegularPerturbation
import Definitions.Def_YoungConventions_Perturbed_StochasticPotential

open Filter Topology Finset

namespace YoungConventions.Perturbed

/-- All states of a recurrent class have the same potential (Young 1993, Econometrica 61:57–84,
Appendix, p. 80, PDF p. 25).

Let `P^ε` be a regular perturbation of the Markov chain `P⁰`. If `x` and `y` lie in the same
recurrent communication class `C` of `P⁰`, then `γ(x) = γ(y)`, with `γ` the potential (9). -/
theorem potential_const_on_class {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (P0 : Matrix X X ℝ) (hP0 : P0 ∈ Matrix.rowStochastic ℝ X)
    (P : ℝ → Matrix X X ℝ) (a : ℝ) (hP : IsRegularPerturbation P0 P a)
    (C : Finset X) (hC : C ∈ recurrentClasses P0) (x y : X) (hx : x ∈ C) (hy : y ∈ C) :
    statePotential P x = statePotential P y := by sorry

end YoungConventions.Perturbed

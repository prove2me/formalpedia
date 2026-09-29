-- Prove2me | Theorems.Thm_MarkovChainCLT_measurable_tvDist_kernel
-- name    : MarkovChainCLT.measurable_tvDist_kernel
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T21:46:44.920969+00:00
-- url     : https://prove2.me/theorems/69cc91ce-fcc8-4559-a317-de83709f9198
-- title:
--   On a countably generated space, $x \mapsto \|Q(x,\cdot)-\nu\|$ is measurable
-- statement:
--   Let $Q$ be a Markov kernel from $\mathsf X$ to a **countably generated** space $\mathsf Y$, and let $\nu$ be a probability measure on $\mathsf Y$. Then
--
--   $$x \;\longmapsto\; \bigl\|Q(x,\cdot) - \nu\bigr\|$$
--
--   is measurable.
--
--   **Why this is not automatic.** The total variation distance is defined as a supremum over *all* measurable sets — an uncountable index set — and an uncountable supremum of measurable functions need not be measurable. So nothing about the definition makes $x \mapsto \|Q(x,\cdot)-\nu\|$ measurable, even though each individual $x \mapsto Q(x,A)$ is.
--
--   **Why it is needed.** Every quantitative ergodicity statement about Markov chains produces bounds of the form $\|P^n(x,\cdot)-\pi\| \le \dots$, and turning such a bound into a statement about the chain's *mixing coefficients* requires integrating it over the starting state:
--   $$\alpha(n) \;\le\; \int_{\mathsf X} \bigl\|P^n(x,\cdot)-\pi\bigr\|\,\mathrm{d}\pi(x).$$
--   That integral is meaningless without this measurability. It is what makes the passage possible from Harris ergodicity — convergence $\|P^n(x,\cdot)-\pi\| \to 0$ from *every* starting point, but at no uniform rate — to $\alpha(n) \to 0$: the integrand is dominated by $1$, so dominated convergence applies, whereas a supremum over $x$ would simply fail to converge. This is exactly where the countably-generated hypothesis on the state space earns its place in the classical statement.
--
--   **Proof.** On a countably generated space there is a countable ring $\mathcal C$ of measurable sets containing $\mathsf Y$ and generating the $\sigma$-algebra. Since the total variation is attained on such a ring, for each $x$
--   $$\|Q(x,\cdot)-\nu\| \;=\; \sup_{A \in \mathcal C}\bigl|Q(x,A)-\nu(A)\bigr|$$
--   — the inequality $\le$ is the approximation theorem, and $\ge$ holds because members of $\mathcal C$ are themselves measurable sets. Enumerating $\mathcal C$ as $\{e_0, e_1, \dots\}$ (possible: it is countable and nonempty) turns the right-hand side into $\sup_{n\in\mathbb N}\bigl|Q(x,e_n)-\nu(e_n)\bigr|$.
--
--   Each term is measurable in $x$, being $|\,\cdot\,|$ of the difference of the measurable function $x \mapsto Q(x,e_n)$ and a constant. The family is uniformly bounded by $2$, since both measures are probability measures, so the countable supremum is measurable.
--
--   Both suprema are taken in $\mathbb R$ rather than $[0,\infty]$, so the boundedness is not decoration: it is what makes the suprema real numbers at all, and it is used three times — for the defining set of the total variation, for the ring supremum, and for the countable supremum.
-- source:
--   P. Halmos, Measure Theory, Van Nostrand 1950, Section 13; S. P. Meyn and R. L. Tweedie, Markov Chains and Stochastic Stability, 2nd ed., Cambridge 2009, Ch. 3 and Ch. 16; R. C. Bradley, "Basic Properties of Strong Mixing Conditions", Probability Surveys 2 (2005) 107-144; G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, Theorem 2(i).

import Definitions.Def_TotalVariationDist
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.Kernel.Basic

open MeasureTheory MeasurableSpace ProbabilityTheory Set
open MarkovChainCLT
open scoped ENNReal NNReal symmDiff

theorem MarkovChainCLT.measurable_tvDist_kernel {X Y : Type*} [MeasurableSpace X]
    [mY : MeasurableSpace Y] [MeasurableSpace.CountablyGenerated Y]
    (Q : Kernel X Y) [IsMarkovKernel Q] (ν : Measure Y) [IsProbabilityMeasure ν] :
    Measurable (fun x => tvDist (Q x) ν) := by sorry

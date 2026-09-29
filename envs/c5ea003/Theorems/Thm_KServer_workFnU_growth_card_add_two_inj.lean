-- Prove2me | Theorems.Thm_KServer_workFnU_growth_card_add_two_inj
-- name    : KServer.workFnU_growth_card_add_two_inj
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T07:31:50.152563+00:00
-- url     : https://prove2.me/theorems/c697f8e8-99c9-4066-b8f6-a0602e89d78b
-- title:
--   Total growth of the unordered work function at injective configurations on $k+2$ points
-- statement:
--   Fix an initial configuration $C_0$ and write $\widehat w_t$ for the unordered work function after the first $t$ requests of a sequence $\sigma$ of length $m$. Call a configuration **injective** when its $k$ servers occupy $k$ distinct points. Here $M$ is a metric space with exactly $k+2$ points, two more than the number of servers.
--
--   **Statement.** There is a constant $c$, depending on the metric space and on $C_0$ but not on the request sequence, such that for every $\sigma$ there are numbers $u_1,\dots,u_m$ with
--   $$\widehat w_t(X)\;\le\;\widehat w_{t-1}(X)+u_t\qquad\text{for every \emph{injective} configuration }X\text{ and every }t\le m,$$
--   $$\sum_{t=1}^{m}u_t\;\le\;(k+1)\cdot\mathrm{OPT}(C_0,\sigma)+c .$$
--
--   **Role.** This is the work-function content of Koutsoupias and Papadimitriou's solution of the *2-evader problem*: the $k$-server conjecture holds on every metric space of $k+2$ points. An injective configuration now leaves two points uncovered, so its state is an unordered pair of evaders and there are $\binom{k+2}{2}$ of them. That is why the counting argument which settles the $(k+1)$-point case --- bound a maximum over the $k+1$ holes by their sum, then telescope --- does not carry over: it would give the factor $\binom{k+2}{2}$ instead of $k+1$. A genuine potential is needed, one that tracks how a request moves the pair of evaders.
--
--   By `KServer.extended_cost_lemma_injective`, a bound of this form with factor $\lambda$ makes the Work Function Algorithm $(\lambda-1)$-competitive; here $\lambda=(k+1)$ gives the ratio $k$. The statement mentions no online algorithm at all.
--
--   **Why the bound is asked only at injective configurations.** The classical theory takes a configuration to be a set of $k$ points, so the case of two servers sharing a point never arises; here a configuration is a labelled map and may be degenerate. The difference is real: at a single step the increment $\widehat w_t(X)-\widehat w_{t-1}(X)$ at a degenerate $X$ can exceed its value at every injective one --- this already happens on the uniform three-point space with $k=2$. So a bound proved by the classical argument is a bound at injective configurations, and `KServer.extended_cost_lemma_injective` is arranged to need no more: by `KServer.moveCost_injective_between` the Work Function Algorithm, started at an injective configuration, stays injective for ever. `Fintype.card M = k + 2` makes $M$ itself the $(k+2)$-point space, and injective configurations exist because $k\le k+2$.
--
--   **Formalization Note** The prefix $r_1,\dots,r_t$ appears as `σ.take t`, and the bounding sequence `u` is given explicitly rather than as a maximum over configurations, since on an unbounded metric space that maximum needs a separate finiteness argument. The proved case $\lambda=k+1$ on $k+1$ points, `KServer.workFnU_growth_card_succ_inj`, is the model for the shape of such an argument.
-- source:
--   E. Koutsoupias, The k-server problem (survey), Computer Science Review 3 (2009) 105-118, https://doi.org/10.1016/j.cosrev.2009.04.002, Section 2 (the $k+2$-point case) and Section 3.4 (the Extended Cost Lemma); originally E. Koutsoupias, C. Papadimitriou, The 2-evader problem, Information Processing Letters 57 (1996) 249-252, https://doi.org/10.1016/0020-0190(96)00010-5

import Mathlib
import Definitions.Def_KServer_workfunctionU

namespace KServer

theorem workFnU_growth_card_add_two_inj (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M] [Fintype M] (hM : Fintype.card M = k + 2)
    (C₀ : Config k M) :
    ∃ c : ℝ, ∀ σ : List M, ∃ u : ℕ → ℝ,
      (∀ t : ℕ, t < σ.length → ∀ X : Config k M, Function.Injective X →
          workFnU C₀ (σ.take (t + 1)) X ≤ workFnU C₀ (σ.take t) X + u t) ∧
      (∑ t ∈ Finset.range σ.length, u t) ≤ ((k : ℝ) + 1) * offlineCost C₀ σ + c := by sorry

end KServer

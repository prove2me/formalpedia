-- Prove2me | Theorems.Thm_KServer_workFnU_growth_two_server_inj
-- name    : KServer.workFnU_growth_two_server_inj
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T07:32:29.208274+00:00
-- url     : https://prove2.me/theorems/3d105a28-5bbb-4a80-9d93-767d70faeb0c
-- title:
--   Total growth of the unordered work function at injective configurations is at most three times the optimum, for two servers
-- statement:
--   Fix an initial configuration $C_0$ and write $\widehat w_t$ for the unordered work function after the first $t$ requests of a sequence $\sigma$ of length $m$. Call a configuration **injective** when its $k$ servers occupy $k$ distinct points. Here $k=2$: two servers on an arbitrary metric space $M$.
--
--   **Statement.** There is a constant $c$, depending on the metric space and on $C_0$ but not on the request sequence, such that for every $\sigma$ there are numbers $u_1,\dots,u_m$ with
--   $$\widehat w_t(X)\;\le\;\widehat w_{t-1}(X)+u_t\qquad\text{for every \emph{injective} configuration }X\text{ and every }t\le m,$$
--   $$\sum_{t=1}^{m}u_t\;\le\;3\cdot\mathrm{OPT}(C_0,\sigma)+c .$$
--
--   **Role.** This is the work-function content of the Manasse--McGeoch--Sleator theorem that the $2$-server conjecture holds on every metric space. Koutsoupias and Papadimitriou's proof establishes the bound through a potential expression
--   $$\Phi_t(A,b_0,b_1,b_2)\;=\;\widehat w_t(A)-d(b_0^{\,2},A)+\widehat w_t(\{b_0,b_1\})+\widehat w_t(\{b_0,b_2\})-d(b_1,b_2),$$
--   where $d(b^{\,2},A)$ denotes the sum of the distances from $b$ to the two points of $A$. The technical heart is that $\Phi_t$ is minimised when $b_0$ is the last request $r_t$; granted that, the number of work-function values occurring in $\Phi_t$ --- namely three --- is the factor $\lambda$, and the sum telescopes.
--
--   By `KServer.extended_cost_lemma_injective`, a bound of this form with factor $\lambda$ makes the Work Function Algorithm $(\lambda-1)$-competitive; here $\lambda=3$ gives the ratio $2$. The statement mentions no online algorithm at all.
--
--   **Why the bound is asked only at injective configurations.** The classical theory takes a configuration to be a set of $k$ points, so the case of two servers sharing a point never arises; here a configuration is a labelled map and may be degenerate. The difference is real: at a single step the increment $\widehat w_t(X)-\widehat w_{t-1}(X)$ at a degenerate $X$ can exceed its value at every injective one --- this already happens on the uniform three-point space with $k=2$. So a bound proved by the classical argument is a bound at injective configurations, and `KServer.extended_cost_lemma_injective` is arranged to need no more: by `KServer.moveCost_injective_between` the Work Function Algorithm, started at an injective configuration, stays injective for ever.
--
--   **Formalization Note** The prefix $r_1,\dots,r_t$ appears as `σ.take t`, and the bounding sequence `u` is given explicitly rather than as a maximum over configurations, since on an unbounded metric space that maximum needs a separate finiteness argument. The proved case $\lambda=k+1$ on $k+1$ points, `KServer.workFnU_growth_card_succ_inj`, is the model for the shape of such an argument.
-- source:
--   E. Koutsoupias, The k-server problem (survey), Computer Science Review 3 (2009) 105-118, https://doi.org/10.1016/j.cosrev.2009.04.002, Section 3.4, Theorem 2 and the potential expression displayed before it; originally M. Manasse, L. McGeoch, D. Sleator, Competitive algorithms for server problems, J. Algorithms 11 (1990) 208-230, https://doi.org/10.1016/0196-6774(90)90003-W (the 2-server case) and E. Koutsoupias, C. Papadimitriou, On the k-server conjecture, J. ACM 42(5) (1995) 971-983, https://doi.org/10.1145/210118.210128

import Mathlib
import Definitions.Def_KServer_workfunctionU

namespace KServer

theorem workFnU_growth_two_server_inj (M : Type) [MetricSpace M] (C₀ : Config 2 M) :
    ∃ c : ℝ, ∀ σ : List M, ∃ u : ℕ → ℝ,
      (∀ t : ℕ, t < σ.length → ∀ X : Config 2 M, Function.Injective X →
          workFnU C₀ (σ.take (t + 1)) X ≤ workFnU C₀ (σ.take t) X + u t) ∧
      (∑ t ∈ Finset.range σ.length, u t) ≤ 3 * offlineCost C₀ σ + c := by sorry

end KServer

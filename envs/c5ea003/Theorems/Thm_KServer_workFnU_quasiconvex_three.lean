-- Prove2me | Theorems.Thm_KServer_workFnU_quasiconvex_three
-- name    : KServer.workFnU_quasiconvex_three
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T15:29:44.33579+00:00
-- url     : https://prove2.me/theorems/8eef01c6-1a37-44a6-bc91-46f9e3215b33
-- title:
--   Quasiconvexity of work functions, pairwise form for three servers
-- statement:
--   Quasiconvexity is the structural property of work functions on which every known proof of $k$-competitiveness of the Work Function Algorithm rests. For three servers it takes a particularly usable *pairwise* form, and it is in this form that Bein, Chrobak and Larmore use it throughout their analysis of the $3$-server problem in the plane, stating it as their equation (3) with the remark that "instead of the general quasiconvexity property, we will only use this last inequality in the calculations".
--
--   ## The statement
--
--   Fix a metric space $M$, an initial configuration $C_0$, a request sequence $\sigma$, and write, following the paper's abuse of notation,
--   $$\omega(x,y) := \widehat w_\sigma(\{r,x,y\})$$
--   for the unordered work function at the three-point configuration consisting of a fixed point $r$ — in the application, the last request — together with $x$ and $y$. Then for all points $x,y,u,v$,
--
--   $$\omega(x,y) + \omega(u,v)\ \ge\ \min\bigl\{\ \omega(x,u) + \omega(y,v),\ \ \omega(x,v) + \omega(y,u)\ \bigr\}.$$
--
--   In words: given two configurations sharing the point $r$, the four remaining points can be **rewired** into two new configurations, again both containing $r$, without increasing the total work-function value — and one of the two possible rewirings always achieves this.
--
--   ## Role
--
--   This is the exchange inequality that drives every case analysis in the three-server theory. It is what allows a step of the form "without loss of generality $\omega(x,y)+\omega(u,v) \ge \omega(x,u)+\omega(y,v)$" that appears repeatedly in the verification of the potential's update property and in the metric-specific arguments. Because both hybrids retain the point $r$, it composes with the recurrence for the work function at configurations covering the last request.
--
--   ## Relation to general quasiconvexity
--
--   `KServer.workFnU_quasiconvex` gives, for any two configurations $X$ and $Y$, a single permutation $\pi$ aligning them such that *every* choice of a subset of coordinates yields a complementary pair of hybrids whose work-function values sum to at most $\widehat w(X) + \widehat w(Y)$. Specialising to $k = 3$ with $X = (r,x,y)$ and $Y = (r,u,v)$ does not immediately give the displayed inequality: the aligning permutation is not under the user's control, and for a general $\pi$ the naive hybrid need not contain $r$ at all, nor be one of the two intended rewirings. The content of this statement is that, whatever $\pi$ is, some choice of the coordinate subset does produce one of the two rewirings — so the minimum, rather than either individual term, is what can be bounded.
--
--   **Formalization Note** Configurations are labelled maps `Fin 3 → M`, written with Mathlib's `![·,·,·]` notation, and `workFnU` is invariant under relabelling, so the statement is really about the three-element multisets $\{r,x,y\}$ etc.; no injectivity is assumed and the points need not be distinct.
-- source:
--   W. Bein, M. Chrobak, L. Larmore, The 3-Server Problem in the Plane, Theoretical Computer Science 289(1) (2002) 335-354, Section 2, equation (3); the general property is E. Koutsoupias, C. Papadimitriou, On the k-server conjecture, J. ACM 42(5) (1995), Section 3.

import Mathlib
import Definitions.Def_KServer_workfunctionU

namespace KServer

theorem workFnU_quasiconvex_three (M : Type) [MetricSpace M] (C₀ : Config 3 M) (σ : List M)
    (r x y u v : M) :
    min (workFnU C₀ σ ![r, x, u] + workFnU C₀ σ ![r, y, v])
        (workFnU C₀ σ ![r, x, v] + workFnU C₀ σ ![r, y, u])
      ≤ workFnU C₀ σ ![r, x, y] + workFnU C₀ σ ![r, u, v] := by sorry

end KServer

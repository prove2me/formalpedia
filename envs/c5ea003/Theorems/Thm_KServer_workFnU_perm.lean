-- Prove2me | Theorems.Thm_KServer_workFnU_perm
-- name    : KServer.workFnU_perm
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T06:56:44.287391+00:00
-- url     : https://prove2.me/theorems/265dde57-38ae-47c7-a184-f70e93689b1c
-- title:
--   The unordered work function depends only on the multiset of occupied points
-- statement:
--   Fix a metric space $M$, $k$ servers, an initial configuration $C_0$ and a request sequence $\sigma$.
--
--   **Statement.** For every configuration $X$ and every permutation $\tau$ of the server indices,
--   $$\widehat w(C_0;\sigma;X\circ\tau)\;=\;\widehat w(C_0;\sigma;X).$$
--
--   **Role.** This is what makes `workFnU` the *classical* work function: it says the value depends only on the multiset of points that $X$ occupies, not on which server occupies which. In the classical treatment a configuration simply is a set of $k$ points, so the statement is invisible; in a model whose configurations are labelled maps it is the bridge that lets unordered reasoning — holes, evaders, minimum-cost matchings, quasiconvexity — be carried out about a labelled object.
--
--   It is also what the step recurrence for `workFnU` rests on, and hence what every argument about the growth of the work function will use. The labelled work function `workFn` has no such invariance, which is exactly why the classical bounds on the total growth hold for $\widehat w$ and fail for $w$.
--
--   **Formalization Note** `workFnU` is defined as $\min_\pi w(C_0;\sigma;X\circ\pi)$, so this is the statement that the minimum is unchanged when the family is reindexed by $\tau$; each inequality follows by exhibiting the reindexed minimiser, $\tau^{-1}\pi$ in one direction and $\tau\pi$ in the other.
-- source:
--   E. Koutsoupias, The k-server problem (survey), Computer Science Review 3 (2009) 105-118, https://doi.org/10.1016/j.cosrev.2009.04.002, Section 1 (configurations are k-point sets, with the minimum-weight matching distance); originally E. Koutsoupias, C. Papadimitriou, On the k-server conjecture, J. ACM 42(5) (1995) 971-983, https://doi.org/10.1145/210118.210128.

import Mathlib
import Definitions.Def_KServer_workfunctionU

namespace KServer

theorem workFnU_perm (k : ℕ) (M : Type) [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) (τ : Equiv.Perm (Fin k)) :
    workFnU C₀ σ (X ∘ τ) = workFnU C₀ σ X := by sorry

end KServer

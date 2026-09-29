-- Prove2me | Theorems.Thm_KServer_shadow_finite
-- name    : KServer.shadow_finite
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T15:40:58.256767+00:00
-- url     : https://prove2.me/theorems/f146a007-c358-41d7-a7f0-e53c183c74dd
-- title:
--   The shadow of a work function is finite
-- statement:
--   The **shadow** of a work function,
--   $$\hat w(x) \;=\; \sup_A\Bigl(\sum_{a \in A} d(x,a) - w(A)\Bigr),$$
--   is a supremum over *all* configurations of the metric space, and the metric space is not assumed bounded, finite, or compact. This says the supremum is finite, with an explicit bound:
--   $$\hat w(x) \;\le\; \sum_i d\bigl(x, C_0(i)\bigr),$$
--   the total distance from $x$ to the initial configuration.
--
--   ## Why it matters
--
--   Every potential in the three-server analysis of Bein–Chrobak–Larmore is assembled from shadows, and the offset and update properties are inequalities between such suprema. In a formalization where `sSup` of a set unbounded above is defined to be $0$, an unbounded shadow would silently make each of those inequalities a statement about junk values rather than about the intended quantity. This bound rules that out, and it does so on an arbitrary metric space — in particular on the Manhattan plane, which is unbounded and where the supremum need not be attained.
--
--   ## The proof
--
--   The single ingredient is that the work function grows at unit rate away from the initial configuration: for **any** base point $v$,
--   $$w(A) \;\ge\; \sum_i d(v, A_i) \;-\; \sum_i d\bigl(v, C_0(i)\bigr),$$
--   which holds because along any schedule serving the requests and ending at $A$, each server's own walk from $C_0(i)$ to $A_i$ costs at least $d(C_0(i), A_i)$, and the triangle inequality through $v$ converts that into the displayed form.
--
--   Applying this with the base point $v$ taken to be $x$ *itself* makes the two sums over $A$ cancel:
--   $$\sum_i d(x, A_i) - w(A) \;\le\; \sum_i d\bigl(x, C_0(i)\bigr),$$
--   a bound independent of $A$. The set is nonempty — take $A = C_0$ — so `csSup_le` applies.
--
--   Choosing the base point to be the very point at which the shadow is evaluated is what makes the bound uniform in $A$; any other base point would leave a term growing with $A$.
-- source:
--   W. Bein, M. Chrobak, L. Larmore, The 3-Server Problem in the Plane, Theoretical Computer Science 289(1) (2002) 335-354, Section 2, equation (1) (definition of the shadow); the unit-rate growth bound used is the standard lower bound on the work function, cf. E. Koutsoupias, C. Papadimitriou, On the k-server conjecture, J. ACM 42(5) (1995), Section 2.

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_lazy_potential

namespace KServer

theorem shadow_finite (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (x : M) :
    shadow C₀ σ x ≤ ∑ i, dist x (C₀ i) := by sorry

end KServer

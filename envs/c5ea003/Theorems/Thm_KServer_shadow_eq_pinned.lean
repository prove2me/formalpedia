-- Prove2me | Theorems.Thm_KServer_shadow_eq_pinned
-- name    : KServer.shadow_eq_pinned
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T16:05:10.475656+00:00
-- url     : https://prove2.me/theorems/401aef76-7056-4818-8045-d97bef2e0ce0
-- title:
--   A maximizer of the shadow contains the last request
-- statement:
--   The **shadow** of a work function, $\hat w(x) = \sup_A\bigl(\sum_{a \in A} d(x,a) - w(A)\bigr)$, ranges over *all* configurations. When $w$ has a last request $r$ — that is, $w$ is saturated at $r$ — the supremum may be restricted to the configurations that **contain** $r$, without changing its value. Writing
--   $$\tilde w(y, x) \;=\; \sup_{a,a'}\bigl(d(x,a) + d(x,a') - w(y,a,a')\bigr)$$
--   for the shadow taken over configurations whose first server sits at $y$, the restriction reads
--
--   $$\hat w(x) \;=\; d(x,r) \;+\; \tilde w(r, x).$$
--
--   Bein, Chrobak and Larmore record this as the relation $\hat e(z) = \tilde w(r,z) + rz$, immediately after observing that "without loss of generality, an $(w,x)$-maximizer contains the last request".
--
--   ## Why it is needed
--
--   The lazy potential is $\Psi_{w,r} = \hat w(r) + \dot w(r)$, a sum of two suprema of different shapes, the second of which nests a copy of $\tilde w$. The analysis of the update property proceeds by choosing witnesses $p, a, a', b, b', d, d'$ realising $\Psi$ as a **single** expression and then splitting each work-function value in it according to which server travels to the new request. That is only possible once $\hat w$ has been rewritten over three-point configurations pinned at $r$ — which is exactly this identity. Without it the outer supremum ranges over configurations of unconstrained shape and the case analysis cannot even be set up.
--
--   ## The proof
--
--   The inequality $\ge$ is the easy half: instantiate the shadow at $A = (r, a, a')$, note $\sum_i d(x, A_i) = d(x,r) + d(x,a) + d(x,a')$, and take the supremum over $a, a'$.
--
--   For $\le$, take any configuration $A$ and apply the update formula: since $r$ is the last request, $w(A)$ equals one of the three values obtained by sending a single server of $A$ to $r$, say $w(A) = w(A[i \mapsto r]) + d(r, A_i)$. Then
--
--   $$\sum_j d(x, A_j) - w(A) \;=\; \sum_j d(x,A_j) - d(r,A_i) - w\bigl(A[i \mapsto r]\bigr)
--   \;\le\; d(x,r) + \sum_{j \ne i} d(x, A_j) - w\bigl(A[i \mapsto r]\bigr),$$
--
--   using $d(x, A_i) - d(r, A_i) \le d(x,r)$ — one triangle inequality, applied to the very server that moved. The remaining expression is an instance of $\tilde w(r,x)$ once $A[i \mapsto r]$ is relabelled to put $r$ first, which is legitimate because the unordered work function is invariant under relabelling. The three cases $i = 0, 1, 2$ differ only in that relabelling: the identity, a transposition, and a $3$-cycle.
--
--   **Formalization note.** Both suprema are bounded above by the unit-rate growth of the work function taken with base point $x$ and $r$ respectively, so neither is the junk value assigned to an unbounded set; the hypothesis that $r$ is the last request is expressed by writing the request sequence as `σ ++ [r]`.
-- source:
--   W. Bein, M. Chrobak, L. Larmore, The 3-Server Problem in the Plane, Theoretical Computer Science 289(1) (2002) 335-354, Section 2, the paragraph following equation (1) ('We conclude that, without loss of generality, an (w,x)-maximizer contains the last request') and the relation e-hat(z) = w-tilde(r,z) + rz stated in Section 3.

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_lazy_potential

namespace KServer

theorem shadow_eq_pinned (M : Type) [MetricSpace M] (C₀ : Config 3 M) (σ : List M)
    (r x : M) :
    shadow C₀ (σ ++ [r]) x = dist x r + shadow₂ C₀ (σ ++ [r]) r x := by sorry

end KServer

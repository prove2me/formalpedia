-- Prove2me | Theorems.Thm_AATA_second_isomorphism_11_2_3
-- name    : AATA.second_isomorphism_11_2_3
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-06T01:05:08.786643+00:00
-- url     : https://prove2.me/theorems/1b2481b1-2747-4005-87e5-64026e763420
-- title:
--   Theorem 11.2.3 — Second Isomorphism Theorem
-- statement:
--   Let $G$ be a group, let $K\le G$ be a subgroup, and let $N$ be a normal subgroup of $G$. The product set $KN=\{kn:k\in K,n\in N\}$ is a subgroup of $G$, the intersection $K\cap N$ is normal in $K$, and
--
--   $$K/(K\cap N)\cong KN/N.$$
--
--   This identifies the part of the quotient $G/N$ reached by $K$. The subgroup $K$ is not required to be normal, and it is not assumed to map onto all of $G/N$.
--
--   **Formalization Note.** The subgroup join is explicitly equated with the product set $KN$. Subgroup restrictions represent $K\cap N$ inside $K$ and the contained copy of $N$ inside $KN$.
-- source:
--   Thomas W. Judson, Abstract Algebra: Theory and Applications, author-hosted HTML edition dated August 4, 2026, Theorem 11.2.3, https://judsonbooks.org/aata-files/aata-html/homomorph-section-group-isomorphism-theorems.html

import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 200000
universe u v

namespace AATA
theorem second_isomorphism_11_2_3 {G : Type u} [Group G] (K N : Subgroup G) [N.Normal] :
    ((K ⊔ N : Subgroup G) : Set G) =
      {g : G | ∃ k ∈ K, ∃ n ∈ N, k*n = g} ∧
    (N.subgroupOf K).Normal ∧
    Nonempty (K ⧸ N.subgroupOf K ≃*
      (K ⊔ N : Subgroup G) ⧸ N.subgroupOf (K ⊔ N)) := by sorry
end AATA

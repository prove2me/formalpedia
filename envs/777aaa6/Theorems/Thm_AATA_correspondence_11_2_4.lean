-- Prove2me | Theorems.Thm_AATA_correspondence_11_2_4
-- name    : AATA.correspondence_11_2_4
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-06T01:05:21.512651+00:00
-- url     : https://prove2.me/theorems/8684af4e-46ad-44de-929e-2e7646efff8f
-- title:
--   Theorem 11.2.4 — Correspondence Theorem
-- statement:
--   Let $G$ be a group and let $N$ be a normal subgroup. Write $q:G\to G/N$ for the canonical quotient homomorphism. The map
--
--   $$K\longmapsto q(K)=K/N$$
--
--   is a bijection from the subgroups $K\le G$ containing $N$ to all subgroups of $G/N$. Moreover, for each such $K$,
--
--   $$K\trianglelefteq G\quad\Longleftrightarrow\quad K/N\trianglelefteq G/N.$$
--
--   Thus the subgroup structure of a quotient is precisely the subgroup structure above its kernel, with normality preserved in both directions.
--
--   **Formalization Note.** The assertion concerns this particular quotient-image map, not an arbitrary bijection. Both groups and subgroups may be infinite; no finiteness, commutativity, or nontriviality assumption is added.
-- source:
--   Thomas W. Judson, Abstract Algebra: Theory and Applications, author-hosted HTML edition dated August 4, 2026, Theorem 11.2.4, https://judsonbooks.org/aata-files/aata-html/homomorph-section-group-isomorphism-theorems.html

import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 200000
universe u v

namespace AATA
theorem correspondence_11_2_4 {G : Type u} [Group G] (N : Subgroup G) [N.Normal] :
    Function.Bijective
      (fun K : {K : Subgroup G // N ≤ K} => K.1.map (QuotientGroup.mk' N)) ∧
    ∀ K : Subgroup G, N ≤ K →
      (K.Normal ↔ (K.map (QuotientGroup.mk' N)).Normal) := by sorry
end AATA

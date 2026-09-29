-- Prove2me | Theorems.Thm_AATA_first_isomorphism_11_2_1
-- name    : AATA.first_isomorphism_11_2_1
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-06T01:04:57.153571+00:00
-- url     : https://prove2.me/theorems/cea7d84b-fbb5-4f8f-8590-006e3bafa187
-- title:
--   Theorem 11.2.1 — First Isomorphism Theorem
-- statement:
--   Let $G,H$ be groups, let $f:G\to H$ be a group homomorphism, and put $K=\ker(f)$. Then $K$ is normal in $G$. For the canonical quotient homomorphism $q:G\to G/K$, there exists a unique group isomorphism
--
--   $$e:G/K\longrightarrow f(G),\qquad e(q(g))=f(g)\quad(g\in G).$$
--
--   The isomorphism identifies the image of a homomorphism with the quotient by exactly the elements sent to the identity. Uniqueness refers to isomorphisms satisfying the displayed commuting equation.
--
--   **Formalization Note.** The codomain is the range subgroup $f(G)$, not all of $H$. Kernel normality is included explicitly. The groups may be infinite or trivial.
-- source:
--   Thomas W. Judson, Abstract Algebra: Theory and Applications, author-hosted HTML edition dated August 4, 2026, Theorem 11.2.1, https://judsonbooks.org/aata-files/aata-html/homomorph-section-group-isomorphism-theorems.html

import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 200000
universe u v

namespace AATA
theorem first_isomorphism_11_2_1 {G : Type u} {H : Type v} [Group G] [Group H] (f : G →* H) :
    f.ker.Normal ∧ ∃! e : G ⧸ f.ker ≃* f.range,
      ∀ g : G, e (QuotientGroup.mk' f.ker g) = f.rangeRestrict g := by sorry
end AATA

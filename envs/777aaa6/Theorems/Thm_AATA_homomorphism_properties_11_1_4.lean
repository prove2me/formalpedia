-- Prove2me | Theorems.Thm_AATA_homomorphism_properties_11_1_4
-- name    : AATA.homomorphism_properties_11_1_4
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-06T01:04:42.05289+00:00
-- url     : https://prove2.me/theorems/6e8ead1f-53f1-4ae7-9766-4d898d19213a
-- title:
--   Proposition 11.1.4 — Basic properties of group homomorphisms
-- statement:
--   Let $G,H$ be groups and let $f:G\to H$ be a group homomorphism. Then
--
--   $$f(1)=1,\qquad f(g^{-1})=f(g)^{-1}\quad(g\in G).$$
--
--   For every subgroup $K\le G$, the image $f(K)$ is a subgroup of $H$. For every subgroup $L\le H$, the inverse image $f^{-1}(L)$ is a subgroup of $G$; if $L$ is normal in $H$, then $f^{-1}(L)$ is normal in $G$.
--
--   These are the four clauses of Judson’s Proposition 11.1.4, kept together as one statement. They provide the subgroup constructions needed to compare groups through a homomorphism.
--
--   **Formalization Note.** Images and inverse images are represented by bundled subgroups, with their carrier sets explicitly equated to the corresponding set-theoretic images and inverse images. No surjectivity assumption is made.
-- source:
--   Thomas W. Judson, Abstract Algebra: Theory and Applications, author-hosted HTML edition dated August 4, 2026, Proposition 11.1.4, https://judsonbooks.org/aata-files/aata-html/homomorph-section-group-homomorphisms.html

import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 200000
universe u v

namespace AATA
theorem homomorphism_properties_11_1_4 {G : Type u} {H : Type v} [Group G] [Group H] (f : G →* H) :
    f 1 = 1 ∧
    (∀ g : G, f g⁻¹ = (f g)⁻¹) ∧
    (∀ K : Subgroup G, ∃ L : Subgroup H, (L : Set H) = f '' (K : Set G)) ∧
    (∀ L : Subgroup H, ∃ K : Subgroup G,
      (K : Set G) = f ⁻¹' (L : Set H) ∧ (L.Normal → K.Normal)) := by sorry
end AATA

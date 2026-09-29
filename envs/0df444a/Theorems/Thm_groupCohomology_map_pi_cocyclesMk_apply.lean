-- Prove2me | Theorems.Thm_groupCohomology_map_pi_cocyclesMk_apply
-- name    : groupCohomology.map_pi_cocyclesMk_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/67ec52dc-c301-53b1-bd66-fc907b40c7a6
-- title:
--   Functoriality of Hⁿ on explicit cocycle representatives
-- statement:
--   Let $k$ be a commutative ring, let $G$ and $H$ be groups, let $A$ be a $k$-linear representation of $H$ and $B$ a $k$-linear representation of $G$ (all in `Type`), let $f : G \to H$ be a group homomorphism and let $\varphi : \mathrm{Res}_f A \to B$ be a morphism of $k$-linear $G$-representations from the restriction of $A$ along $f$ to $B$. Let $n$ be a natural number and let $x : (\mathrm{Fin}\,n \to H) \to A$ be an inhomogeneous $n$-cochain of $H$ with values in $A$, assumed to satisfy $d^n_A(x) = 0$, where $d^n_A$ is the degree-$n$ differential of the inhomogeneous cochain complex of $A$; and assume moreover that the pulled-back cochain $g \mapsto \varphi(x(f \circ g))$ on $(\mathrm{Fin}\,n \to G)$ with values in $B$ satisfies $d^n_B\bigl(g \mapsto \varphi(x(f \circ g))\bigr) = 0$. The conclusion is that the $k$-linear map $H^n(H, A) \to H^n(G, B)$ induced by the pair $(f, \varphi)$ carries the cohomology class of the $n$-cocycle determined by $x$ and its cocycle identity, taken under the projection `groupCohomology.π` from $n$-cocycles to $H^n(H,A)$, to the class of the $n$-cocycle determined by $g \mapsto \varphi(x(f \circ g))$ and its cocycle identity. The cocycle condition for the pulled-back cochain is thus a hypothesis rather than a consequence derived inside the statement.
--
--   This is the usual functoriality of group cohomology in the pair (group, module), made explicit on representatives: the induced map sends the class of an inhomogeneous cocycle $x$ to the class of $g \mapsto \varphi(x(f \circ g))$. It is used when reading explicit idèle-valued cocycles in local coordinates, namely after restriction along an inclusion of a decomposition group followed by a coefficient morphism, and specialises further in [`groupCohomology.map_id_pi_cocyclesMk_apply`](thm.html#groupCohomology.map_id_pi_cocyclesMk_apply).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_map_pi_cocyclesMk_apply.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.map_pi_cocyclesMk_apply
    {k G H : Type} [CommRing k] [Group G] [Group H] {A : Rep.{0} k H} {B : Rep.{0} k G}
    (f : G →* H) (φ : Rep.res f A ⟶ B) (n : ℕ) (x : (Fin n → H) → A)
    (hx : (inhomogeneousCochains.d A n).hom x = 0)
    (hx' : (inhomogeneousCochains.d B n).hom (fun g => φ.hom (x (f ∘ g))) = 0) :
    (groupCohomology.map f φ n).hom (groupCohomology.π A n (groupCohomology.cocyclesMk x hx)) =
      groupCohomology.π B n (groupCohomology.cocyclesMk (fun g => φ.hom (x (f ∘ g))) hx') := by sorry

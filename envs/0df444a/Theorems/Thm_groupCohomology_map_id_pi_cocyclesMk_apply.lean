-- Prove2me | Theorems.Thm_groupCohomology_map_id_pi_cocyclesMk_apply
-- name    : groupCohomology.map_id_pi_cocyclesMk_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/ddbd7adb-6beb-599c-a732-e5256714e625
-- title:
--   Coefficient change on an explicit cocycle class
-- statement:
--   Let $k$ be a commutative ring and $G$ a group, and let $A$, $B$ be $k$-linear representations of $G$ (objects of `Rep k G` in the zeroth universe). Let $\varphi \colon A \to B$ be a morphism of such representations, let $n$ be a natural number, and let $x \colon (\mathrm{Fin}\,n \to G) \to A$ be a function on $n$-tuples of group elements, i.e. an inhomogeneous $n$-cochain with values in $A$. Assume $x$ is a cocycle, that is, the $n$-th differential of the inhomogeneous cochain complex of $A$ sends $x$ to $0$, and assume likewise that the composite cochain $g \mapsto \varphi(x(g))$ is killed by the $n$-th differential of the inhomogeneous cochain complex of $B$. Then the map on $n$-th group cohomology induced by the identity homomorphism of $G$ together with $\varphi$ sends the class of the cocycle determined by $x$ to the class of the cocycle determined by $g \mapsto \varphi(x(g))$; here classes are taken via the canonical projection $\pi$ from cocycles to cohomology, and `cocyclesMk` packages a cochain with a proof that it is a cocycle into an element of the cocycle module.
--
--   This is the effect of a change of coefficients on an explicitly given cohomology class: functoriality of $H^n(G,-)$ in the coefficient module, computed on representatives. It is the special case of the general functoriality in the pair (group homomorphism, equivariant map) at the identity homomorphism, stated in the form in which no composition with the identity appears in the cochain, and it is used in the level arithmetic of idele-theoretic coboundary computations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_map_id_pi_cocyclesMk_apply.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.map_id_pi_cocyclesMk_apply
    {k G : Type} [CommRing k] [Group G] {A B : Rep.{0} k G}
    (φ : A ⟶ B) (n : ℕ) (x : (Fin n → G) → A)
    (hx : (inhomogeneousCochains.d A n).hom x = 0)
    (hx' : (inhomogeneousCochains.d B n).hom (fun g => φ.hom (x g)) = 0) :
    (groupCohomology.map (MonoidHom.id G) φ n).hom (groupCohomology.π A n (groupCohomology.cocyclesMk x hx)) =
      groupCohomology.π B n (groupCohomology.cocyclesMk (fun g => φ.hom (x g)) hx') := by sorry

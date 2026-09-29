-- Prove2me | Theorems.Thm_groupCohomology_inf_injective_and_exact_of_isZero_res
-- name    : groupCohomology.inf_injective_and_exact_of_isZero_res
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/3bf7455e-6279-5d8a-a464-94662e3421f8
-- title:
--   Inflation–restriction in degree q under partial vanishing
-- statement:
--   Let $k$ be a commutative ring, $G$ a group, $A$ a $k$-linear representation of $G$, $S$ a normal subgroup of $G$, and $q$ a natural number. Assume that for every $i$ with $1 \le i < q$ the cohomology object $H^i(S, A)$ — that is, `groupCohomology` of the restriction of $A$ along the inclusion $S \hookrightarrow G$ in degree $i$ — is a zero object. Two assertions are made about the underlying $k$-linear maps of the two canonical morphisms in degree $q$. First, the inflation map $H^q(G/S, A^S) \to H^q(G, A)$, induced by the quotient homomorphism $G \to G/S$ together with the morphism of representations given by the lift of $\rho_A$ to the $S$-invariants $A^S$ viewed as a $G/S$-representation, is injective. Second, every class $x \in H^q(G, A)$ whose image under the restriction map $H^q(G,A) \to H^q(S, A)$ (induced by the inclusion $S \hookrightarrow G$ and the identity of the restricted representation) is zero lies in the image of that inflation map, i.e. $x = \mathrm{inf}(y)$ for some $y \in H^q(G/S, A^S)$. The vanishing of the composite $\mathrm{res} \circ \mathrm{inf}$ is not part of the conclusion.
--
--   This is the Hochschild–Serre inflation–restriction exact sequence in degree $q$, in the form 'inflation is injective and the kernel of restriction is contained in its image', valid once $H^i(S,A)$ vanishes for $0 < i < q$. It is used to produce an isomorphism $H^q(G/S, A^S) \cong H^q(G,A)$ when restriction to $S$ vanishes identically in the relevant degrees, and, in the arithmetic applications, to compare Galois cohomology of a quotient group with that of the full group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_inf_injective_and_exact_of_isZero_res.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory groupCohomology Rep

theorem groupCohomology.inf_injective_and_exact_of_isZero_res
    {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G) (S : Subgroup G) [S.Normal] (q : ℕ)
    (hvan : ∀ i : ℕ, 1 ≤ i → i < q → CategoryTheory.Limits.IsZero (groupCohomology (Rep.res S.subtype A) i)) :
    Function.Injective (groupCohomology.map (A := A.quotientToInvariants S) (B := A)
        (QuotientGroup.mk' S) (Rep.ofHom (A.ρ.quotientToInvariants_lift S)) q).hom ∧
    ∀ x : groupCohomology A q, (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype A)) q).hom x = 0 →
      ∃ y : groupCohomology (A.quotientToInvariants S) q,
        (groupCohomology.map (A := A.quotientToInvariants S) (B := A)
        (QuotientGroup.mk' S) (Rep.ofHom (A.ρ.quotientToInvariants_lift S)) q).hom y = x := by sorry

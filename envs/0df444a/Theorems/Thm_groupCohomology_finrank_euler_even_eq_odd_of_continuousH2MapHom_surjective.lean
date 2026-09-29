-- Prove2me | Theorems.Thm_groupCohomology_finrank_euler_even_eq_odd_of_continuousH2MapHom_surjective
-- name    : groupCohomology.finrank_euler_even_eq_odd_of_continuousH2MapHom_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/5ca28113-ab8b-566e-8c60-4c368492bae8
-- title:
--   Additivity of continuous Euler characteristics in short exact sequences
-- statement:
--   Let $k$ be a field, $G$ a group, and $r \colon G \to \operatorname{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ a homomorphism into the group of $\mathbb{Q}$-algebra automorphisms of $\mathrm{AlgebraicClosure}\,\mathbb{Q}$, used to measure levels. Let $A, B, C$ be $k$-linear representations of $G$ and $\varphi \colon A \to B$, $\psi \colon B \to C$ morphisms of representations such that $\varphi$ is injective on underlying modules, $\psi$ is surjective, and for every $b \in B$ one has $\psi(b) = 0$ if and only if $b$ lies in the image of $\varphi$; thus $0 \to A \to B \to C \to 0$ is exact. Assume $B$ is smooth for $r$: each $m \in B$ admits a finite-dimensional intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ with $B.\rho(s)\,m = m$ for all $s$ whose image $r(s)$ fixes $F$ pointwise. Here $\mathrm{continuousH1}$ denotes the submodule of $H^1$ spanned by the classes of level-constant $1$-cocycles, i.e. the image of $\mathrm{levelCocycles}_1$ under the projection to $H^1$, and $\mathrm{continuousH2}$ denotes the quotient of the module of level-constant $2$-cocycles by those of them that are level coboundaries; $\mathrm{continuousH2MapHom}\ r\ \psi$ is the map induced by $\psi$ over the identity of $G$. Assume the invariants and the continuous $H^1$ and $H^2$ of the two outer terms $A$ and $C$ are all finite-dimensional over $k$, and that $\mathrm{continuousH2MapHom}\ r\ \psi$ is surjective. Then
--   $$\dim A^G + \dim C^G + \dim H^1_{\mathrm{cts}}(B) + \dim H^2_{\mathrm{cts}}(A) + \dim H^2_{\mathrm{cts}}(C) = \dim B^G + \dim H^1_{\mathrm{cts}}(A) + \dim H^1_{\mathrm{cts}}(C) + \dim H^2_{\mathrm{cts}}(B),$$
--   all ranks taken over $k$. No finite-dimensionality is assumed for the middle term $B$.
--
--   This is the additivity of the Euler characteristic $h^0 - h^1 + h^2$ along a short exact sequence of smooth representations, stated without subtraction, for the invariants and the level-constant (continuous) $H^1$ and $H^2$ of this development. It is the arithmetic input to the Euler–Poincaré identity and to the comparison of Euler characteristics under coinduction and restriction, both of which cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_finrank_euler_even_eq_odd_of_continuousH2MapHom_surjective.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory

theorem groupCohomology.finrank_euler_even_eq_odd_of_continuousH2MapHom_surjective {k G : Type u} [Field k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) {A B C : Rep.{u} k G} (φ : A ⟶ B) (ψ : B ⟶ C)
    (hφ : Function.Injective φ.hom) (hψ : Function.Surjective ψ.hom) (hex : ∀ b : B, ψ.hom b = 0 ↔ ∃ a : A, φ.hom a = b)
    (hsm : ∀ m : B, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → B.ρ s m = m)
    [FiniteDimensional k A.ρ.invariants] [FiniteDimensional k C.ρ.invariants]
    [FiniteDimensional k (groupCohomology.continuousH1 r A)] [FiniteDimensional k (groupCohomology.continuousH1 r C)]
    [FiniteDimensional k (groupCohomology.continuousH2 r A)] [FiniteDimensional k (groupCohomology.continuousH2 r C)]
    (hsurj : Function.Surjective (groupCohomology.continuousH2MapHom r ψ)) :
    Module.finrank k A.ρ.invariants + Module.finrank k C.ρ.invariants
        + Module.finrank k (groupCohomology.continuousH1 r B)
        + Module.finrank k (groupCohomology.continuousH2 r A) + Module.finrank k (groupCohomology.continuousH2 r C)
      = Module.finrank k B.ρ.invariants
        + Module.finrank k (groupCohomology.continuousH1 r A) + Module.finrank k (groupCohomology.continuousH1 r C)
        + Module.finrank k (groupCohomology.continuousH2 r B) := by sorry

-- Prove2me | Theorems.Thm_groupCohomology_cup_mem_levelCoboundaries2_of_mem_coboundaries1_right
-- name    : groupCohomology.cup_mem_levelCoboundaries2_of_mem_coboundaries1_right
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/caf62fbd-3e97-5b06-b142-b09a35b74cae
-- title:
--   Cup product with the coboundary of a level-fixed vector
-- statement:
--   Let $k$ be a commutative ring, $G$ a group, and $r\colon G \to \mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ a monoid homomorphism into the $\mathbb Q$-algebra automorphisms of the algebraic closure of $\mathbb Q$. Let $A$, $B$, $N$ be $k$-linear representations of $G$ and let $\varphi\colon A \to B \to N$ be $k$-bilinear and equivariant in the sense of [`Rep.IsEquivariantBilinear`](def/GroupCohomology_CupProduct.html#L13), i.e. $\varphi(\rho_A(s)a, \rho_B(s)b) = \rho_N(s)\varphi(a,b)$ for all $s \in G$, $a \in A$, $b \in B$. Let $f$ be a $1$-cocycle of $A$ satisfying the level-constancy predicate `IsLevelConstant₁ r`, and let $g$ be a $1$-cocycle of $B$. Assume there is a vector $b \in B$ and a finite-dimensional intermediate field $F$ of $\overline{\mathbb Q}/\mathbb Q$ such that $\rho_B(s)b = b$ whenever $r(s)$ lies in the fixing subgroup of $F$, and assume $g(s) = \rho_B(s)b - b$ for all $s$. Then the $2$-cochain underlying the cup product `cup φ hφ f g`, namely $(s,t) \mapsto \varphi\bigl(f(s), \rho_B(s)g(t)\bigr)$, lies in `levelCoboundaries₂ r N`: it is the coboundary, under `d₁₂`, of a $1$-cochain that is itself level-constant with respect to $r$.
--
--   This is the right-hand half of the verification that the explicit cup product on $1$-cochains descends to level-constant (continuous) cohomology, the coboundary directions in the two arguments being treated separately. It is used in the construction carried out by [`groupCohomology.exists_theta1`](thm.html#groupCohomology.exists_theta1).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_cup_mem_levelCoboundaries2_of_mem_coboundaries1_right.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_CupProduct

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory groupCohomology

theorem groupCohomology.cup_mem_levelCoboundaries2_of_mem_coboundaries1_right
    {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    {A B N : Rep.{u} k G} (φ : A →ₗ[k] B →ₗ[k] N) (hφ : Rep.IsEquivariantBilinear A B N φ)
    (f : cocycles₁ A) (g : cocycles₁ B) (hf : IsLevelConstant₁ r (⇑f))
    (b : B) (hb : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → B.ρ s b = b)
    (hg : ∀ s, g s = B.ρ s b - b) :
    (cup φ hφ f g : G × G → N) ∈ levelCoboundaries₂ r N := by sorry

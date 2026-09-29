-- Prove2me | Theorems.Thm_groupCohomology_finrank_continuousClasses_eq_finrank_of_isUnit_index_of_forall_apply_eq
-- name    : groupCohomology.finrank_continuousClasses_eq_finrank_of_isUnit_index_of_forall_apply_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/898dc9f3-426a-5b3d-a8f1-993f52954f8f
-- title:
--   Dimension of level-constant H¹(G,A) via cocycles on S
-- statement:
--   Let $k$ be a field, $G$ a group, and $r : G \to \mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ a homomorphism into the $\mathbb Q$-algebra automorphisms of `AlgebraicClosure ℚ`; let $A$ be a $k$-linear representation of $G$ (an object of `Rep k G`) and $S \le G$ a normal subgroup of finite index whose index is invertible in $k$, acting trivially on $A$ (that is, $A.\rho(s)v = v$ for all $s \in S$, $v \in A$), and open for the level filtration in the sense that there is a finite-dimensional intermediate field $F_0$ of $\overline{\mathbb Q}/\mathbb Q$ with $r(s) \in F_0^{\mathrm{fix}}$ implying $s \in S$. Let $\mathrm{adm}$ be a $k$-submodule of $H^1(G,A)$ consisting exactly of the classes $(H1\pi\,A)(c)$ of those $1$-cocycles $c$ that are level-constant for $r$, i.e. for which some finite-dimensional intermediate field $F$ satisfies $c(gu) = c(g)$ whenever $r(u)$ fixes $F$ pointwise; and let $W$ be a $k$-submodule of `cocycles₁ (Rep.res S.subtype A)` consisting exactly of those $1$-cocycles $c$ of $S$ with values in $A$ that are level-constant for $r|_S$ and satisfy $A.\rho(g)(c(t)) = c(s)$ whenever $g^{-1}sg = t$ with $s,t \in S$, $g \in G$. Then $\dim_k \mathrm{adm} = \dim_k W$.
--
--   This is the level-constant ("continuous") form of inflation–restriction in degree one at an index invertible in the coefficients: classes of $H^1(G,A)$ represented by level-constant cocycles are counted by the level-constant, conjugation-equivariant homomorphisms $S \to A$. It feeds the dimension count for continuous $H^1$ in [`groupCohomology.finrank_continuousH1_eq_invariants_add_dualTwist_add_finrank_mul_of_tame_intermediateField`](thm.html#groupCohomology.finrank_continuousH1_eq_invariants_add_dualTwist_add_finrank_mul_of_tame_intermediateField).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_finrank_continuousClasses_eq_finrank_of_isUnit_index_of_forall_apply_eq.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Module groupCohomology

theorem groupCohomology.finrank_continuousClasses_eq_finrank_of_isUnit_index_of_forall_apply_eq
    {k G : Type u} [Field k] [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (A : Rep.{u} k G) (S : Subgroup G) [S.Normal] [S.FiniteIndex]
    (hindex : IsUnit ((S.index : k)))
    (htriv : ∀ s ∈ S, ∀ v : A, A.ρ s v = v)
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      ∀ s : G, r s ∈ F₀.fixingSubgroup → s ∈ S)
    (adm : Submodule k (H1 A))
    (hadm : ∀ x, x ∈ adm ↔ ∃ c : cocycles₁ A, IsLevelConstant₁ r c.val ∧ (H1π A).hom c = x)
    (W : Submodule k (cocycles₁ (Rep.res S.subtype A)))
    (hW : ∀ c, c ∈ W ↔ IsLevelConstant₁ (r.comp S.subtype) c.val ∧
      ∀ (g : G) (s t : S), (g⁻¹ * s * g : G) = t → A.ρ g (c t) = c s) :
    finrank k adm = finrank k W := by sorry

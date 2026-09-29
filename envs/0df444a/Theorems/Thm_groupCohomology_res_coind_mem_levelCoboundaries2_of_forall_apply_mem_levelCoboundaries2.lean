-- Prove2me | Theorems.Thm_groupCohomology_res_coind_mem_levelCoboundaries2_of_forall_apply_mem_levelCoboundaries2
-- name    : groupCohomology.res_coind_mem_levelCoboundaries2_of_forall_apply_mem_levelCoboundaries2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/baf3cca7-9e71-550d-b9b3-cbe9dcb787d4
-- title:
--   Semi-local Shapiro–Mackey injectivity in degree two for coinduced modules
-- statement:
--   Let $k$ be a commutative ring, $V$ a $k$-module, $G$ a group, and let $\Gamma$ denote the group of $\mathbb{Q}$-algebra automorphisms of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$, with $r : G \to \Gamma$ a group homomorphism. Let $U \trianglelefteq \Gamma$ be a normal subgroup which is open in the sense that there is an intermediate field $F_0$ of $\mathbb{Q}$ in $\mathrm{AlgebraicClosure}\ \mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, whose fixing subgroup is contained in $U$. Let $\gamma : \Gamma/(U \sqcup r(G)) \to \Gamma$ be a set-theoretic section, so $\gamma(t)$ maps to $t$ for every $t$. Let $c : G \times G \to \mathrm{Res}_r\,\mathrm{CoInd}_{U \hookrightarrow \Gamma}(V)$ be a $2$-cochain with values in the $U$-trivial module $V$ coinduced along $U \hookrightarrow \Gamma$ and then restricted along $r$, and assume $c$ lies in [`groupCohomology.levelCocycles₂`](def/GroupCohomology_ContinuousH2.html#L85) for $r$ and this representation. Assume further that for every $t \in \Gamma/(U \sqcup r(G))$ the map $(d,d') \mapsto c(d,d')(\gamma(t))$ on $r^{-1}(U) \times r^{-1}(U)$, obtained by evaluating the coinduced functions $\Gamma \to V$ at $\gamma(t)$, lies in [`groupCohomology.levelCoboundaries₂`](def/GroupCohomology_ContinuousH2.html#L92) for $r$ composed with the inclusion of $r^{-1}(U)$ and the trivial $r^{-1}(U)$-module $V$. Then $c$ itself lies in [`groupCohomology.levelCoboundaries₂`](def/GroupCohomology_ContinuousH2.html#L92) for $r$ and $\mathrm{Res}_r\,\mathrm{CoInd}_{U \hookrightarrow \Gamma}(V)$.
--
--   This is the injectivity half, at the level of the project's level cocycles and coboundaries, of the semi-local Shapiro–Mackey description of degree-two cohomology of $\mathrm{Res}_r\,\mathrm{CoInd}_U^{\Gamma} V$ as a product of copies of $H^2(r^{-1}(U), V)$ indexed by the double cosets $U \backslash \Gamma / r(G)$: a level $2$-cocycle all of whose components are level coboundaries is itself a level coboundary. It is used in the construction of a global class with prescribed local restrictions, through [`groupCohomology.exists_forall_locRes_continuousH2S_coind_trivial_eq_add_smul`](thm.html#groupCohomology.exists_forall_locRes_continuousH2S_coind_trivial_eq_add_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_res_coind_mem_levelCoboundaries2_of_forall_apply_mem_levelCoboundaries2.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory

theorem groupCohomology.res_coind_mem_levelCoboundaries2_of_forall_apply_mem_levelCoboundaries2
    {k : Type u} [CommRing k] {V : Type u} [AddCommGroup V] [Module k V]
    {G : Type u} [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (U : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [U.Normal]
    (hU : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup ≤ U)
    (γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (U ⊔ r.range) → (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hγ : ∀ t, (γ t : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (U ⊔ r.range)) = t)
    (c : G × G → Rep.res r (Rep.coind U.subtype (Rep.trivial k ↥U V)))
    (hc : c ∈ groupCohomology.levelCocycles₂ r (Rep.res r (Rep.coind U.subtype (Rep.trivial k ↥U V))))
    (h : ∀ t, (fun d : ↥(U.comap r) × ↥(U.comap r) =>
        ((c ((d.1 : G), (d.2 : G)) : Rep.coind U.subtype (Rep.trivial k ↥U V)) :
          (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → V) (γ t))
      ∈ groupCohomology.levelCoboundaries₂ (r.comp (U.comap r).subtype) (Rep.trivial k ↥(U.comap r) V)) :
    c ∈ groupCohomology.levelCoboundaries₂ r (Rep.res r (Rep.coind U.subtype (Rep.trivial k ↥U V))) := by sorry

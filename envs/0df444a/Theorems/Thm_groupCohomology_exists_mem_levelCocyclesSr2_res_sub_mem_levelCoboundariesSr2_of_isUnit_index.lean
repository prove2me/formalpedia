-- Prove2me | Theorems.Thm_groupCohomology_exists_mem_levelCocyclesSr2_res_sub_mem_levelCoboundariesSr2_of_isUnit_index
-- name    : groupCohomology.exists_mem_levelCocyclesSr2_res_sub_mem_levelCoboundariesSr2_of_isUnit_index
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/d4443a3f-71d3-5cf1-86d2-fa2c7198b377
-- title:
--   Degree-two restriction onto G-invariant S-level classes is surjective
-- statement:
--   Let $k$ be a commutative ring, $G$ a group, $r : G \to \operatorname{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ a homomorphism to the group of $\mathbb Q$-algebra automorphisms of `AlgebraicClosure ℚ`, $S$ a finite set of rational primes, and $M$ a $k$-linear representation of $G$. Assume that every vector $m \in M$ is fixed by some level subgroup: there is an intermediate field $F$ of $\overline{\mathbb Q}/\mathbb Q$ which is finite-dimensional over $\mathbb Q$ and such that for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a nonunit of $A$ the image of the inertia subgroup of $A$ over $\mathbb Q$ lies in the fixing subgroup of $F$, with $\rho(g)m = m$ whenever $r(g)$ fixes $F$ pointwise. Let $N \trianglelefteq G$ be a normal subgroup of finite index whose index is invertible in $k$, and assume $N$ contains $r^{-1}(\operatorname{Gal}(\overline{\mathbb Q}/F_0))$ for some such field $F_0$ unramified outside $S$ in the above sense. Let $x : N \times N \to M$ belong to `levelCocyclesSr₂` for the level map $r|_N$, the set $S$ and the restricted representation, and suppose the class of $x$ is $G$-invariant in the sense that for every $g \in G$ the difference between $(a,b) \mapsto \rho(g)\,x(g^{-1}ag, g^{-1}bg)$ (conjugation taken inside the normal subgroup $N$) and $x$ lies in `levelCoboundariesSr₂` for the same data. Then there exists $y : G \times G \to M$ in `levelCocyclesSr₂ r S M` whose restriction $(a,b) \mapsto y(a,b)$ to $N \times N$ differs from $x$ by an element of `levelCoboundariesSr₂` for $r|_N$, $S$ and the restricted representation.
--
--   This is the cochain-level form of the statement that restriction $H^2_S(G,M) \to H^2_S(N,M)^{G/N}$ is surjective when the index $(G:N)$ is invertible in $k$, for the variant of group cohomology whose cochains are constant along level subgroups coming from finite subfields of $\overline{\mathbb Q}$ unramified outside $S$; the classical mechanism is restriction–corestriction together with the double coset formula for a normal subgroup. It is used in the construction of $S$-ramified degree-two classes for the full Galois group from classes over a subgroup, via [`groupCohomology.exists_forall_eq_res_continuousH2Sr_trivial_add_smul_of_exists_sq_eq_neg_one`](thm.html#groupCohomology.exists_forall_eq_res_continuousH2Sr_trivial_add_smul_of_exists_sq_eq_neg_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_mem_levelCocyclesSr2_res_sub_mem_levelCoboundariesSr2_of_isUnit_index.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology

theorem groupCohomology.exists_mem_levelCocyclesSr2_res_sub_mem_levelCoboundariesSr2_of_isUnit_index
    {k G : Type u} [CommRing k] [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (S : Finset Nat.Primes) (M : Rep.{u} k G)
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
      ∀ g : G, r g ∈ F.fixingSubgroup → M.ρ g m = m)
    (N : Subgroup G) [N.Normal] [N.FiniteIndex] (hu : IsUnit ((N.index : ℕ) : k))
    (hN : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), F₀.IsUnramifiedOutside S ∧ F₀.fixingSubgroup.comap r ≤ N)
    (x : ↥N × ↥N → M) (hx : x ∈ levelCocyclesSr₂ (r.comp N.subtype) S (Rep.res N.subtype M))
    (hinv : ∀ g : G,
      (fun ab : ↥N × ↥N => M.ρ g (x (MulAut.conjNormal g⁻¹ ab.1, MulAut.conjNormal g⁻¹ ab.2))) - x ∈
        levelCoboundariesSr₂ (r.comp N.subtype) S (Rep.res N.subtype M)) :
    ∃ y : G × G → M, y ∈ levelCocyclesSr₂ r S M ∧
      (fun ab : ↥N × ↥N => y ((ab.1 : G), (ab.2 : G))) - x ∈ levelCoboundariesSr₂ (r.comp N.subtype) S (Rep.res N.subtype M) := by sorry

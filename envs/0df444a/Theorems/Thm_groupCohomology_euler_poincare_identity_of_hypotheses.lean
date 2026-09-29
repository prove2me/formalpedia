-- Prove2me | Theorems.Thm_groupCohomology_euler_poincare_identity_of_hypotheses
-- name    : groupCohomology.euler_poincare_identity_of_hypotheses
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/16336f84-81cb-58da-bcb5-ab353c3d870e
-- title:
--   Local Euler–Poincaré identity from five named inputs
-- statement:
--   Fix a field $k$ of characteristic $p$ ($p$ prime), a group $G$, a homomorphism $r \colon G \to \mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$, a character $\chi \colon G \to k^{\times}$ and an arbitrary predicate $\mathrm{IsTame}$ on pairs consisting of a subgroup $S \le G$ and an object of $\mathrm{Rep}_k S$. Call $S$ *open* if some finite-dimensional intermediate field $F_0$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ has $r^{-1}(F_0^{\mathrm{fix}}) \le S$, and call $N \in \mathrm{Rep}_k S$ *smooth* if every vector of $N$ is fixed by all $s \in S$ with $r(s)$ in the fixing subgroup of some finite-dimensional intermediate field. Cohomology is taken for the level map $r \circ S \hookrightarrow G$: `continuousH1` is the image in $H^1$ of the level $1$-cocycles, and `continuousH2` is the level $2$-cocycles modulo the level $2$-coboundaries. Assume, for all open $S$: (HFIN) both groups are finite-dimensional for smooth finite-dimensional $N$; (HD2) `continuousH2MapHom` is surjective for any morphism $\psi \colon B \to C$ with $B$ smooth finite-dimensional and $\psi$ surjective; (HTAME1) if $\mathrm{IsTame}(S,N)$ and $H^1_{\mathrm{cts}}$ is finite-dimensional, then $\dim H^1_{\mathrm{cts}} = \dim N^{S} + \dim (N^{\vee} \otimes \chi)^{S} + [G:S]\dim N$, where $N^{\vee}\otimes\chi$ is the dual representation scaled by $\chi$; (HTAME2) if $\mathrm{IsTame}(S,N)$ then $\dim H^2_{\mathrm{cts}} = \dim (N^{\vee}\otimes\chi)^{S}$; (HARITH) if $N$ is smooth, finite-dimensional, nonzero and has no $S$-stable submodule other than $\bot$ and $\top$, then either $\mathrm{IsTame}(S,N)$ holds, or there is an open $S' \le S$ normal of index $p$ in $S$ whose image in $\mathrm{Aut}(N)$ has strictly smaller cardinality than that of $S$. The conclusion is that for every open $S$ and every smooth finite-dimensional $N \in \mathrm{Rep}_k S$, $$\dim_k H^1_{\mathrm{cts}}(S,N) = \dim_k N^{S} + \dim_k H^2_{\mathrm{cts}}(S,N) + [G:S]\,\dim_k N,$$ with $[G:S]$ the subgroup index.
--
--   This is the local Euler–Poincaré characteristic formula $\chi(G_K,N) = -[K:\mathbb{Q}_p]\dim N$ in the shape $h^1 = h^0 + h^2 + [G:S]\dim N$, stated for an abstract group with a level structure and reduced to five named inputs: finiteness, right exactness of $H^2_{\mathrm{cts}}$, the tame computations in degrees one and two, and a ramification-theoretic dichotomy for irreducible modules. It is applied in [`groupCohomology.finrank_continuousClasses_eq_invariants_add_continuousH2_add_finrank_of_primeLocal`](thm.html#groupCohomology.finrank_continuousClasses_eq_invariants_add_continuousH2_add_finrank_of_primeLocal), where the inputs are verified for local Galois groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_euler_poincare_identity_of_hypotheses.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_Selmer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory

theorem groupCohomology.euler_poincare_identity_of_hypotheses {k G : Type u} [Field k] [Group G] (p : ℕ) [Fact p.Prime] [CharP k p]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (χ : G →* kˣ)
    (IsTame : ∀ S : Subgroup G, Rep.{u} k S → Prop)

    (HFIN : ∀ (S : Subgroup G), (∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap r ≤ S) →
      ∀ (N : Rep.{u} k S), (∀ n : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ s : S, (r.comp S.subtype) s ∈ F.fixingSubgroup → N.ρ s n = n) → FiniteDimensional k N →
        FiniteDimensional k (groupCohomology.continuousH1 (r.comp S.subtype) N) ∧
          FiniteDimensional k (groupCohomology.continuousH2 (r.comp S.subtype) N))

    (HD2 : ∀ (S : Subgroup G), (∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap r ≤ S) →
      ∀ (B C : Rep.{u} k S) (ψ : B ⟶ C), (∀ n : B, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ s : S, (r.comp S.subtype) s ∈ F.fixingSubgroup → B.ρ s n = n) → FiniteDimensional k B →
        Function.Surjective ψ.hom → Function.Surjective (groupCohomology.continuousH2MapHom (r.comp S.subtype) ψ))

    (HTAME1 : ∀ (S : Subgroup G), (∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap r ≤ S) →
      ∀ (N : Rep.{u} k S), (∀ n : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ s : S, (r.comp S.subtype) s ∈ F.fixingSubgroup → N.ρ s n = n) → FiniteDimensional k N →
        FiniteDimensional k (groupCohomology.continuousH1 (r.comp S.subtype) N) →
        IsTame S N →
        Module.finrank k (groupCohomology.continuousH1 (r.comp S.subtype) N)
          = Module.finrank k N.ρ.invariants + Module.finrank k (N.dualTwist (χ.comp S.subtype)).ρ.invariants
            + S.index * Module.finrank k N)

    (HTAME2 : ∀ (S : Subgroup G), (∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap r ≤ S) →
      ∀ (N : Rep.{u} k S), (∀ n : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ s : S, (r.comp S.subtype) s ∈ F.fixingSubgroup → N.ρ s n = n) → FiniteDimensional k N →
        IsTame S N →
        Module.finrank k (groupCohomology.continuousH2 (r.comp S.subtype) N)
          = Module.finrank k (N.dualTwist (χ.comp S.subtype)).ρ.invariants)

    (HARITH : ∀ (S : Subgroup G), (∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap r ≤ S) →
      ∀ (N : Rep.{u} k S), (∀ n : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ s : S, (r.comp S.subtype) s ∈ F.fixingSubgroup → N.ρ s n = n) → FiniteDimensional k N → Module.finrank k N ≠ 0 →
        (∀ W : Submodule k N, (∀ (s : S) (v : N), v ∈ W → N.ρ s v ∈ W) → W = ⊥ ∨ W = ⊤) →
        IsTame S N ∨
        (∃ (S' : Subgroup G) (hle : S' ≤ S), (∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap r ≤ S') ∧ (S'.subgroupOf S).Normal ∧ (S'.subgroupOf S).index = p ∧
            Nat.card (MonoidHom.mrange (N.ρ.comp (Subgroup.inclusion hle)))
              < Nat.card (MonoidHom.mrange N.ρ)))

    (S : Subgroup G) (hS : (∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap r ≤ S)) (N : Rep.{u} k S)
    (hsm : (∀ n : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ s : S, (r.comp S.subtype) s ∈ F.fixingSubgroup → N.ρ s n = n)) [FiniteDimensional k N] :
    Module.finrank k (groupCohomology.continuousH1 (r.comp S.subtype) N)
            = Module.finrank k N.ρ.invariants + Module.finrank k (groupCohomology.continuousH2 (r.comp S.subtype) N)
              + S.index * Module.finrank k N := by sorry

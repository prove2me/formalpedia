-- Prove2me | Theorems.Thm_groupCohomology_exists_mem_split_adjoin_rootsOfUnity_of_padic
-- name    : groupCohomology.exists_mem_split_adjoin_rootsOfUnity_of_padic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/0aa506f3-27cb-5c78-92a7-f04b041578f6
-- title:
--   Splitting of local Brauer classes by cyclotomic layers
-- statement:
--   Let $q$ be a prime, write $\Omega$ for the algebraic closure `PadicAlgCl q` of $\mathbb{Q}_q$, and let $K$ be an intermediate field of $\Omega/\mathbb{Q}_q$ that is finite over $\mathbb{Q}_q$. Let $r$ be a group homomorphism from $\mathrm{Aut}_K(\Omega)$ to $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$, subject to two cofinality hypotheses: `hlevel`, that for every intermediate field $E$ of $\Omega/K$ finite over $K$ there is an intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ finite over $\mathbb{Q}$ with $r^{-1}(\mathrm{Fix}(F)) \subseteq \mathrm{Fix}(E)$, and `hopen`, the converse direction, that for every such $F$ there is such an $E$ with $r(\mathrm{Fix}(E)) \subseteq \mathrm{Fix}(F)$, where $\mathrm{Fix}$ denotes the fixing subgroup. Let $x$ be an element of `continuousH2 r (Rep.ofAlgebraAutOnUnits K (PadicAlgCl q))`, that is, of the quotient of the submodule `levelCocycles₂` of inhomogeneous $2$-cocycles of $\mathrm{Aut}_K(\Omega)$ acting on $\Omega^\times$ by the submodule of those elements of `levelCocycles₂` lying in `levelCoboundaries₂`. Then there is an $N > 0$ such that, putting $L_N := K(\{\zeta \in \Omega : \zeta^{q^N-1} = 1\})$, the extension $L_N/K$ is finite and normal, and $x$ is the class of $\mathrm{inf}(f)$ for some $f : \mathrm{Aut}_K(L_N)^2 \to \mathrm{Additive}\,(L_N)^\times$ in `cocycles₂` of `Rep.ofAlgebraAutOnUnits K L_N` whose inflation `unitsInflate₂ L_N f` lies in `levelCocycles₂`; the conclusion is phrased as membership of $x$ in the set of classes of this shape, via `continuousH2π`.
--
--   This is the classical statement that every Brauer class of a $p$-adic field is split by an unramified extension, here in the form that $H^2$ of $K$ with values in $\Omega^\times$ (computed with the level structure supplied by $r$) is the union of the images of the inflation maps from the cyclotomic layers $K(\mu_{q^N-1})$. It feeds the computation of torsion in `continuousH2` for local fields and the extraction, from a given class, of a cyclotomic layer over which its restriction becomes a level-coboundary.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_mem_split_adjoin_rootsOfUnity_of_padic.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_GaloisUnitsInflation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory groupCohomology IntermediateField

theorem groupCohomology.exists_mem_split_adjoin_rootsOfUnity_of_padic
    (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]
    (r : (PadicAlgCl q ≃ₐ[K] PadicAlgCl q) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hlevel : ∀ E : IntermediateField K (PadicAlgCl q), FiniteDimensional K E →
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ σ : PadicAlgCl q ≃ₐ[K] PadicAlgCl q, r σ ∈ F.fixingSubgroup → σ ∈ E.fixingSubgroup)
    (hopen : ∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F →
      ∃ E : IntermediateField K (PadicAlgCl q), FiniteDimensional K E ∧
        ∀ σ : PadicAlgCl q ≃ₐ[K] PadicAlgCl q, σ ∈ E.fixingSubgroup → r σ ∈ F.fixingSubgroup)
    (x : continuousH2 r (Rep.ofAlgebraAutOnUnits K (PadicAlgCl q))) :
    ∃ (N : ℕ) (_ : 0 < N)
      (_ : FiniteDimensional K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))
      (_ : Normal K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})),
      x ∈ {x | ∃ (f : ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[K] (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) × ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[K] (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) → Additive ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))ˣ)
          (_ : f ∈ cocycles₂ (Rep.ofAlgebraAutOnUnits K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})))
          (h : unitsInflate₂ (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) f ∈ levelCocycles₂ r (Rep.ofAlgebraAutOnUnits K (PadicAlgCl q))),
          x = continuousH2π r (Rep.ofAlgebraAutOnUnits K (PadicAlgCl q)) ⟨unitsInflate₂ (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) f, h⟩} := by sorry

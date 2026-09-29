-- Prove2me | Theorems.Thm_groupCohomology_mem_split_of_restrict_mem_levelCoboundaries2
-- name    : groupCohomology.mem_split_of_restrict_mem_levelCoboundaries2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/4325fd5f-101e-54f5-b153-0bc85bd7ea46
-- title:
--   Continuous degree-two inflation: classes split by L are inflated
-- statement:
--   Let $K \subseteq \Omega$ be fields with $\Omega/K$ Galois, and let $r \colon (\Omega \simeq_{\mathrm{alg}[K]} \Omega) \to \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ be a group homomorphism (a "level map"), subject to two cofinality hypotheses: `hlevel`, that for every intermediate field $E$ of $\Omega/K$ finite over $K$ there is an intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ finite over $\mathbb{Q}$ with $r^{-1}(\mathrm{Gal}(\overline{\mathbb{Q}}/F)) \subseteq \mathrm{Gal}(\Omega/E)$, and `hopen`, the converse, that for every such $F$ there is such an $E$ with $r(\mathrm{Gal}(\Omega/E)) \subseteq \mathrm{Gal}(\overline{\mathbb{Q}}/F)$. Let $L$ be an intermediate field of $\Omega/K$, finite-dimensional and normal over $K$, and let $c$ lie in the subgroup `levelCocycles₂ r (Rep.ofAlgebraAutOnUnits K Ω)` of $2$-cochains on $\mathrm{Gal}(\Omega/K)$ valued in the $\mathrm{Gal}(\Omega/K)$-module $\Omega^\times$ (written additively). Assume `hres`: the restriction of the underlying cochain of $c$ along the homomorphism $\mathrm{Gal}(\Omega/L) \cong \mathrm{Gal}(\Omega/L)^{\mathrm{fix}} \hookrightarrow \mathrm{Gal}(\Omega/K)$, obtained from `IntermediateField.fixingSubgroupEquiv L` followed by the inclusion of the fixing subgroup, belongs to `levelCoboundaries₂` for the composed level map and the module $\Omega^\times$ over $L$. Then the image of $c$ in the quotient `continuousH2 r (Rep.ofAlgebraAutOnUnits K Ω)` of `levelCocycles₂` by the preimage of `levelCoboundaries₂`, under the projection `continuousH2π`, lies in the subset of classes of the form `continuousH2π r (Rep.ofAlgebraAutOnUnits K Ω) ⟨unitsInflate₂ L f, h⟩` for some $f \colon \mathrm{Gal}(L/K) \times \mathrm{Gal}(L/K) \to \mathrm{Additive}\, L^\times$ in `cocycles₂ (Rep.ofAlgebraAutOnUnits K L)` whose inflation `unitsInflate₂ L f` is itself a level cocycle.
--
--   This is the surjectivity half of inflation–restriction in degree two for the continuous (level-constant) cohomology of $\Omega^\times$: a class killed by restriction to $\mathrm{Gal}(\Omega/L)$ comes from a $2$-cocycle of $\mathrm{Gal}(L/K)$ with values in $L^\times$, as in the identification of $\mathrm{Br}(L/K)$ with $\ker(\mathrm{Br}(K) \to \mathrm{Br}(L))$. It is used in [`groupCohomology.exists_mem_split_adjoin_rootsOfUnity_of_padic`](thm.html#groupCohomology.exists_mem_split_adjoin_rootsOfUnity_of_padic), where classes over a $p$-adic field are exhibited as split by an explicit cyclotomic extension.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_mem_split_of_restrict_mem_levelCoboundaries2.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_GaloisUnitsInflation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory groupCohomology

theorem groupCohomology.mem_split_of_restrict_mem_levelCoboundaries2
    {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    (r : (Ω ≃ₐ[K] Ω) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hlevel : ∀ E : IntermediateField K Ω, FiniteDimensional K E →
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ σ : Ω ≃ₐ[K] Ω, r σ ∈ F.fixingSubgroup → σ ∈ E.fixingSubgroup)
    (hopen : ∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F →
      ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
        ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ E.fixingSubgroup → r σ ∈ F.fixingSubgroup)
    (L : IntermediateField K Ω) [FiniteDimensional K L] [Normal K L]
    (c : levelCocycles₂ r (Rep.ofAlgebraAutOnUnits K Ω))
    (hres : (fun g : (Ω ≃ₐ[L] Ω) × (Ω ≃ₐ[L] Ω) =>
        (c.1 : (Ω ≃ₐ[K] Ω) × (Ω ≃ₐ[K] Ω) → (Rep.ofAlgebraAutOnUnits K Ω))
          ((L.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv L).symm.toMonoidHom) g.1,
           (L.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv L).symm.toMonoidHom) g.2))
        ∈ levelCoboundaries₂ (r.comp (L.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv L).symm.toMonoidHom))
            (Rep.ofAlgebraAutOnUnits L Ω)) :
    continuousH2π r (Rep.ofAlgebraAutOnUnits K Ω) c ∈ {x | ∃ (f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Additive (L)ˣ)
          (_ : f ∈ cocycles₂ (Rep.ofAlgebraAutOnUnits K L))
          (h : unitsInflate₂ L f ∈ levelCocycles₂ r (Rep.ofAlgebraAutOnUnits K Ω)),
          x = continuousH2π r (Rep.ofAlgebraAutOnUnits K Ω) ⟨unitsInflate₂ L f, h⟩} := by sorry

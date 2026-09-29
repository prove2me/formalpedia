-- Prove2me | Theorems.Thm_groupCohomology_mem_coboundaries2_of_unitsInflate2_mem_levelCoboundaries2
-- name    : groupCohomology.mem_coboundaries2_of_unitsInflate2_mem_levelCoboundaries2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/538dcf53-f8c4-58c0-b8d4-113d7cce469f
-- title:
--   Injectivity of degree-two inflation via continuous Hilbert 90
-- statement:
--   Let $K$ and $\Omega$ be fields with $\Omega$ a Galois extension of $K$ (an algebra instance together with `IsGalois K Ω`), and let $r \colon \mathrm{Gal}(\Omega/K) \to \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ be a group homomorphism into the automorphism group of `AlgebraicClosure ℚ` over $\mathbb{Q}$. Assume the openness condition `hopen`: for every intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ that is finite-dimensional over $\mathbb{Q}$ there is an intermediate field $E$ of $\Omega/K$, finite-dimensional over $K$, such that every $\sigma \in \mathrm{Gal}(\Omega/K)$ lying in the fixing subgroup of $E$ has $r\,\sigma$ in the fixing subgroup of $F$. Let $L$ be an intermediate field of $\Omega/K$ which is finite-dimensional and normal over $K$, and let $f \colon \mathrm{Gal}(L/K) \times \mathrm{Gal}(L/K) \to$ `Additive Lˣ` be a $2$-cocycle, i.e. an element of `cocycles₂` of the representation `Rep.ofAlgebraAutOnUnits K L` of $\mathrm{Gal}(L/K)$ on the unit group $L^\times$ written additively. Suppose that the inflated $2$-cochain `unitsInflate₂ L f` of $\mathrm{Gal}(\Omega/K)$ with values in `Additive Ωˣ` lies in `levelCoboundaries₂ r (Rep.ofAlgebraAutOnUnits K Ω)`, the subgroup of coboundaries cut out using the level map $r$. Then $f$ itself lies in `coboundaries₂ (Rep.ofAlgebraAutOnUnits K L)`, i.e. $f$ is the coboundary of a $1$-cochain $\mathrm{Gal}(L/K) \to L^\times$.
--
--   This is the degree-two inflation injectivity of the inflation–restriction sequence in its continuous form: the inflation map $H^2(\mathrm{Gal}(L/K), L^\times) \to H^2(\mathrm{Gal}(\Omega/K), \Omega^\times)$ is injective on classes whose inflation is bounded by a cochain satisfying the level condition attached to $r$, the required vanishing of $H^1$ of $\mathrm{Gal}(\Omega/L)$ being supplied by [`groupCohomology.exists_eq_smul_div_of_isMulCocycle1_fixingSubgroup`](thm.html#groupCohomology.exists_eq_smul_div_of_isMulCocycle1_fixingSubgroup). It is used in the construction and analysis of level $2$-cocycles attached to characters and in the splitting results for extensions obtained by adjoining roots of unity in the $p$-adic setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_mem_coboundaries2_of_unitsInflate2_mem_levelCoboundaries2.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_GaloisUnitsInflation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory groupCohomology

theorem groupCohomology.mem_coboundaries2_of_unitsInflate2_mem_levelCoboundaries2
    {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    (r : (Ω ≃ₐ[K] Ω) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hopen : ∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F →
      ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
        ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ E.fixingSubgroup → r σ ∈ F.fixingSubgroup)
    (L : IntermediateField K Ω) [FiniteDimensional K L] [Normal K L]
    {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Additive (L)ˣ}
    (hf : f ∈ cocycles₂ (Rep.ofAlgebraAutOnUnits K L))
    (h : unitsInflate₂ L f ∈ levelCoboundaries₂ r (Rep.ofAlgebraAutOnUnits K Ω)) :
    f ∈ coboundaries₂ (Rep.ofAlgebraAutOnUnits K L) := by sorry

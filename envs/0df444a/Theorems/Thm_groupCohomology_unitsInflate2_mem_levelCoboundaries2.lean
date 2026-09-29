-- Prove2me | Theorems.Thm_groupCohomology_unitsInflate2_mem_levelCoboundaries2
-- name    : groupCohomology.unitsInflate2_mem_levelCoboundaries2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/d2bc9d2b-4793-5d0b-a2fe-0908a229abc1
-- title:
--   Inflation carries 2-coboundaries to level coboundaries
-- statement:
--   Let $K$ and $\Omega$ be fields with $\Omega$ a $K$-algebra, and let $r\colon(\Omega\simeq_{\mathrm{alg}[K]}\Omega)\to(\overline{\mathbb{Q}}\simeq_{\mathrm{alg}[\mathbb{Q}]}\overline{\mathbb{Q}})$ be a group homomorphism from the group of $K$-algebra automorphisms of $\Omega$ to that of `AlgebraicClosure ℚ` over $\mathbb{Q}$. Let $L$ be an intermediate field of $\Omega/K$ that is normal over $K$, and assume $(hL)$ there is an intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, such that every $\sigma$ with $r\sigma$ in the fixing subgroup of $F$ lies in the fixing subgroup of $L$. Let $f\colon(L\simeq_{\mathrm{alg}[K]}L)^{2}\to\mathrm{Additive}\,L^{\times}$ be a $2$-coboundary for the representation `Rep.ofAlgebraAutOnUnits K L` of $\mathrm{Aut}_K(L)$ on $L^{\times}$ written additively, i.e. $f=d^{1}_{2}x$ for some $1$-cochain $x$. The conclusion is that the inflated $2$-cochain `unitsInflate₂ L f`, namely $(g,h)\mapsto$ the image in $\Omega^{\times}$ under $L\to\Omega$ of $f(g|_{L},h|_{L})$, belongs to `levelCoboundaries₂ r (Rep.ofAlgebraAutOnUnits K Ω)`: it is the coboundary of a $1$-cochain of $\mathrm{Aut}_K(\Omega)$ with values in $\Omega^{\times}$ which is unchanged under right multiplication by any element whose image under $r$ fixes some finite subextension $F/\mathbb{Q}$ pointwise.
--
--   This is the coboundary half of the statement that inflation along restriction $\mathrm{Aut}_K(\Omega)\to\mathrm{Aut}_K(L)$ induces a map from $H^2(\mathrm{Gal}(L/K),L^\times)$ to the continuous (level-wise locally constant) $H^2$ of $\mathrm{Aut}_K(\Omega)$ acting on $\Omega^\times$. It is used in the construction of that induced map and in the criteria for a scaled Kummer cocycle to be a level coboundary.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_unitsInflate2_mem_levelCoboundaries2.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_GaloisUnitsInflation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory groupCohomology

theorem groupCohomology.unitsInflate2_mem_levelCoboundaries2
    {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    (r : (Ω ≃ₐ[K] Ω) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (L : IntermediateField K Ω) [Normal K L]
    (hL : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ σ : Ω ≃ₐ[K] Ω, r σ ∈ F.fixingSubgroup → σ ∈ L.fixingSubgroup)
    {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Additive (L)ˣ}
    (hf : f ∈ coboundaries₂ (Rep.ofAlgebraAutOnUnits K L)) :
    unitsInflate₂ L f ∈ levelCoboundaries₂ r (Rep.ofAlgebraAutOnUnits K Ω) := by sorry

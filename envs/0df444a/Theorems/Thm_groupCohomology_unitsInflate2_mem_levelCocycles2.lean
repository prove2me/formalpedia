-- Prove2me | Theorems.Thm_groupCohomology_unitsInflate2_mem_levelCocycles2
-- name    : groupCohomology.unitsInflate2_mem_levelCocycles2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/f217f6df-4197-5dc8-b3b6-c56221b1320c
-- title:
--   Inflation of a 2-cocycle is level-constant
-- statement:
--   Let $K$ and $\Omega$ be fields with $\Omega$ a $K$-algebra, and let $r \colon (\Omega \simeq_{\mathrm{alg}[K]} \Omega) \to \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ be a monoid homomorphism from the group of $K$-algebra automorphisms of $\Omega$ to the automorphism group of `AlgebraicClosure ℚ` over $\mathbb{Q}$ (the "level map"). Let $L$ be an intermediate field of $\Omega/K$ which is normal over $K$, and assume the hypothesis `hL`: there is an intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, such that every $\sigma \in \mathrm{Aut}_K(\Omega)$ with $r\sigma$ in the fixing subgroup of $F$ lies in the fixing subgroup of $L$; equivalently $r^{-1}(\mathrm{Gal}(\overline{\mathbb{Q}}/F)) \subseteq \mathrm{Gal}(\Omega/L)$. Let $f \colon (L \simeq_{\mathrm{alg}[K]} L)^2 \to \mathrm{Additive}\,L^\times$ be an inhomogeneous $2$-cocycle for Mathlib's representation `Rep.ofAlgebraAutOnUnits K L` of $\mathrm{Aut}_K(L)$ on $L^\times$ written additively. The conclusion is that the inflated function $\mathrm{unitsInflate}_2\,L\,f$, given by $(g,h) \mapsto f(g|_L, h|_L)$ composed with the inclusion $L^\times \hookrightarrow \Omega^\times$ induced by $\mathrm{algebraMap}\,L\,\Omega$, is a level cocycle for `Rep.ofAlgebraAutOnUnits K Ω`: it is an inhomogeneous $2$-cocycle of $\mathrm{Aut}_K(\Omega)$ in $\Omega^\times$, and there is a finite subextension $F/\mathbb{Q}$ of $\overline{\mathbb{Q}}$ such that its value at $(g,g')$ is unchanged when $g$ and $g'$ are multiplied on the right by arbitrary elements $s,s'$ with $rs, rs'$ in the fixing subgroup of $F$.
--
--   This is the inflation map from $\mathrm{Gal}(L/K)$ to $\mathrm{Gal}(\Omega/K)$ on inhomogeneous $2$-cochains with unit coefficients, together with the observation that inflation along a subextension cut out by a level subgroup lands in the level-constant ("continuous") cocycles, i.e. in the group whose quotient defines $H^2_{\mathrm{cts}}(\mathrm{Aut}_K(\Omega), \Omega^\times)$. It is used to produce level cocycles from finite-level data, for instance in the construction of witnesses for local invariants of cyclotomic characters and in comparing $H^2$ of the finite layers with the continuous $H^2$ of the full automorphism group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_unitsInflate2_mem_levelCocycles2.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_GaloisUnitsInflation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory groupCohomology

theorem groupCohomology.unitsInflate2_mem_levelCocycles2
    {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    (r : (Ω ≃ₐ[K] Ω) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (L : IntermediateField K Ω) [Normal K L]
    (hL : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ σ : Ω ≃ₐ[K] Ω, r σ ∈ F.fixingSubgroup → σ ∈ L.fixingSubgroup)
    {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Additive (L)ˣ}
    (hf : f ∈ cocycles₂ (Rep.ofAlgebraAutOnUnits K L)) :
    unitsInflate₂ L f ∈ levelCocycles₂ r (Rep.ofAlgebraAutOnUnits K Ω) := by sorry

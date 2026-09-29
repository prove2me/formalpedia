-- Prove2me | Theorems.Thm_groupCohomology_exists_linearMap_H2_continuousH2_ofAlgebraAutOnUnits
-- name    : groupCohomology.exists_linearMap_H2_continuousH2_ofAlgebraAutOnUnits
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/cf216ce0-4fc2-5ac0-b528-c9589ea4d77e
-- title:
--   Inflation into continuous H² as a ℤ-linear map
-- statement:
--   Let $K$ and $\Omega$ be fields with $\Omega$ a $K$-algebra, let $r \colon (\Omega \simeq_{\mathrm{alg}[K]} \Omega) \to (\overline{\mathbb{Q}} \simeq_{\mathrm{alg}[\mathbb{Q}]} \overline{\mathbb{Q}})$ be a group homomorphism from the group of $K$-algebra automorphisms of $\Omega$ to that of `AlgebraicClosure ℚ`, and let $L$ be an intermediate field of $\Omega/K$ which is normal over $K$. Assume the compatibility hypothesis `hL`: there is an intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, such that every $\sigma$ with $r\sigma$ in the fixing subgroup of $F$ lies in the fixing subgroup of $L$. The assertion is the existence of a $\mathbb{Z}$-linear map $\mathrm{inf}$ from Mathlib's $H^2$ of the representation `Rep.ofAlgebraAutOnUnits K L` of $\mathrm{Gal}(L/K)$ on `Additive Lˣ` to `continuousH2 r (Rep.ofAlgebraAutOnUnits K Ω)`, the quotient of the submodule `levelCocycles₂ r` of $2$-cochains by the preimage of `levelCoboundaries₂ r` under its inclusion, with the following property: for every $2$-cocycle $f$ of `Rep.ofAlgebraAutOnUnits K L` and every proof that the inflated cochain `unitsInflate₂ L f` lies in `levelCocycles₂ r (Rep.ofAlgebraAutOnUnits K Ω)`, the map $\mathrm{inf}$ sends the class `H2π … f` to the class of `unitsInflate₂ L f` in `continuousH2`.
--
--   This is the inflation map $H^2(\mathrm{Gal}(L/K), L^\times) \to H^2_{\mathrm{cts}}(\mathrm{Gal}(\Omega/K), \Omega^\times)$, packaged as a single $\mathbb{Z}$-linear map on cohomology classes together with its description on cocycles, the hypothesis `hL` guaranteeing that inflated cochains are constant on a level subgroup. It is used in the construction of splitting fields after adjoining roots of unity in the $p$-adic setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_linearMap_H2_continuousH2_ofAlgebraAutOnUnits.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_GaloisUnitsInflation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory groupCohomology

theorem groupCohomology.exists_linearMap_H2_continuousH2_ofAlgebraAutOnUnits
    {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    (r : (Ω ≃ₐ[K] Ω) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (L : IntermediateField K Ω) [Normal K L]
    (hL : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ σ : Ω ≃ₐ[K] Ω, r σ ∈ F.fixingSubgroup → σ ∈ L.fixingSubgroup) :
    ∃ inf : H2 (Rep.ofAlgebraAutOnUnits K L) →ₗ[ℤ] continuousH2 r (Rep.ofAlgebraAutOnUnits K Ω),
      ∀ (f : cocycles₂ (Rep.ofAlgebraAutOnUnits K L))
        (hf' : unitsInflate₂ L f ∈ levelCocycles₂ r (Rep.ofAlgebraAutOnUnits K Ω)),
        inf (H2π (Rep.ofAlgebraAutOnUnits K L) f) =
          continuousH2π r (Rep.ofAlgebraAutOnUnits K Ω) ⟨unitsInflate₂ L f, hf'⟩ := by sorry

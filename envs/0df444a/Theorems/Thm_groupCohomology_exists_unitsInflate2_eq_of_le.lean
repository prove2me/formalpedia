-- Prove2me | Theorems.Thm_groupCohomology_exists_unitsInflate2_eq_of_le
-- name    : groupCohomology.exists_unitsInflate2_eq_of_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/e6e99c2b-cc00-5819-884f-df91d7d59e5e
-- title:
--   Inflation of unit-valued 2-cocycles along L ⊆ L'
-- statement:
--   Let $K$ and $\Omega$ be fields with $\Omega$ a $K$-algebra, and let $L \le L'$ be intermediate fields of $\Omega/K$, each normal over $K$. Let $f$ be a function on pairs of $K$-algebra automorphisms of $L$, $f : (L \simeq_{\mathrm{alg}[K]} L) \times (L \simeq_{\mathrm{alg}[K]} L) \to \mathrm{Additive}\,L^{\times}$, and assume $f$ lies in `cocycles₂ (Rep.ofAlgebraAutOnUnits K L)`, i.e. $f$ is a $2$-cocycle for the representation `Rep.ofAlgebraAutOnUnits K L` of the automorphism group of $L/K$ on the additively written group $L^{\times}$. The assertion is the existence of a function $f'$ on pairs of $K$-algebra automorphisms of $L'$ with values in $\mathrm{Additive}\,L'^{\times}$ which is a $2$-cocycle for `Rep.ofAlgebraAutOnUnits K L'` and satisfies $\mathtt{unitsInflate₂}\,L'\,f' = \mathtt{unitsInflate₂}\,L\,f$, where `unitsInflate₂ L` denotes the inflation operation carrying a $2$-cochain of the automorphism group of $L/K$ with values in $L^{\times}$ to a $2$-cochain of the automorphism group of $\Omega/K$ with values in $\Omega^{\times}$. The statement is purely existential: no $L$-algebra structure on $L'$ appears in it.
--
--   This is the transitivity of inflation of unit-valued $2$-cocycles along a tower $K \subseteq L \subseteq L' \subseteq \Omega$ of normal levels: a cocycle on $\mathrm{Gal}(L/K)$ and its pullback to $\mathrm{Gal}(L'/K)$ have the same inflation to the automorphism group of $\Omega/K$, so that a class split at level $L$ is split at every larger normal level. It is used in [`groupCohomology.exists_split_adjoin_rootsOfUnity_eq_zmultiples_of_padic`](thm.html#groupCohomology.exists_split_adjoin_rootsOfUnity_eq_zmultiples_of_padic), where the splitting level must be enlarged to contain prescribed roots of unity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_unitsInflate2_eq_of_le.lean

import Mathlib
import Definitions.Def_GroupCohomology_GaloisUnitsInflation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory groupCohomology

theorem groupCohomology.exists_unitsInflate2_eq_of_le
    {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    (L L' : IntermediateField K Ω) [Normal K L] [Normal K L'] (hLL' : L ≤ L')
    (f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Additive (L)ˣ) (hf : f ∈ cocycles₂ (Rep.ofAlgebraAutOnUnits K L)) :
    ∃ f' : (L' ≃ₐ[K] L') × (L' ≃ₐ[K] L') → Additive (L')ˣ,
      f' ∈ cocycles₂ (Rep.ofAlgebraAutOnUnits K L') ∧ unitsInflate₂ L' f' = unitsInflate₂ L f := by sorry

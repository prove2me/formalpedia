-- Prove2me | Theorems.Thm_groupCohomology_nonempty_continuousHSr_linearEquiv_of_iso
-- name    : groupCohomology.nonempty_continuousHSr_linearEquiv_of_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/85781115-0d84-5158-8336-1400ef0582ca
-- title:
--   Isomorphic representations give equivalent S-restricted H¹, H²
-- statement:
--   Fix a prime $p$, a finite set $S$ of rational primes, and an intermediate field $K$ of $\mathbb{Q}$ inside $\mathrm{AlgebraicClosure}\ \mathbb{Q}$, and write $r$ for the inclusion $K.\mathrm{fixingSubgroup} \hookrightarrow \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, i.e. the monoid homomorphism `K.fixingSubgroup.subtype`. Let $A$ and $B$ be representations of the group $K.\mathrm{fixingSubgroup}$ over $\mathbb{Z}/p$, in the sense of objects of `Rep (ZMod p) ↥K.fixingSubgroup` in `Type 0`, and let $e : A \cong B$ be an isomorphism of such representations. The conclusion is the conjunction of two nonemptiness assertions. First, the $\mathbb{Z}/p$-module `continuousH1Sr r S A`, namely the submodule of $H^1(K.\mathrm{fixingSubgroup}, A)$ obtained as the image under the projection `H1π A` of the submodule `levelCocyclesSr₁ r S A` of $1$-cocycles, is linearly equivalent over $\mathbb{Z}/p$ to the corresponding submodule for $B$. Second, the $\mathbb{Z}/p$-module `continuousH2Sr r S A`, namely the quotient of `levelCocyclesSr₂ r S A` by the preimage of `levelCoboundariesSr₂ r S A` under the inclusion of that cocycle submodule, is linearly equivalent over $\mathbb{Z}/p$ to the corresponding quotient for $B$. Both equivalences are asserted only as nonemptiness of the type of linear equivalences, with no compatibility with $e$ recorded.
--
--   This is the functoriality of the $S$-restricted cohomology modules over the base field $K$ in the coefficient representation: isomorphic coefficients give isomorphic $H^1$ and $H^2$, in the restricted form used in the Euler-characteristic bookkeeping. It is used in establishing finite-dimensionality and the dimension formula for the restricted $H^2$ of a coinduced module, [`groupCohomology.finiteDimensional_continuousH2S_coind_and_finrank_eq`](thm.html#groupCohomology.finiteDimensional_continuousH2S_coind_and_finrank_eq), where coefficients may be replaced by an isomorphic copy.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_nonempty_continuousHSr_linearEquiv_of_iso.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation
open scoped Classical

theorem groupCohomology.nonempty_continuousHSr_linearEquiv_of_iso
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    {A B : Rep.{0} (ZMod p) ↥K.fixingSubgroup} (e : A ≅ B) :
    Nonempty (↥(continuousH1Sr K.fixingSubgroup.subtype S A) ≃ₗ[ZMod p] ↥(continuousH1Sr K.fixingSubgroup.subtype S B)) ∧
      Nonempty (continuousH2Sr K.fixingSubgroup.subtype S A ≃ₗ[ZMod p] continuousH2Sr K.fixingSubgroup.subtype S B) := by sorry

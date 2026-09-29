-- Prove2me | Theorems.Thm_groupCohomology_finiteDimensional_and_finrank_continuousH2Sr_twist_add_eq_sClassTorsionP_add_sum_placesRep
-- name    : groupCohomology.finiteDimensional_and_finrank_continuousH2Sr_twist_add_eq_sClassTorsionP_add_sum_placesRep
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/507a4d89-27e6-50d0-a6f2-9462ff389384
-- title:
--   Dimension of H²_S(K,N(1)) via S-class group and places
-- statement:
--   Fix a prime $p$ and a finite set $S$ of primes with $p \in S$. Let $K \subseteq L$ be intermediate fields of $\mathbb{Q}$ in $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, each finite over $\mathbb{Q}$ and unramified outside $S$ in the sense of `IsUnramifiedOutside` (finite-dimensional over $\mathbb{Q}$, and for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ lies in the fixing subgroup of the field). Assume $L$ is normal over $K$ as an intermediate field of $\overline{\mathbb{Q}}/K$, that conjugation by any element of $K$'s fixing subgroup preserves $L$'s fixing subgroup, and that the relative index of $L$'s fixing subgroup in $K$'s fixing subgroup is coprime to $p$. Assume further that $L$ contains a primitive $p$-th root of unity $\zeta$, and, if $p = 2$, an element $i$ with $i^2 = -1$. Let $N$ be a finite-dimensional representation of $\Gamma_K = K$'s fixing subgroup over $\mathbb{Z}/p$ on which every element acting trivially on $L$ acts as the identity. Then the group `continuousH2Sr` of $\Gamma_K$ with $S$-restricted ramification — the quotient of `levelCocyclesSr₂` by the image of `levelCoboundariesSr₂` — with coefficients in the twist $N(1)$ of $N$ by the mod-$p$ cyclotomic character restricted to $\Gamma_K$, is finite-dimensional over $\mathbb{Z}/p$, and its dimension plus $\dim N^{\Gamma_K}$ equals $\dim (\mathrm{Cl}_S(L)[p] \otimes N)^{\Gamma_K}$ — where `sClassTorsionP` is the $p$-torsion of the $S$-class group representation of $L$ over $K$, inflated along $\Gamma_K \to \mathrm{Gal}(L/K)$ — plus the sum over $q \in S$ of $\dim(\,\mathbb{Z}/p[\text{places of } L \text{ above } q] \otimes N)^{\Gamma_K}$, the first factor being `placesRep` at the index `Sum.inr q`, the finitely supported $\mathbb{Z}/p$-valued functions on those places with the permutation action of $\Gamma_K$.
--
--   This is the global class field theory input of the mod-$p$ Tate formula over the $S$-integers: the exact sequence relating $\mathrm{Br}(\mathcal{O}_{L,S})$, the $S$-class group and the local invariants at the places in $S$, read off as a dimension count for $H^2_S$ with coefficients in $N(1)$. It is combined with Kummer theory and a unit theorem to yield the corresponding formula for $H^1_S(K, N(1))$, and is cited in that form by [`groupCohomology.finiteDimensional_and_finrank_continuousH1Sr_twist_cycloChar_eq_of_trivial`](thm.html#groupCohomology.finiteDimensional_and_finrank_continuousH1Sr_twist_cycloChar_eq_of_trivial).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_finiteDimensional_and_finrank_continuousH2Sr_twist_add_eq_sClassTorsionP_add_sum_placesRep.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith
open scoped Classical NumberField.LevelArith

theorem groupCohomology.finiteDimensional_and_finrank_continuousH2Sr_twist_add_eq_sClassTorsionP_add_sum_placesRep
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hK : K.IsUnramifiedOutside S) (hL : L.IsUnramifiedOutside S)
    [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L]
    (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)]
    (hnorm : ∀ g ∈ K.fixingSubgroup, ∀ s ∈ L.fixingSubgroup, g * s * g⁻¹ ∈ L.fixingSubgroup)
    (hcop : (L.fixingSubgroup.relIndex K.fixingSubgroup).Coprime p)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) (hζL : ζ ∈ L)
    (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1)
    (N : Rep.{0} (ZMod p) ↥K.fixingSubgroup) [FiniteDimensional (ZMod p) N]
    (htriv : ∀ s : ↥K.fixingSubgroup, (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ L.fixingSubgroup → N.ρ s = 1) :
    FiniteDimensional (ZMod p)
        (continuousH2Sr K.fixingSubgroup.subtype S (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype))) ∧
      Module.finrank (ZMod p)
          (continuousH2Sr K.fixingSubgroup.subtype S (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype))) +
        Module.finrank (ZMod p) N.ρ.invariants =
        Module.finrank (ZMod p) (sClassTorsionP K L hKL S p ⊗ N : Rep.{0} (ZMod p) ↥K.fixingSubgroup).ρ.invariants +
        ∑ q : ↥S, Module.finrank (ZMod p)
          (placesRep K L hnorm S (Sum.inr q) p ⊗ N : Rep.{0} (ZMod p) ↥K.fixingSubgroup).ρ.invariants := by sorry

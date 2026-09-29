-- Prove2me | Theorems.Thm_groupCohomology_finiteDimensional_and_finrank_continuousH1Sr_twist_eq_unitsModP_add_sClassTorsionP
-- name    : groupCohomology.finiteDimensional_and_finrank_continuousH1Sr_twist_eq_unitsModP_add_sClassTorsionP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/c25fa1c8-e076-59b6-aacc-5fa60c0850c3
-- title:
--   Kummer rank formula for H¹_S(K, N(1))
-- statement:
--   Fix a prime $p$, a finite set $S$ of rational primes with $p \in S$, and two intermediate fields $K \subseteq L$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, both finite over $\mathbb{Q}$ and both unramified outside $S$ in the sense that, for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ lies in the fixing subgroup of the field. Assume $\overline{\mathbb{Q}}$-level data: $L$'s fixing subgroup is normalised by $K$'s, the relative index of $L$'s fixing subgroup in $K$'s is coprime to $p$, $L$ is normal over $K$ as an extension of $K$ inside $\overline{\mathbb{Q}}$, and $L$ contains a primitive $p$-th root of unity $\zeta$. Let $N$ be a finite-dimensional $\mathbb{Z}/p$-representation of $K$'s fixing subgroup which is trivial on those elements lying in $L$'s fixing subgroup. Then the submodule $\mathtt{continuousH1Sr}$ of $H^1$ of the twist of $N$ by the mod-$p$ cyclotomic character (the image under $H^1\pi$ of the $S$-level cocycles) is finite-dimensional over $\mathbb{Z}/p$, and its rank equals the dimension of the invariants of $(\mathcal{O}_{L,S}^\times/p) \otimes N$ plus the dimension of the invariants of $\mathrm{Cl}_S(L)[p] \otimes N$, where both arithmetic modules are formed for $L/K$ with the places of $K$ above $S$ and inflated along the level Galois map.
--
--   This is the Kummer-theoretic input to the field-level Tate formula: it computes the $S$-ramified first cohomology with coefficients in the cyclotomic twist $N(1)$ in terms of $S$-units modulo $p$ and the $p$-torsion of the $S$-class group of the splitting level $L$. It feeds the statement [`groupCohomology.finiteDimensional_and_finrank_continuousH1Sr_twist_cycloChar_eq_of_trivial`](thm.html#groupCohomology.finiteDimensional_and_finrank_continuousH1Sr_twist_cycloChar_eq_of_trivial).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_finiteDimensional_and_finrank_continuousH1Sr_twist_eq_unitsModP_add_sClassTorsionP.lean

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

theorem groupCohomology.finiteDimensional_and_finrank_continuousH1Sr_twist_eq_unitsModP_add_sClassTorsionP
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hK : K.IsUnramifiedOutside S) (hL : L.IsUnramifiedOutside S)
    [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L]
    (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)]
    (hnorm : ∀ g ∈ K.fixingSubgroup, ∀ s ∈ L.fixingSubgroup, g * s * g⁻¹ ∈ L.fixingSubgroup)
    (hcop : (L.fixingSubgroup.relIndex K.fixingSubgroup).Coprime p)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) (hζL : ζ ∈ L)
    (N : Rep.{0} (ZMod p) ↥K.fixingSubgroup) [FiniteDimensional (ZMod p) N]
    (htriv : ∀ s : ↥K.fixingSubgroup, (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ L.fixingSubgroup → N.ρ s = 1) :
    FiniteDimensional (ZMod p)
        ↥(continuousH1Sr K.fixingSubgroup.subtype S (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype))) ∧
      Module.finrank (ZMod p)
          ↥(continuousH1Sr K.fixingSubgroup.subtype S (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype))) =
        Module.finrank (ZMod p) (unitsModP K L hKL S p ⊗ N : Rep.{0} (ZMod p) ↥K.fixingSubgroup).ρ.invariants +
        Module.finrank (ZMod p) (sClassTorsionP K L hKL S p ⊗ N : Rep.{0} (ZMod p) ↥K.fixingSubgroup).ρ.invariants := by sorry

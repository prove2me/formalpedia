-- Prove2me | Theorems.Thm_groupCohomology_exists_isLevelConstant_d_two_three_eq_of_pPow_smul_sUnitsMax
-- name    : groupCohomology.exists_isLevelConstant_d_two_three_eq_of_pPow_smul_sUnitsMax
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/47fdc913-11ba-58d3-99bf-d99e8a41b641
-- title:
--   p-power-torsion level-constant 3-cocycles on S-units are coboundaries
-- statement:
--   Fix a prime $p$ and a finite set $S$ of primes containing $p$ (as `pPrime p ∈ S`), and an intermediate field $L$ of $\mathbb{Q}$ in $\operatorname{AlgebraicClosure}\mathbb{Q}$ which is finite over $\mathbb{Q}$ and unramified outside $S$, in the sense that $L$ is finite-dimensional over $\mathbb{Q}$ and for every prime $q \notin S$ and every valuation subring $A$ of $\operatorname{AlgebraicClosure}\mathbb{Q}$ with $q$ a non-unit of $A$, the image in $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ over $\mathbb{Q}$ lies in `L.fixingSubgroup`; assume moreover that if $p = 2$ then $L$ contains an element $i$ with $i^2 = -1$. Write $\Gamma_L =$ `L.fixingSubgroup` and let $M =$ `sUnitsMaxRep S L` be the $\mathbb{Z}[\Gamma_L]$-module obtained from the $\Gamma_L$-stable subgroup `sUnitsMaxStable S L` of $(\operatorname{AlgebraicClosure}\mathbb{Q})^\times$, written additively, with $\Gamma_L$ acting through the unit action. Call a function on $\Gamma_L^n$ with values in $M$ level-constant if there is an intermediate field $F$, unramified outside $S$ in the above sense, such that the value at $g \cdot s$ equals the value at $g$ whenever every coordinate $s_i$ lies in `F.fixingSubgroup`. Let $u \colon \Gamma_L^3 \to M$ be level-constant with $d^{3,4} u = 0$ in Mathlib's inhomogeneous cochain complex of $M$, and suppose there exist $k \in \mathbb{N}$ and a level-constant $w_0 \colon \Gamma_L^2 \to M$ with $d^{2,3} w_0 = p^k \cdot u$. Then there exists a level-constant $w \colon \Gamma_L^2 \to M$ with $d^{2,3} w = u$.
--
--   This is the cochain-level form of the vanishing of the $p$-primary part of $H^3(G_{L,S}, E_S)$ for the $S$-units of the maximal extension of $L$ unramified outside $S$, phrased directly in terms of inhomogeneous cochains and of cochains that are constant along the fixing subgroup of some finite level, so that no degree-three cohomology object need be introduced. It feeds [`groupCohomology.exists_isLevelConstant_d_two_three_eq_trivial_of_cycloChar_eq_one`](thm.html#groupCohomology.exists_isLevelConstant_d_two_three_eq_trivial_of_cycloChar_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_isLevelConstant_d_two_three_eq_of_pPow_smul_sUnitsMax.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import Definitions.Def_NumberField_SUnitsMax

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module Limits groupCohomology ExtCitation NumberField.LevelArith
open scoped Classical NumberField.LevelArith TensorProduct Pointwise

theorem groupCohomology.exists_isLevelConstant_d_two_three_eq_of_pPow_smul_sUnitsMax
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L]
    (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1)
    (u : (Fin 3 → ↥L.fixingSubgroup) → sUnitsMaxRep S L)
    (hlc : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
      ∀ g s : Fin 3 → ↥L.fixingSubgroup,
        (∀ i, ((s i : ↥L.fixingSubgroup) : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∈ F.fixingSubgroup) → u (g * s) = u g)
    (hcoc : ((inhomogeneousCochains (sUnitsMaxRep S L)).d 3 4).hom u = 0)
    (htor : ∃ (k : ℕ) (w₀ : (Fin 2 → ↥L.fixingSubgroup) → sUnitsMaxRep S L),
      (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
        ∀ g s : Fin 2 → ↥L.fixingSubgroup,
          (∀ i, ((s i : ↥L.fixingSubgroup) : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∈ F.fixingSubgroup) → w₀ (g * s) = w₀ g) ∧
      ((inhomogeneousCochains (sUnitsMaxRep S L)).d 2 3).hom w₀ = (p ^ k : ℤ) • u) :
    ∃ w : (Fin 2 → ↥L.fixingSubgroup) → sUnitsMaxRep S L,
      (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
        ∀ g s : Fin 2 → ↥L.fixingSubgroup,
          (∀ i, ((s i : ↥L.fixingSubgroup) : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∈ F.fixingSubgroup) → w (g * s) = w g) ∧
      ((inhomogeneousCochains (sUnitsMaxRep S L)).d 2 3).hom w = u := by sorry

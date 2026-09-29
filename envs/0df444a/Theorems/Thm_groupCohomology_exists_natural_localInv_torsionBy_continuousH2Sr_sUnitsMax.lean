-- Prove2me | Theorems.Thm_groupCohomology_exists_natural_localInv_torsionBy_continuousH2Sr_sUnitsMax
-- name    : groupCohomology.exists_natural_localInv_torsionBy_continuousH2Sr_sUnitsMax
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/28dbeb32-da4a-59ae-9238-c8f4a8de205f
-- title:
--   Local invariants on p-torsion of H²_S, with naturality
-- statement:
--   Let $p$ be a prime, let $S$ be a finite set of rational primes containing $p$, and let $L$ be an intermediate field of $\overline{\mathbb{Q}}/\mathbb{Q}$ that is finite over $\mathbb{Q}$ and satisfies `IsUnramifiedOutside S`: for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ lies in the fixing subgroup of $L$; assume moreover that if $p = 2$ then $L$ contains an element $i$ with $i^2 = -1$. Write $H :=$ `continuousH2Sr` for the inclusion $\mathrm{Gal}(\overline{\mathbb{Q}}/L) =$ `L.fixingSubgroup` $\hookrightarrow \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, the set $S$ and the coefficient module `sUnitsMaxRep S L` (the additive group of the Galois-stable subgroup `sUnitsMaxStable S L` of $\overline{\mathbb{Q}}^{\times}$), i.e. the quotient of `levelCocyclesSr₂` by the coboundaries lying in it. Then there is a $\mathbb{Z}/p$-linear map $\mathrm{inv}$ from the $p$-torsion $\{a \in H : pa = 0\}$ to the functions on `placesOverPrimes` $L\,S$ — the height-one primes $w$ of $\mathcal{O}_L$ containing some $q \in S$ — with values in $\mathbb{Z}/p$, such that: $\mathrm{inv}$ is injective; a function $f$ lies in its range exactly when $\sum^{f}_{w} f(w) = 0$; and $\mathrm{inv}$ is natural for the Galois action, in the following action-free form. For $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ and $\tau \in \mathrm{Aut}_{\mathbb{Q}}(L)$ with $\sigma|_L = \tau$, for $p$-torsion classes $a, a'$ represented by cocycles $w, w'$ under the projection `continuousH2Srπ`, if $w'(s,t) = \sigma \cdot w(s',t')$ in $\overline{\mathbb{Q}}^{\times}$ whenever $\sigma^{-1} s \sigma = s'$ and $\sigma^{-1} t \sigma = t'$ in `L.fixingSubgroup`, then for places $v, v'$ in the above set with $v'(\tau y) = v(y)$ for all $y \in L$ one has $\mathrm{inv}(a')(v') = \mathrm{inv}(a)(v)$.
--
--   This is the class-field-theoretic input on the $H^2$ side: the local-invariant description (Hasse principle, reciprocity and realisation of sum-zero families, together with Galois naturality of the invariants) of the $p$-torsion of the $S$-level second cohomology of the $S$-units of the maximal $S$-ramified extension, in its mod $p$ form with $\mathbb{Z}/p$ coefficients; it is obtained from the $p$-primary version with values in $\mathbb{Q}/\mathbb{Z}$. It feeds the construction of the Kummer–Brauer comparison maps over cyclotomic $S$-levels and the bound on the number of places in terms of the order of this $p$-torsion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_natural_localInv_torsionBy_continuousH2Sr_sUnitsMax.lean

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

theorem groupCohomology.exists_natural_localInv_torsionBy_continuousH2Sr_sUnitsMax
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L]
    (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1) :
    ∃ inv : ↥(Submodule.torsionBy ℤ (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (p : ℤ)) →ₗ[ZMod p] (↥(placesOverPrimes ↥L (S : Set Nat.Primes)) → ZMod p),
      Function.Injective inv ∧ (∀ f, f ∈ LinearMap.range inv ↔ ∑ᶠ w, f w = 0) ∧
      ∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (τ : ↥L ≃ₐ[ℚ] ↥L), (∀ y : ↥L, σ (y : AlgebraicClosure ℚ) = ((τ y : ↥L) : AlgebraicClosure ℚ)) →
        ∀ (a a' : ↥(Submodule.torsionBy ℤ (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (p : ℤ))) (w w' : ↥(levelCocyclesSr₂ L.fixingSubgroup.subtype S (sUnitsMaxRep S L))),
          (a : (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L))) = continuousH2Srπ L.fixingSubgroup.subtype S _ w → (a' : (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L))) = continuousH2Srπ L.fixingSubgroup.subtype S _ w' →
          (∀ s t s' t' : ↥L.fixingSubgroup, σ⁻¹ * (s : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * σ = s' → σ⁻¹ * (t : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * σ = t' →
            sUnitsMaxRep.val S L ((w' : ↥L.fixingSubgroup × ↥L.fixingSubgroup → (sUnitsMaxRep S L)) (s, t)) =
              σ • sUnitsMaxRep.val S L ((w : ↥L.fixingSubgroup × ↥L.fixingSubgroup → (sUnitsMaxRep S L)) (s', t'))) →
          ∀ (v v' : ↥(placesOverPrimes ↥L (S : Set Nat.Primes))), (∀ y : ↥L, (v'.1).valuation ↥L (τ y) = (v.1).valuation ↥L y) →
            inv a' v' = inv a v := by sorry

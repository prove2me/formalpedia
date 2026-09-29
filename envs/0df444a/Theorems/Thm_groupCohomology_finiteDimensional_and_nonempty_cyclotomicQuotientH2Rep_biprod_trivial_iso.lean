-- Prove2me | Theorems.Thm_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso
-- name    : groupCohomology.finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/70ea232e-77ad-5171-ba0f-1a9cd546eda2
-- title:
--   Equivariant splitting of S-ramified H² with μₚ coefficients
-- statement:
--   Let $p$ be a prime and $S$ a finite set of rational primes with $p \in S$. Let $K \subseteq L$ be intermediate fields of $\mathbb{Q}$ in $\mathrm{AlgebraicClosure}\ \mathbb{Q}$, both finite over $\mathbb{Q}$ and both unramified outside $S$ in the sense of `IsUnramifiedOutside`: finite-dimensional over $\mathbb{Q}$, and for every prime $q \notin S$ and every valuation subring $A$ of the algebraic closure in whose nonunits $q$ lies, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ over $\mathbb{Q}$ is contained in the fixing subgroup of the field. Assume $K$ is normal in $L$ viewed as an intermediate field over $K$ (`levelField K L hKL`), that $\Gamma_L =$ `L.fixingSubgroup` is normal inside $\Gamma_K =$ `K.fixingSubgroup`, both as a subgroup-of instance and in the pointwise form $g s g^{-1} \in \Gamma_L$ for $g \in \Gamma_K$, $s \in \Gamma_L$, and that the relative index of $\Gamma_L$ in $\Gamma_K$ is coprime to $p$. Assume further that a primitive $p$-th root of unity $\zeta$ lies in $L$, and, if $p = 2$, that $L$ contains a square root of $-1$. Then the $\mathbb{Z}/p$-representation `cyclotomicQuotientH2Rep S K L p` of $\Gamma_K$ — the object carrying the second $S$-ramified cohomology with $\mu_p$-coefficients — is finite-dimensional over $\mathbb{Z}/p$, and its biproduct with the trivial representation $\mathbb{Z}/p$ is isomorphic, in $\mathrm{Rep}_{\mathbb{Z}/p}(\Gamma_K)$, to the biproduct of `sClassTorsionP K L hKL S p` — the $p$-torsion of the $S$-class group representation of the extension $K \subseteq$ `levelField K L hKL` (the class group modulo the classes of primes above $S$), inflated along `levelGal K L hKL` to $\Gamma_K$ — with the categorical product over $q \in S$ of the permutation representations `placesRep K L hnorm S (Sum.inr q) p`, each the free $\mathbb{Z}/p$-module on the finitely supported functions on `placesAbove L S (Sum.inr q)` (the places of $L$ above $q$, as an orbit quotient for $\Gamma_L$) with $\Gamma_K$ permuting the basis through `orbitQuotientAction`.
--
--   This is the Kummer-theoretic and class-field-theoretic computation of $H^2$ of the $S$-ramified Galois group of $L$ with $\mu_p$-coefficients, in $\mathrm{Gal}(L/K)$-equivariant form: the $\mu_p$-cohomology plus a trivial line splits off the $p$-torsion of the $S$-class group and a permutation module on the places above $S$, the splitting being available because the relative index is prime to $p$. It feeds the corresponding dimension count for the twisted $H^2$ in terms of the $S$-class group and the place modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import Definitions.Def_Rep_QuotientRightTranslation
import Definitions.Def_GroupCohomology_CyclotomicQuotientH2Rep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module Limits groupCohomology ExtCitation NumberField.LevelArith
open scoped Classical NumberField.LevelArith TensorProduct

theorem groupCohomology.finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hK : K.IsUnramifiedOutside S) (hL : L.IsUnramifiedOutside S)
    [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L]
    (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)] [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).Normal]
    (hnorm : ∀ g ∈ K.fixingSubgroup, ∀ s ∈ L.fixingSubgroup, g * s * g⁻¹ ∈ L.fixingSubgroup)
    (hcop : (L.fixingSubgroup.relIndex K.fixingSubgroup).Coprime p)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) (hζL : ζ ∈ L)
    (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1) :
    FiniteDimensional (ZMod p) (cyclotomicQuotientH2Rep S K L p) ∧
      Nonempty ((cyclotomicQuotientH2Rep S K L p ⊞ Rep.trivial (ZMod p) ↥K.fixingSubgroup (ZMod p) : Rep.{0} (ZMod p) ↥K.fixingSubgroup) ≅
        sClassTorsionP K L hKL S p ⊞ ∏ᶜ fun q : ↥S => placesRep K L hnorm S (Sum.inr q) p) := by sorry

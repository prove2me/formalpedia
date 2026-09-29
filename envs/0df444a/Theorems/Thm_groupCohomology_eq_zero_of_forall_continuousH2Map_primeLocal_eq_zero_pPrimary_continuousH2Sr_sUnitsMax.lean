-- Prove2me | Theorems.Thm_groupCohomology_eq_zero_of_forall_continuousH2Map_primeLocal_eq_zero_pPrimary_continuousH2Sr_sUnitsMax
-- name    : groupCohomology.eq_zero_of_forall_continuousH2Map_primeLocal_eq_zero_pPrimary_continuousH2Sr_sUnitsMax
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/bb78c622-76cf-5fa1-a19d-c0f26e23f1b7
-- title:
--   Hasse principle for the p-primary part of H² of S-units
-- statement:
--   Fix a prime $p$ and a finite set $S$ of rational primes containing $p$ (as the element `pPrime p` of `Nat.Primes`), and let $L$ be an intermediate field of $\overline{\mathbb{Q}}/\mathbb{Q}$ that is finite over $\mathbb{Q}$ and satisfies `L.IsUnramifiedOutside S`, i.e. $L$ is finite over $\mathbb{Q}$ and for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ over $\mathbb{Q}$ lies in the fixing subgroup $\Gamma_L =$ `L.fixingSubgroup`; if $p = 2$ it is assumed that some $i \in L$ has $i^2 = -1$. Coefficients are `sUnitsMaxRep S L`, the $\mathbb{Z}[\Gamma_L]$-module obtained from the $\Gamma_L$-stable subgroup `sUnitsMaxStable S L` of $\overline{\mathbb{Q}}^\times$ written additively, with the Galois action. Let $a$ be a class in `continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)`, the quotient of the module of $S$-level 2-cocycles `levelCocyclesSr₂` for the inclusion $\Gamma_L \hookrightarrow \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ by the preimage of `levelCoboundariesSr₂`, and assume $a$ is $p$-primary, i.e. annihilated by some power of $p$ (membership in `Submodule.torsion'` for the powers of $(p : \mathbb{Z})$). Assume further that $a$ dies locally everywhere above $S$: for every $q \in S$ and every $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, write $\psi_{q,\sigma}$ for the homomorphism $\mathrm{Gal}(\overline{\mathbb{Q}}_q/\mathbb{Q}_q) \to \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ given by `primeLocalToGlobal q` (restriction of scalars to $\mathbb{Q}$ followed by `AlgEquiv.restrictNormalHom`) followed by conjugation by $\sigma$, and let $H_{q,\sigma} = \psi_{q,\sigma}^{-1}(\Gamma_L)$; then the image of $a$ in `continuousH2` under `continuousH2SrToContinuousH2`, pulled back along $H_{q,\sigma} \to \Gamma_L$ with the identity on coefficients by `continuousH2Map`, is required to vanish in the continuous $H^2$ of $H_{q,\sigma}$ (taken with respect to $\psi_{q,\sigma}$ on $H_{q,\sigma}$) with coefficients `sUnitsMaxRep S L` restricted to $H_{q,\sigma}$. The conclusion is $a = 0$.
--
--   This is the Hasse principle, or local–global injectivity, for the $p$-primary part of $H^2(G_{L,S}, E_S)$, here realised with the genuine restriction maps to the decomposition groups at the places of $L$ above $S$ rather than with abstract local invariant maps. It is used in [`groupCohomology.continuousH2Sr_galoisSUnitsRep_eq_zero_of_forall_res_extArithIndex_eq_zero`](thm.html#groupCohomology.continuousH2Sr_galoisSUnitsRep_eq_zero_of_forall_res_extArithIndex_eq_zero), on the route to the cohomological vanishing statements needed for the deformation-theoretic part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_eq_zero_of_forall_continuousH2Map_primeLocal_eq_zero_pPrimary_continuousH2Sr_sUnitsMax.lean

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

theorem groupCohomology.eq_zero_of_forall_continuousH2Map_primeLocal_eq_zero_pPrimary_continuousH2Sr_sUnitsMax
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L]
    (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1)
    (a : continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L))
    (ha : a ∈ Submodule.torsion' ℤ (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (Submonoid.powers (p : ℤ)))
    (hloc : ∀ (q : ↥S) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      continuousH2Map
          (rH := L.fixingSubgroup.subtype)
          (rG := (((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal (q : Nat.Primes))).comp
                    (L.fixingSubgroup.comap ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal (q : Nat.Primes)))).subtype))
          (((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal (q : Nat.Primes))).subgroupComap L.fixingSubgroup)
          (fun _ => rfl)
          (A := sUnitsMaxRep S L)
          (B := Rep.res (((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal (q : Nat.Primes))).subgroupComap L.fixingSubgroup) (sUnitsMaxRep S L))
          LinearMap.id (fun _ _ => rfl)
        (continuousH2SrToContinuousH2 L.fixingSubgroup.subtype S (sUnitsMaxRep S L) a) = 0) :
    a = 0 := by sorry

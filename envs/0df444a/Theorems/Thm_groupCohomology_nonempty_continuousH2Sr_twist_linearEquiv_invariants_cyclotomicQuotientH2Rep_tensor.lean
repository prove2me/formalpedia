-- Prove2me | Theorems.Thm_groupCohomology_nonempty_continuousH2Sr_twist_linearEquiv_invariants_cyclotomicQuotientH2Rep_tensor
-- name    : groupCohomology.nonempty_continuousH2Sr_twist_linearEquiv_invariants_cyclotomicQuotientH2Rep_tensor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/15009018-2c08-50e8-a9f7-49387fb6d1d0
-- title:
--   H²_S with cyclotomic twist as tensor invariants
-- statement:
--   Fix a prime $p$ and a finite set $S$ of rational primes, and let $K, L$ be intermediate fields of $\mathbb{Q}$ in $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, with fixing subgroups $\Gamma_K =$ `K.fixingSubgroup` and $\Gamma_L =$ `L.fixingSubgroup` inside $\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$. Assume that $\Gamma_L \cap \Gamma_K$, viewed as a subgroup of $\Gamma_K$, is normal and of finite index, and that its relative index in $\Gamma_K$ is coprime to $p$. Let $N$ be a representation of $\Gamma_K$ on a finite-dimensional $\mathbb{Z}/p$-vector space such that $N.\rho(s) = 1$ for every $s \in \Gamma_K$ whose underlying automorphism lies in $\Gamma_L$. The assertion is that the type of $\mathbb{Z}/p$-linear isomorphisms between two spaces is nonempty, i.e. that such an isomorphism exists: on one side, `continuousH2Sr` for the inclusion $\Gamma_K \hookrightarrow (\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}})$, the set $S$, and the coefficient module $N$ twisted by the mod $p$ cyclotomic character `cycloChar p` restricted to $\Gamma_K$ (the twist of a representation $\rho$ by a character $\chi$ sending $g$ to $\chi(g) \cdot \rho(g)$), this being by definition the quotient of `levelCocyclesSr₂` by the part of `levelCoboundariesSr₂` contained in it; on the other side, the $\Gamma_K$-invariants of the tensor product representation `cyclotomicQuotientH2Rep S K L p` $\otimes\, N$ in `Rep (ZMod p) ↥K.fixingSubgroup`.
--
--   This is the untwisting step on the $H^2$ side: degree-two $S$-level continuous cohomology of $\Gamma_K$ with coefficients in a cyclotomically twisted finite $\mathbb{Z}/p$-representation that is trivial on $\Gamma_L$ is recovered from the fixed representation `cyclotomicQuotientH2Rep S K L p` by tensoring with $N$ and taking invariants, the coprimality hypothesis making an averaging argument available. It feeds the subsequent computation of the dimension of this $H^2$ in terms of $p$-torsion in the $S$-class group and local contributions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_nonempty_continuousH2Sr_twist_linearEquiv_invariants_cyclotomicQuotientH2Rep_tensor.lean

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

theorem groupCohomology.nonempty_continuousH2Sr_twist_linearEquiv_invariants_cyclotomicQuotientH2Rep_tensor
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ))
    [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).Normal] [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).FiniteIndex]
    (hcop : (L.fixingSubgroup.relIndex K.fixingSubgroup).Coprime p)
    (N : Rep.{0} (ZMod p) ↥K.fixingSubgroup) [FiniteDimensional (ZMod p) N]
    (htriv : ∀ s : ↥K.fixingSubgroup, (s : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∈ L.fixingSubgroup → N.ρ s = 1) :
    Nonempty (continuousH2Sr K.fixingSubgroup.subtype S (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype)) ≃ₗ[ZMod p]
      (cyclotomicQuotientH2Rep S K L p ⊗ N : Rep.{0} (ZMod p) ↥K.fixingSubgroup).ρ.invariants) := by sorry

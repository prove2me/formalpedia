-- Prove2me | Theorems.Thm_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_pin
-- name    : groupCohomology.exists_continuousH2Sr_cyclotomicQuotientRep_equiv_pin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/8fbaf5f4-4eab-551e-bf7d-eb1b147247c6
-- title:
--   Pinned relative Shapiro isomorphism in degree two
-- statement:
--   Fix a prime $p$ and a finite set $S$ of rational primes, and let $K \le L$ be intermediate fields of $\mathbb{Q}$ in $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, with $L$ unramified outside $S$ in the sense of `IsUnramifiedOutside`: $L/\mathbb{Q}$ is finite and, for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ having $q$ among its nonunits, the inertia subgroup of $A$ over $\mathbb{Q}$ lies in $\Gamma_L := L^{\mathrm{fix}}$. Assume moreover that $\Lambda := \Gamma_L \cap \Gamma_K$, viewed as a subgroup of $\Gamma_K$, is normal and of finite index. Write $P(1)$ for the representation of $\Gamma_K$ on $\mathrm{Finsupp}(\Gamma_K/\Lambda, \mathbb{Z}/p)$ by left translation, twisted by the mod $p$ cyclotomic character `cycloChar p` restricted to $\Gamma_K$, and $\mu$ for the trivial $\Gamma_L$-module $\mathbb{Z}/p$ twisted by `cycloChar p` on $\Gamma_L$. The assertion is the existence of a $\mathbb{Z}/p$-linear equivalence $\Theta$ from `continuousH2Sr` of $P(1)$ over $\Gamma_K$ (degree-two $S$-level cocycles modulo the $S$-level coboundaries lying in them) to `continuousH2Sr` of $\mu$ over $\Gamma_L$, subject to two pinnings. First, for $S$-level $2$-cocycles $z$ (for $\Gamma_K$) and $w$ (for $\Gamma_L$): if for all $s,t \in \Gamma_L$, regarded in $\Gamma_K$ via $K \le L$, $w(s,t)$ is the coefficient of $z(s,t)$ at the identity coset of $\Gamma_K/\Lambda$, then $\Theta$ sends the class of $z$ to the class of $w$. Second, for $\sigma \in \Gamma_K$, a class $a$ with $\Theta a$ the class of $w$, and a cocycle $w'$ such that $w'(s,t) = \mathrm{cycloChar}_p(\sigma)\, w(s',t')$ whenever $\sigma^{-1} s \sigma = s'$ and $\sigma^{-1} t \sigma = t'$ in the ambient Galois group, the image of $a$ under the map induced by the right-translation endomorphism `cyclotomicQuotientRT K L p σ` of $P(1)$ (right multiplication by the inverse of the coset of $\sigma$ on $\Gamma_K/\Lambda$, compatible with the twist) is the class of $w'$.
--
--   This is the relative Shapiro (induction–restriction) comparison in degree two for the twisted permutation module $\mathbb{F}_p[\Gamma_K/\Lambda](1)$ against $\mathbb{F}_p(1)$ over $\Gamma_L$, in a form pinned on cocycles so that both the value of $\Theta$ and its interaction with right translation by $\sigma$ — conjugation $w \mapsto \chi(\sigma) w(\sigma^{-1} \cdot \sigma, \sigma^{-1} \cdot \sigma)$ on the target — are specified explicitly. It feeds the finite-dimensionality and nonemptiness statement for the cyclotomic quotient $H^2$ representation, where the equivariance pinning is what identifies the $\Gamma_K$-action on $H^2_S(L, \mu_p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_pin.lean

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
open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation

theorem groupCohomology.exists_continuousH2Sr_cyclotomicQuotientRep_equiv_pin
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L) (hL : L.IsUnramifiedOutside S)
    [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).Normal] [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).FiniteIndex] :
    ∃ Θ : continuousH2Sr K.fixingSubgroup.subtype S (cyclotomicQuotientRep K L p) ≃ₗ[ZMod p]
        continuousH2Sr L.fixingSubgroup.subtype S
          ((Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).twist ((cycloChar p).comp L.fixingSubgroup.subtype)),
      (∀ (z : ↥(levelCocyclesSr₂ K.fixingSubgroup.subtype S (cyclotomicQuotientRep K L p)))
          (w : ↥(levelCocyclesSr₂ L.fixingSubgroup.subtype S
            ((Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).twist ((cycloChar p).comp L.fixingSubgroup.subtype)))),
        (∀ s t : ↥L.fixingSubgroup,
            (w : ↥L.fixingSubgroup × ↥L.fixingSubgroup → ZMod p) (s, t) =
              ((z : ↥K.fixingSubgroup × ↥K.fixingSubgroup → (↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup) →₀ ZMod p)
                (⟨(s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), IntermediateField.fixingSubgroup_antitone hKL s.2⟩,
                 ⟨(t : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), IntermediateField.fixingSubgroup_antitone hKL t.2⟩))
                (1 : ↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup)) →
          Θ (continuousH2Srπ K.fixingSubgroup.subtype S _ z) = continuousH2Srπ L.fixingSubgroup.subtype S _ w) ∧
      ∀ (σ : ↥K.fixingSubgroup) (a : continuousH2Sr K.fixingSubgroup.subtype S (cyclotomicQuotientRep K L p))
        (w w' : ↥(levelCocyclesSr₂ L.fixingSubgroup.subtype S
          ((Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).twist ((cycloChar p).comp L.fixingSubgroup.subtype)))),
        Θ a = continuousH2Srπ L.fixingSubgroup.subtype S _ w →
        (∀ s t s' t' : ↥L.fixingSubgroup,
            ((σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))⁻¹ * s * σ = s' →
            ((σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))⁻¹ * t * σ = t' →
              (w' : ↥L.fixingSubgroup × ↥L.fixingSubgroup → ZMod p) (s, t) =
                ((cycloChar p (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : (ZMod p)ˣ) : ZMod p) *
                  (w : ↥L.fixingSubgroup × ↥L.fixingSubgroup → ZMod p) (s', t')) →
          Θ (continuousH2SrMapHom S K.fixingSubgroup.subtype (cyclotomicQuotientRT K L p σ) a) =
            continuousH2Srπ L.fixingSubgroup.subtype S _ w' := by sorry

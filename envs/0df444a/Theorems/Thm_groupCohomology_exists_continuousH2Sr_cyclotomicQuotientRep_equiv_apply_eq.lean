-- Prove2me | Theorems.Thm_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_apply_eq
-- name    : groupCohomology.exists_continuousH2Sr_cyclotomicQuotientRep_equiv_apply_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/196be0e5-4e27-57ce-8ef8-9207641eb096
-- title:
--   Pinned degree-two Shapiro isomorphism for ℤ/p(1)
-- statement:
--   Fix a prime $p$, a finite set $S$ of rational primes, and intermediate fields $K \le L$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, with $L$ unramified outside $S$ in the sense of [`IntermediateField.IsUnramifiedOutside`](def/GroupCohomology_ContinuousUnramified.html#L16): $L/\mathbb{Q}$ is finite and for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ lies in $\Gamma_L := L.\mathrm{fixingSubgroup}$. Assume moreover that $\Lambda$, the subgroup $\Gamma_L$ regarded inside $\Gamma_K$, is normal and of finite index. The assertion is the existence of a $\mathbb{Z}/p$-linear isomorphism $\Theta$ from `continuousH2Sr` for $\Gamma_K$ (the level map being the inclusion $\Gamma_K \hookrightarrow \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$), $S$ and the coefficient module `cyclotomicQuotientRep K L p`, namely $\mathbb{Z}/p$-valued finitely supported functions on $\Gamma_K/\Lambda$ with the permutation action twisted by the mod-$p$ cyclotomic character `cycloChar p` restricted to $\Gamma_K$, onto `continuousH2Sr` for $\Gamma_L$, $S$ and the trivial module $\mathbb{Z}/p$ twisted by `cycloChar p` restricted to $\Gamma_L$, i.e. $\mathbb{Z}/p(1)$; here `continuousH2Sr` denotes the quotient of the module `levelCocyclesSr₂` of level-$S$ $2$-cocycles by those that are coboundaries. The isomorphism is pinned on cocycle classes: whenever $z$ is a level-$S$ $2$-cocycle for $\Gamma_K$ with values in the above coset module, $w$ a level-$S$ $2$-cocycle for $\Gamma_L$ with values in $\mathbb{Z}/p$, and $w(s,t)$ equals the value of $z(s,t)$ at the identity coset for all $s,t \in \Gamma_L$ (viewed in $\Gamma_K$ via $\Gamma_L \le \Gamma_K$), then $\Theta$ sends the class of $z$ to the class of $w$.
--
--   This is the relative Shapiro lemma in degree two, in the form compatible with the level-$S$ conditions: restriction to $\Gamma_L$ followed by evaluation at the identity coset identifies the degree-two level-$S$ cohomology of $\mathbb{Z}/p[\Gamma_K/\Lambda](1)$ over $\Gamma_K$ with that of $\mathbb{Z}/p(1)$ over $\Gamma_L$. The isomorphism is produced together with its effect on cocycle classes so that later computations can use it explicitly; it is cited by [`groupCohomology.exists_continuousH2Sr_cyclotomicQuotientRep_equiv_pin`](thm.html#groupCohomology.exists_continuousH2Sr_cyclotomicQuotientRep_equiv_pin).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_apply_eq.lean

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

theorem groupCohomology.exists_continuousH2Sr_cyclotomicQuotientRep_equiv_apply_eq
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L) (hL : L.IsUnramifiedOutside S)
    [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).Normal] [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).FiniteIndex] :
    ∃ Θ : continuousH2Sr K.fixingSubgroup.subtype S (cyclotomicQuotientRep K L p) ≃ₗ[ZMod p]
        continuousH2Sr L.fixingSubgroup.subtype S
          ((Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).twist ((cycloChar p).comp L.fixingSubgroup.subtype)),
      ∀ (z : ↥(levelCocyclesSr₂ K.fixingSubgroup.subtype S (cyclotomicQuotientRep K L p)))
          (w : ↥(levelCocyclesSr₂ L.fixingSubgroup.subtype S
            ((Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).twist ((cycloChar p).comp L.fixingSubgroup.subtype)))),
        (∀ s t : ↥L.fixingSubgroup,
            (w : ↥L.fixingSubgroup × ↥L.fixingSubgroup → ZMod p) (s, t) =
              ((z : ↥K.fixingSubgroup × ↥K.fixingSubgroup → (↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup) →₀ ZMod p)
                (⟨(s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), IntermediateField.fixingSubgroup_antitone hKL s.2⟩,
                 ⟨(t : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), IntermediateField.fixingSubgroup_antitone hKL t.2⟩))
                (1 : ↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup)) →
          Θ (continuousH2Srπ K.fixingSubgroup.subtype S _ z) = continuousH2Srπ L.fixingSubgroup.subtype S _ w := by sorry

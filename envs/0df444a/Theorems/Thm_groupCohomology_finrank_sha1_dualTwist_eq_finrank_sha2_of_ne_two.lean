-- Prove2me | Theorems.Thm_groupCohomology_finrank_sha1_dualTwist_eq_finrank_sha2_of_ne_two
-- name    : groupCohomology.finrank_sha1_dualTwist_eq_finrank_sha2_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/c097203e-03d2-5152-a804-b88581c2fb76
-- title:
--   dim Ш¹_S(M^∨(1)) = dim Ш²_S(M) for odd p
-- statement:
--   Fix a prime $p$ with $p \neq 2$, a finite set $S$ of primes containing $p$ (as the element `pPrime p` of `Nat.Primes`), and a representation $M$ of the absolute Galois group $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, realised as $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ for the Mathlib algebraic closure, on a finite-dimensional $\mathbb{Z}/p$-vector space. Two arithmetic hypotheses are imposed: smoothness of the action, namely that each $m \in M$ is fixed by the fixing subgroup of some intermediate field $F$ with $F/\mathbb{Q}$ finite; and unramifiedness outside $S$, namely that for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ lying in the nonunits of $A$, every element of the inertia subgroup of $A$ over $\mathbb{Q}$ (the image in $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ of the inertia subgroup inside the decomposition subgroup) acts trivially on $M$. It is further assumed that `continuousH2S S M`, the quotient of the level-$S$ degree-two cocycles by the degree-two coboundaries meeting them, is finite-dimensional over $\mathbb{Z}/p$. The conclusion is the equality of $\mathbb{Z}/p$-dimensions $\operatorname{finrank}\,\mathrm{sha₁}\,S\,(M.\mathrm{dualTwist}\,(\mathrm{cycloChar}\,p)) = \operatorname{finrank}\,\mathrm{sha₂}\,S\,M$, where `sha₁` and `sha₂` are the project's degree-one and degree-two Tate–Shafarevich-type groups for the level $S$, and `M.dualTwist (cycloChar p)` is the representation on the $\mathbb{Z}/p$-dual of $M$ twisted by the mod-$p$ cyclotomic character $\sigma \mapsto$ `modularCyclotomicCharacter`, i.e. the Cartier dual $M^{\vee}(1)$.
--
--   This is the numerical consequence of global (Poitou–Tate) duality that the dimensions of the two Tate–Shafarevich groups $Ш^1_S(M^\vee(1))$ and $Ш^2_S(M)$ agree, in the form needed for odd residue characteristic. It feeds the Greenberg–Wiles style computation of the dimension of the tangent space of the deformation functor, and is used in [`groupCohomology.greenbergWilesLeAdm_extArithLoc_of_isTheta1_eval_of_ne_two`](thm.html#groupCohomology.greenbergWilesLeAdm_extArithLoc_of_isTheta1_eval_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_finrank_sha1_dualTwist_eq_finrank_sha2_of_ne_two.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_ContinuousDuality
import Definitions.Def_DualSelmer_ExtConditions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.finrank_sha1_dualTwist_eq_finrank_sha2_of_ne_two
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s m = m)
    (hMur : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ, M.ρ g = 1)
    [FiniteDimensional (ZMod p) (continuousH2S S M)] :
    finrank (ZMod p) (sha₁ S (M.dualTwist (cycloChar p))) = finrank (ZMod p) (sha₂ S M) := by sorry

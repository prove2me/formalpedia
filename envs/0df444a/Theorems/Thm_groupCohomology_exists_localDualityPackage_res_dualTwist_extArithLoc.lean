-- Prove2me | Theorems.Thm_groupCohomology_exists_localDualityPackage_res_dualTwist_extArithLoc
-- name    : groupCohomology.exists_localDualityPackage_res_dualTwist_extArithLoc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/ed9386f2-6c1c-55e3-9371-3b2e67fb8e91
-- title:
--   Local duality package in degree one at q∈ S
-- statement:
--   Fix a prime $p$ and a finite set $S$ of primes, and let $M$ be a representation of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ (realised as the automorphism group of `AlgebraicClosure ℚ` over $\mathbb{Q}$) on a finite-dimensional $\mathbb{Z}/p$-vector space, assumed smooth in the sense that every $m \in M$ is fixed by the fixing subgroup of some finite subextension $F/\mathbb{Q}$ of $\overline{\mathbb{Q}}$. Let $q$ be an element of $S$, and write $r =$ `extArithLoc S (Sum.inr q)` for the homomorphism `primeLocalToGlobal q` from the local Galois group at $q$ to the global one. Then there exist a $\mathbb{Z}/p$-linear form $\mathrm{inv}$ on `continuousH2 r` of the coefficient module `ofChar ((cycloChar p).comp r)`, that is, of $\mathbb{Z}/p$ with the local group acting through the mod $p$ cyclotomic character composed with $r$ (this `continuousH2` being the quotient of the level $2$ cocycles by those level $2$ cocycles that are coboundaries), and a $\mathbb{Z}/p$-linear map $\theta$ from `continuousH1 r` of the restriction $r^*M$ — the image in $H^1$ of the level $1$ cocycles — to the dual of `continuousH1 r` of the restriction $r^*(M^\vee \otimes \chi_p)$, where `M.dualTwist (cycloChar p)` is the dual representation of $M$ twisted by the mod $p$ cyclotomic character, such that: $\mathrm{inv}$ is bijective; $\theta$ satisfies `IsTheta1` for the evaluation pairing $r^*M \times r^*(M^\vee \otimes \chi_p) \to$ `ofChar ((cycloChar p).comp r)` and $\mathrm{inv}$, i.e. on classes of level-constant $1$-cocycles $f, g$ the value $\theta(f)(g)$ equals $\mathrm{inv}$ of the class of any level $2$ cocycle agreeing with the cup cochain of $f$ and $g$; and $\theta$ is bijective.
--
--   This is local Tate duality in degree one at the place $q$, packaged as the data (invariant form on $H^2$ of the twisted coefficients, cup-product-compatible map $\theta_1$, bijectivity of both) in which the restriction to the decomposition group is taken after the Cartier dual twist. It feeds the Greenberg–Wiles computation of local terms, being cited by [`groupCohomology.greenbergWiles_eq_unramifiedMenu_extArithLoc`](thm.html#groupCohomology.greenbergWiles_eq_unramifiedMenu_extArithLoc).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_localDualityPackage_res_dualTwist_extArithLoc.lean

import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousDuality
import Definitions.Def_DualSelmer_ExtConditions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory Module groupCohomology ExtCitation in

theorem groupCohomology.exists_localDualityPackage_res_dualTwist_extArithLoc
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s m = m) (q : ↥S) :
    ∃ (inv : continuousH2 (extArithLoc S (Sum.inr q))
          (ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inr q)))) →ₗ[ZMod p] ZMod p)
      (θ : continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M) →ₗ[ZMod p]
        Module.Dual (ZMod p) (continuousH1 (extArithLoc S (Sum.inr q))
          (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))))),
      Function.Bijective inv ∧
      IsTheta1 (extArithLoc S (Sum.inr q))
        (Module.Dual.eval (ZMod p) M :
          Rep.res (extArithLoc S (Sum.inr q)) M →ₗ[ZMod p]
            Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)) →ₗ[ZMod p]
              ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inr q)))) inv θ ∧
      Function.Bijective θ := by sorry

-- Prove2me | Theorems.Thm_groupCohomology_bijective_of_isTheta1_localInv_extArithLoc
-- name    : groupCohomology.bijective_of_isTheta1_localInv_extArithLoc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/a0d3d97f-a11a-5728-9785-df5724bc6e1f
-- title:
--   Degree-one local duality at q: bijectivity of θ
-- statement:
--   Fix a prime $p$, a finite set $S$ of primes and an element $q$ of $S$. Let $M$ be a representation of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q) = \overline{\mathbb Q}\simeq_{\mathbb Q}\overline{\mathbb Q}$ on a finite-dimensional $\mathbb Z/p$-vector space which is smooth in the sense that every $m \in M$ is fixed by $M.\rho(s)$ for all $s$ in the fixing subgroup of some finite extension $F/\mathbb Q$ inside $\overline{\mathbb Q}$, and let $\zeta \in \overline{\mathbb Q}$ be a primitive $p$-th root of unity. Write $\mathrm{loc} =$ `extArithLoc S (Sum.inr q)`, which at the index $\mathrm{inr}\,q$ is the map `primeLocalToGlobal` from the local Galois group at $q$ to the global one. Let $\theta$ be a $\mathbb Z/p$-linear map from `continuousH1 loc` of the restriction of $M$ along $\mathrm{loc}$ — that is, from the image in $H^1$ of the level-$\mathrm{loc}$ $1$-cocycles — to the $\mathbb Z/p$-dual of the corresponding `continuousH1` of the restriction of $M^{\vee}$ twisted by the mod-$p$ cyclotomic character `cycloChar p` (the twist is formed globally and then restricted). Assume `IsTheta1` holds for $\theta$ with respect to the evaluation pairing $M \to (M^{\vee}(1)) \to$ `ofChar ((cycloChar p).comp loc)` and the functional `localInv p ζ q`: for all level-constant $1$-cocycles $f$ with values in the restriction of $M$ and $g$ with values in the restriction of $M^{\vee}(1)$, and every level $2$-cocycle $e$ agreeing pointwise with the cup cochain of $f$ and $g$, one has $\theta([f])([g]) =$ `localInv p ζ q` applied to the class of $e$ in `continuousH2`. The conclusion is that $\theta$ is bijective.
--
--   This is local Tate duality in degree one at the finite place $q$, in the form used by the Poitou–Tate localisation frame: the pairing map $\theta_q$ normalised by the cup product and the local invariant is an isomorphism onto the dual. It is consumed in the assembly of the nondegenerate pairing between the Selmer-type groups $Ш^1$ and $Ш^2$ of $M$ and $M^{\vee}(1)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_bijective_of_isTheta1_localInv_extArithLoc.lean

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousDuality
import Definitions.Def_GroupCohomology_LocalInvariant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory ExtCitation
open groupCohomology

theorem groupCohomology.bijective_of_isTheta1_localInv_extArithLoc
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (q : ↥S)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s m = m)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
    (θ : continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M) →ₗ[ZMod p]
        Module.Dual (ZMod p)
          (continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))))
    (hθ :
      haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
      IsTheta1 (extArithLoc S (Sum.inr q))
        (Module.Dual.eval (ZMod p) M :
          Rep.res (extArithLoc S (Sum.inr q)) M →ₗ[ZMod p]
            Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)) →ₗ[ZMod p]
              ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inr q))))
        (localInv p ζ (q : Nat.Primes)) θ) :
    Function.Bijective θ := by sorry

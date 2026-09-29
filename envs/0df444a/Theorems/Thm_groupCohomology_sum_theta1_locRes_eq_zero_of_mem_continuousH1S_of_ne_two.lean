-- Prove2me | Theorems.Thm_groupCohomology_sum_theta1_locRes_eq_zero_of_mem_continuousH1S_of_ne_two
-- name    : groupCohomology.sum_theta1_locRes_eq_zero_of_mem_continuousH1S_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/d7857e73-1842-5f4f-9263-6de525200561
-- title:
--   Sum of local Tate pairings of global classes vanishes, p odd
-- statement:
--   Let $p$ be an odd prime, $S$ a finite set of rational primes, $M$ a representation of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ over $\mathbb Z/p$, and $\zeta\in\overline{\mathbb Q}$ a primitive $p$-th root of unity; write $M' =$ `M.dualTwist (cycloChar p)` for the dual of $M$ twisted by the mod $p$ cyclotomic character. For each $q\in S$ let $\theta_q$ be a $\mathbb Z/p$-linear map from `continuousH1` of the restriction of $M$ along `extArithLoc S (Sum.inr q)` (the submodule of $H^1$ spanned by classes of level cocycles) to the dual of the corresponding `continuousH1` for $M'$, and assume each $\theta_q$ satisfies `IsTheta1` for the evaluation pairing $M\times M'\to$ `ofChar` of the cyclotomic character composed with the local map, with respect to the invariant `localInv p ζ q`: on classes of level-constant cocycles $f,g$, $\theta_q([f])([g])$ is the inverse image under `continuousH2π` of any level $2$-cocycle whose underlying function is the cup cochain of $f$ and $g$. Let $x\in H^1(M)$ and $y\in H^1(M')$ lie in `continuousH1S S` (classes of level-$S$ cocycles), and assume the restriction of $x$ along the archimedean component `extArithLoc S (Sum.inl ())` vanishes. Let $z_q$, $w_q$ be elements of the local `continuousH1` submodules whose underlying classes are the localisations of $x$, resp. $y$, at $q$. Then $\sum_{q\in S}\theta_q(z_q)(w_q)=0$.
--
--   This is the global reciprocity relation for the local Tate pairings: the sum of the local pairings of the localisations of two global classes, one of them trivial at the archimedean place, vanishes; it is the exactness statement underlying the Poitou–Tate mechanism used to compute dual Selmer groups. It is invoked in the criterion characterising which families of local classes come from a global class in `continuousH1S`, and in its archimedean variant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_sum_theta1_locRes_eq_zero_of_mem_continuousH1S_of_ne_two.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_ContinuousDuality
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_GroupCohomology_LocalInvariant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.sum_theta1_locRes_eq_zero_of_mem_continuousH1S_of_ne_two
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hp2 : p ≠ 2)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
    (θ : ∀ q : ↥S,
      continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M) →ₗ[ZMod p]
        Module.Dual (ZMod p)
          (continuousH1 (extArithLoc S (Sum.inr q))
            (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))))
    (hθ : ∀ q : ↥S,
      haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
      IsTheta1 (extArithLoc S (Sum.inr q))
        (Module.Dual.eval (ZMod p) M :
          Rep.res (extArithLoc S (Sum.inr q)) M →ₗ[ZMod p]
            Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)) →ₗ[ZMod p]
              ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inr q))))
        (localInv p ζ (q : Nat.Primes)) (θ q))
    (x : H1 M) (hx : x ∈ continuousH1S S M)
    (hxinf : (locRes (extArithLoc S) M (Sum.inl ())).hom x = 0)
    (y : H1 (M.dualTwist (cycloChar p))) (hy : y ∈ continuousH1S S (M.dualTwist (cycloChar p)))
    (z : ∀ q : ↥S, continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M))
    (w : ∀ q : ↥S, continuousH1 (extArithLoc S (Sum.inr q))
      (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))))
    (hz : ∀ q, (z q : H1 _) = (locRes (extArithLoc S) M (Sum.inr q)).hom x)
    (hw : ∀ q, (w q : H1 _) = (locRes (extArithLoc S) (M.dualTwist (cycloChar p)) (Sum.inr q)).hom y) :
    ∑ q : ↥S, θ q (z q) (w q) = 0 := by sorry

-- Prove2me | Theorems.Thm_groupCohomology_exists_mem_continuousH1S_locRes_eq_iff_forall_sum_theta_eq_zero_of_ne_two
-- name    : groupCohomology.exists_mem_continuousH1S_locRes_eq_iff_forall_sum_theta_eq_zero_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/52f64d2d-b9c5-5df4-b07e-37aa9c73d264
-- title:
--   Poitou–Tate exactness in degree one, odd p
-- statement:
--   Let $p$ be an odd prime, let $S$ be a finite set of primes with $p \in S$ (as `pPrime p`), and let $M$ be a finite-dimensional representation of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ over $\mathbb{Z}/p$. Assume: every $m \in M$ is fixed by the fixing subgroup of some finite intermediate field $F/\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ (smoothness); for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q \in A.\mathrm{nonunits}$, every element of the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ acts as the identity on $M$; and $H^1$ of the restriction of $M$ along the inclusion `archimedeanDecomposition` $\hookrightarrow \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ is a subsingleton. Fix a primitive $p$-th root of unity $\zeta \in \overline{\mathbb{Q}}$. For each $q \in S$ let $\theta_q$ be a $\mathbb{Z}/p$-linear map from `continuousH1` of the restriction of $M$ along `extArithLoc S (Sum.inr q)` (the image under `H1π` of `levelCocycles₁`) to the dual of `continuousH1` of the restriction of the cyclotomic dual twist `M.dualTwist (cycloChar p)` $= M^\vee \otimes \chi_p$, and assume each $\theta_q$ satisfies `IsTheta1` for the evaluation pairing $M \times (M^\vee \otimes \chi_p) \to$ `ofChar` $(\chi_p \circ \mathrm{loc}_q)$ and the local invariant `localInv p ζ q`, i.e. $\theta_q$ computes the cup product of level-constant $1$-cocycles followed by that invariant. Then, for a family $z = (z_q)_{q \in S}$ of such local classes, there exists $x$ in `continuousH1S S M` (the image under `H1π` of `levelCocyclesS₁ S M`) whose restriction `locRes` at each $q \in S$ equals $z_q$ if and only if, for every $y$ in `continuousH1S S (M.dualTwist (cycloChar p))` and every family $w = (w_q)_{q\in S}$ of continuous local classes of the dual twist with $w_q$ equal to the restriction of $y$ at $q$, one has $\sum_{q \in S} \theta_q(z_q)(w_q) = 0$.
--
--   This is the degree-one Poitou–Tate exactness statement in the form used on the route to $R = T$: the local conditions at $S$ cutting out the image of the global $S$-level classes are exactly annihilation, under the local duality pairings $\theta_q$ normalised by the canonical local invariants, of all localisations of global $S$-level classes of the cyclotomic dual twist. It is the odd-$p$ edition, the hypothesis $p \neq 2$ being carried so that the downstream Greenberg–Wiles computation [`groupCohomology.greenbergWilesLeAdm_extArithLoc_of_isTheta1_eval_of_ne_two`](thm.html#groupCohomology.greenbergWilesLeAdm_extArithLoc_of_isTheta1_eval_of_ne_two), stated for odd $p$, can apply it directly.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_mem_continuousH1S_locRes_eq_iff_forall_sum_theta_eq_zero_of_ne_two.lean

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

theorem groupCohomology.exists_mem_continuousH1S_locRes_eq_iff_forall_sum_theta_eq_zero_of_ne_two
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s m = m)
    (hMur : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ, M.ρ g = 1)
    (hinf : Subsingleton (H1 (Rep.res (extArithLoc S (Sum.inl ())) M)))
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
    (z : ∀ q : ↥S, continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M)) :
    (∃ x ∈ continuousH1S S M, ∀ q : ↥S, (locRes (extArithLoc S) M (Sum.inr q)).hom x = (z q : H1 _)) ↔
      ∀ y ∈ continuousH1S S (M.dualTwist (cycloChar p)),
        ∀ w : ∀ q : ↥S, continuousH1 (extArithLoc S (Sum.inr q))
            (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))),
          (∀ q, (w q : H1 _) = (locRes (extArithLoc S) (M.dualTwist (cycloChar p)) (Sum.inr q)).hom y) →
          ∑ q : ↥S, θ q (z q) (w q) = 0 := by sorry

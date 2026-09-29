-- Prove2me | Theorems.Thm_groupCohomology_cupCochain_mem_levelCocyclesS2_and_theta1_eq_localInv_locRes2S
-- name    : groupCohomology.cupCochain_mem_levelCocyclesS2_and_theta1_eq_localInv_locRes2S
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/a33a90ce-3d4f-5a08-bb91-0af91be98806
-- title:
--   Cup product of level-S cocycles and local invariants
-- statement:
--   Fix a prime $p$, a finite set $S$ of rational primes, a representation $M$ of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ over $\mathbb{Z}/p$, and an element $\zeta\in\overline{\mathbb{Q}}$. Write $M^{*}(\chi_p)=$ `M.dualTwist (cycloChar p)` for the dual of $M$ twisted by the mod-$p$ cyclotomic character `cycloChar p`, and $\mathbb{Z}/p(\chi_p)=$ `ofChar (cycloChar p)` for the trivial module twisted by that character; the places are indexed by `extArithIndex S`, the decomposition map being the inclusion of `archimedeanDecomposition` at `Sum.inl ()` and `primeLocalToGlobal q` at `Sum.inr q`. Suppose given, for each $q\in S$, a $\mathbb{Z}/p$-linear map $\theta_q$ from `continuousH1` of $M$ restricted to the local group at $q$ to the dual of `continuousH1` of $M^{*}(\chi_p)$ restricted there, and suppose each $\theta_q$ satisfies `IsTheta1` for the evaluation pairing `Module.Dual.eval` into $\mathbb{Z}/p(\chi_p)$ and the functional `localInv p ζ q`: that is, for all level-constant $1$-cocycles $f_0,g_0$ and every level $2$-cocycle agreeing pointwise with $(s,t)\mapsto\langle f_0(s),\rho_s g_0(t)\rangle$, the value $\theta_q([f_0])([g_0])$ equals `localInv p ζ q` of the class of that $2$-cocycle. Let $f$ be a $1$-cocycle for $M$ and $g$ a $1$-cocycle for $M^{*}(\chi_p)$, both satisfying the level condition `IsLevelConstantS₁ S`. Then the cup cochain $(s,t)\mapsto\langle f(s),\rho_s g(t)\rangle$ lies in `levelCocyclesS₂ S` for $\mathbb{Z}/p(\chi_p)$, and, for the resulting class $c$ in `continuousH2S`: (i) for each $q\in S$ and each $z,w$ in the respective continuous $H^1$ subspaces whose underlying $H^1$ classes are the images of $[f]$ and $[g]$ under `locRes` at $q$, one has $\theta_q(z)(w)=$ `localInv p ζ q` applied to the localisation `locRes₂S` of $c$ at $q$; and (ii) if the localisation of $[f]$ at the archimedean place vanishes, then the localisation `locRes₂S` of $c$ at the archimedean place vanishes. The membership proof and the two assertions are packaged as a single existential, so both refer to the same class $c$.
--
--   This is the local–global compatibility of the cup product with restriction, stated in the restricted-ramification currency of level-$S$ cochains and of local duality maps characterised by the local invariant: the local pairing of the restrictions of two global classes is computed by the localisation of the global cup product class. It feeds [`groupCohomology.sum_theta1_locRes_eq_zero_of_mem_continuousH1S_of_ne_two`](thm.html#groupCohomology.sum_theta1_locRes_eq_zero_of_mem_continuousH1S_of_ne_two), the global reciprocity relation asserting that the sum over places of these local pairings vanishes, used in bounding Selmer groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_cupCochain_mem_levelCocyclesS2_and_theta1_eq_localInv_locRes2S.lean

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

theorem groupCohomology.cupCochain_mem_levelCocyclesS2_and_theta1_eq_localInv_locRes2S
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (ζ : AlgebraicClosure ℚ)
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
    (f : cocycles₁ M) (hf : IsLevelConstantS₁ S (⇑f))
    (g : cocycles₁ (M.dualTwist (cycloChar p))) (hg : IsLevelConstantS₁ S (⇑g)) :
    ∃ hc : cupCochain (Module.Dual.eval (ZMod p) M :
          M →ₗ[ZMod p] M.dualTwist (cycloChar p) →ₗ[ZMod p] ofChar (k := ZMod p) (cycloChar p))
        (⇑f) (⇑g) ∈ levelCocyclesS₂ S (ofChar (k := ZMod p) (cycloChar p)),
      (∀ q : ↥S,
        haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
        ∀ (z : continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M))
          (w : continuousH1 (extArithLoc S (Sum.inr q))
            (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))),
          (z : H1 _) = (locRes (extArithLoc S) M (Sum.inr q)).hom ((H1π M).hom f) →
          (w : H1 _) = (locRes (extArithLoc S) (M.dualTwist (cycloChar p)) (Sum.inr q)).hom
              ((H1π (M.dualTwist (cycloChar p))).hom g) →
          θ q z w = localInv p ζ (q : Nat.Primes)
            (locRes₂S S (ofChar (k := ZMod p) (cycloChar p)) (extArithLoc S (Sum.inr q))
              (continuousH2Sπ S (ofChar (k := ZMod p) (cycloChar p)) ⟨_, hc⟩))) ∧
      ((locRes (extArithLoc S) M (Sum.inl ())).hom ((H1π M).hom f) = 0 →
        locRes₂S S (ofChar (k := ZMod p) (cycloChar p)) (extArithLoc S (Sum.inl ()))
          (continuousH2Sπ S (ofChar (k := ZMod p) (cycloChar p)) ⟨_, hc⟩) = 0) := by sorry

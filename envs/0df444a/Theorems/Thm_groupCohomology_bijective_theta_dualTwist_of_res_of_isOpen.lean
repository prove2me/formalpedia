-- Prove2me | Theorems.Thm_groupCohomology_bijective_theta_dualTwist_of_res_of_isOpen
-- name    : groupCohomology.bijective_theta_dualTwist_of_res_of_isOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/2d762c7c-f274-5bdd-906c-ce84376b258a
-- title:
--   Local duality over S descends from a subgroup of index prime to p
-- statement:
--   Fix a prime $p$ and a prime $q$, and let $G_q$ denote the group `primeLocalGaloisGroup q` of $\mathbb{Q}_p[q]$-algebra automorphisms of a fixed algebraic closure of $\mathbb{Q}_q$, together with the homomorphism `primeLocalToGlobal q` to $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$; write $\chi$ for the mod-$p$ cyclotomic character `cycloChar p` and $N =$ `ofChar` of $\chi \circ$ `primeLocalToGlobal q`, the one-dimensional $\mathbb{Z}/p$-representation obtained by twisting the trivial representation by that character. Let $S \le G_q$ be a subgroup and $U \le S$ a subgroup of finite index whose index is a unit in $\mathbb{Z}/p$, such that for some finite extension $F_0/\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ the preimage of the fixing subgroup of $F_0$ under the level map of $S$ is contained in $U$, and such that the continuous $H^2$ of $U$ — the quotient of the level $2$-cocycles by those level $2$-cocycles that are level coboundaries — with coefficients in $N$ restricted to $U$ is one-dimensional over $\mathbb{Z}/p$. Let $M$ be a finite-dimensional $\mathbb{Z}/p$-representation of $S$ which is smooth, in the sense that every $m \in M$ is fixed by all $s \in S$ whose image lies in the fixing subgroup of some finite extension of $\mathbb{Q}$, and let $D =$ `M.dualTwist` of $\chi$ restricted to $S$, the dual representation twisted by that character, paired with $M$ into $N$ by evaluation. Let $\mathrm{inv} \colon H^2_{\mathrm{cts}}(S,N) \to \mathbb{Z}/p$ be a bijective linear map. Assume the duality statement over $U$: for every bijective linear functional $\mathrm{inv}_U$ on $H^2_{\mathrm{cts}}(U, N)$ and every triple of maps $\theta_0, \theta_1, \theta_2$ satisfying `IsTheta0`, `IsTheta1`, `IsTheta2` for the restricted data and $\mathrm{inv}_U$, all three are bijective. Then, for any maps $\theta_0 \colon M^S \to H^2_{\mathrm{cts}}(S,D)^\vee$, $\theta_1 \colon H^1_{\mathrm{cts}}(S,M) \to H^1_{\mathrm{cts}}(S,D)^\vee$ and $\theta_2 \colon H^2_{\mathrm{cts}}(S,M) \to (D^S)^\vee$ satisfying `IsTheta0`, `IsTheta1` and `IsTheta2` for the evaluation pairing and $\mathrm{inv}$ — that is, $\theta_0(m)([z]) = \mathrm{inv}([e])$ whenever $e(s,t) = \langle m, z(s,t)\rangle$, $\theta_1([f])([g]) = \mathrm{inv}([e])$ whenever $e$ agrees with the cup cochain of $f$ and $g$, and $\theta_2([z])(d) = \mathrm{inv}([e])$ whenever $e(s,t) = \langle z(s,t), d\rangle$, for level cocycles throughout — all three of $\theta_0$, $\theta_1$, $\theta_2$ are bijective.
--
--   This is the relative dévissage step in the proof of local Tate duality at $q$ in degrees $0$, $1$, $2$ for a finite smooth mod-$p$ representation and its Cartier dual: duality for a subgroup of index prime to $p$, together with the one-dimensionality of the Brauer-type invariant there, propagates to the ambient subgroup by the unit–trace maps of coinduction. It is used in the passage to an arbitrary open subgroup of the local Galois group, [`groupCohomology.bijective_theta_dualTwist_of_isOpen`](thm.html#groupCohomology.bijective_theta_dualTwist_of_isOpen).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_bijective_theta_dualTwist_of_res_of_isOpen.lean

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_CupProduct
import Definitions.Def_GroupCohomology_ContinuousDuality
import Definitions.Def_GroupCohomology_Selmer
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.bijective_theta_dualTwist_of_res_of_isOpen
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes)
    (S : Subgroup (primeLocalGaloisGroup q)) (U : Subgroup S) [U.FiniteIndex] (hUp : IsUnit ((U.index : ℕ) : ZMod p))
    (hU : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap ((primeLocalToGlobal q).comp S.subtype) ≤ U)
    (hTU : FiniteDimensional (ZMod p) (continuousH2 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))))) ∧
      finrank (ZMod p) (continuousH2 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))))) = 1)
    (M : Rep.{0} (ZMod p) S) [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : S, ((primeLocalToGlobal q).comp S.subtype) s ∈ F.fixingSubgroup → M.ρ s m = m)
    (inv : continuousH2 ((primeLocalToGlobal q).comp S.subtype) (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) →ₗ[ZMod p] ZMod p)
    (hinv : Function.Bijective inv)
    (hres : ∀ (invU : continuousH2 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))) →ₗ[ZMod p] ZMod p),
      Function.Bijective invU →
      ∀ (θ₀ : (Rep.res U.subtype M).ρ.invariants →ₗ[ZMod p] Module.Dual (ZMod p)
          (continuousH2 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))))),
        IsTheta0 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Module.Dual.eval (ZMod p) M : Rep.res U.subtype M →ₗ[ZMod p]
            Rep.res U.subtype (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) →ₗ[ZMod p]
            Rep.res U.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))) invU θ₀ →
      ∀ (θ₁ : continuousH1 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype M) →ₗ[ZMod p] Module.Dual (ZMod p)
          (continuousH1 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))))),
        IsTheta1 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Module.Dual.eval (ZMod p) M : Rep.res U.subtype M →ₗ[ZMod p]
            Rep.res U.subtype (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) →ₗ[ZMod p]
            Rep.res U.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))) invU θ₁ →
      ∀ (θ₂ : continuousH2 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype M) →ₗ[ZMod p] Module.Dual (ZMod p)
          (Rep.res U.subtype (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))).ρ.invariants),
        IsTheta2 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Module.Dual.eval (ZMod p) M : Rep.res U.subtype M →ₗ[ZMod p]
            Rep.res U.subtype (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) →ₗ[ZMod p]
            Rep.res U.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))) invU θ₂ →
      Function.Bijective θ₀ ∧ Function.Bijective θ₁ ∧ Function.Bijective θ₂)
    (θ₀ : M.ρ.invariants →ₗ[ZMod p] Module.Dual (ZMod p) (continuousH2 ((primeLocalToGlobal q).comp S.subtype) (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))))
    (hθ₀ : IsTheta0 ((primeLocalToGlobal q).comp S.subtype) (Module.Dual.eval (ZMod p) M : M →ₗ[ZMod p] M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype) →ₗ[ZMod p]
        Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) inv θ₀)
    (θ₁ : continuousH1 ((primeLocalToGlobal q).comp S.subtype) M →ₗ[ZMod p] Module.Dual (ZMod p) (continuousH1 ((primeLocalToGlobal q).comp S.subtype) (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))))
    (hθ₁ : IsTheta1 ((primeLocalToGlobal q).comp S.subtype) (Module.Dual.eval (ZMod p) M : M →ₗ[ZMod p] M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype) →ₗ[ZMod p]
        Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) inv θ₁)
    (θ₂ : continuousH2 ((primeLocalToGlobal q).comp S.subtype) M →ₗ[ZMod p] Module.Dual (ZMod p) (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)).ρ.invariants)
    (hθ₂ : IsTheta2 ((primeLocalToGlobal q).comp S.subtype) (Module.Dual.eval (ZMod p) M : M →ₗ[ZMod p] M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype) →ₗ[ZMod p]
        Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) inv θ₂) :
    Function.Bijective θ₀ ∧ Function.Bijective θ₁ ∧ Function.Bijective θ₂ := by sorry

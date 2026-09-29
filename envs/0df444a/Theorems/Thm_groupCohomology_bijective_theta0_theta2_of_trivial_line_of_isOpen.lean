-- Prove2me | Theorems.Thm_groupCohomology_bijective_theta0_theta2_of_trivial_line_of_isOpen
-- name    : groupCohomology.bijective_theta0_theta2_of_trivial_line_of_isOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/802e6d6d-cf89-59ff-8fb6-e6e79f8bb6ed
-- title:
--   Bijectivity of θ⁰ and θ² for a trivial 𝔽ₚ-line
-- statement:
--   Fix a prime $p$ and a prime $q$, and let $S$ be a subgroup of $\mathrm{Gal}(\overline{\mathbb{Q}}_q/\mathbb{Q}_q)$, where $\overline{\mathbb{Q}}_q$ is the chosen algebraic closure of $\mathbb{Q}_q$. Assume: (i) there is an intermediate field $F_0$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, whose fixing subgroup pulls back, along the local-to-global map $\mathrm{Gal}(\overline{\mathbb{Q}}_q/\mathbb{Q}_q)\to\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, into $S$; (ii) the mod-$p$ cyclotomic character $\chi$, pulled back to $S$ along that map, is identically $1$; (iii) $A$ is a representation of $S$ over $\mathbb{Z}/p$ on which every $s\in S$ acts as the identity, with $\dim_{\mathbb{Z}/p}A=1$; (iv) $\mathrm{inv}_S$ is a bijective $\mathbb{Z}/p$-linear map from the continuous $H^2$ of $S$ (continuity measured through the local-to-global map: cocycles of level type modulo coboundaries) with coefficients in the trivial line twisted by $\chi$, to $\mathbb{Z}/p$. Let $\theta_0 : A^S \to (H^2_{\mathrm{cts}}(S, A^\vee(\chi)))^*$ and $\theta_2 : H^2_{\mathrm{cts}}(S,A) \to ((A^\vee(\chi))^S)^*$ be linear maps satisfying the predicates `IsTheta0` and `IsTheta2` for the evaluation pairing $A \to (A^\vee(\chi) \to (\mathbb{Z}/p)(\chi))$ and $\mathrm{inv}_S$, i.e. $\theta_0(m)([z]) = \mathrm{inv}_S([e])$ and $\theta_2([z])(d) = \mathrm{inv}_S([e])$ whenever the $2$-cocycle $e$ is obtained pointwise from $z$ by the pairing against $m$, resp. against $d$. Then $\theta_0$ and $\theta_2$ are both bijective.
--
--   This is the degree-$0$ and degree-$2$ part of local Tate duality in the special case of a one-dimensional trivial coefficient line over an open subgroup of a local Galois group on which the mod-$p$ cyclotomic character is trivial; all three modules involved are then trivial $S$-lines with one-dimensional continuous $H^2$. It is used by [`groupCohomology.bijective_theta_dualTwist_of_sylowLevel`](thm.html#groupCohomology.bijective_theta_dualTwist_of_sylowLevel) and feeds the local duality input to the dual Selmer group computations, and it cites the computation [`groupCohomology.finrank_continuousH2_ofChar_cycloChar_of_isOpen`](thm.html#groupCohomology.finrank_continuousH2_ofChar_cycloChar_of_isOpen) of that $H^2$ together with the transport of invariants and continuous cohomology along an isomorphism of representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_bijective_theta0_theta2_of_trivial_line_of_isOpen.lean

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

theorem groupCohomology.bijective_theta0_theta2_of_trivial_line_of_isOpen {p : ℕ} [Fact p.Prime] (q : Nat.Primes)
    (S : Subgroup (primeLocalGaloisGroup q))
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S)
    (hχS : ∀ s : primeLocalGaloisGroup q, s ∈ S → (cycloChar p) (primeLocalToGlobal q s) = 1)
    (A : Rep (ZMod p) S) (hA : ∀ (s : S) (a : A), A.ρ s a = a) (hA1 : finrank (ZMod p) A = 1)
    (invS : continuousH2 ((primeLocalToGlobal q).comp S.subtype)
      (ofChar (k := ZMod p) (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) →ₗ[ZMod p] ZMod p)
    (hinvS : Function.Bijective invS)
    (θ₀ : A.ρ.invariants →ₗ[ZMod p] Module.Dual (ZMod p)
      (continuousH2 ((primeLocalToGlobal q).comp S.subtype) (A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))))
    (hθ₀ : IsTheta0 ((primeLocalToGlobal q).comp S.subtype)
      (Module.Dual.eval (ZMod p) A : A →ₗ[ZMod p] A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)
        →ₗ[ZMod p] ofChar (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) invS θ₀)
    (θ₂ : continuousH2 ((primeLocalToGlobal q).comp S.subtype) A →ₗ[ZMod p] Module.Dual (ZMod p)
      (A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)).ρ.invariants)
    (hθ₂ : IsTheta2 ((primeLocalToGlobal q).comp S.subtype)
      (Module.Dual.eval (ZMod p) A : A →ₗ[ZMod p] A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)
        →ₗ[ZMod p] ofChar (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) invS θ₂) :
    Function.Bijective θ₀ ∧ Function.Bijective θ₂ := by sorry

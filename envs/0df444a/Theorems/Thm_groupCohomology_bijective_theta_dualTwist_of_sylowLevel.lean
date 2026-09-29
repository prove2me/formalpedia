-- Prove2me | Theorems.Thm_groupCohomology_bijective_theta_dualTwist_of_sylowLevel
-- name    : groupCohomology.bijective_theta_dualTwist_of_sylowLevel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/df08e2f6-a9b9-5fcd-9c52-e2a10864627a
-- title:
--   Local Tate duality at a Sylow level
-- statement:
--   Fix a prime $p$ and a prime $q$, and let $G_q = \mathrm{Aut}(\overline{\mathbb{Q}}_q/\mathbb{Q}_q)$ be `primeLocalGaloisGroup q`, with `primeLocalToGlobal q` its monoid homomorphism to $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$; write $r$ for the composite of this map with the inclusion of a subgroup $S \le G_q$, and $\chi$ for the composite of $r$ with the mod-$p$ cyclotomic character `cycloChar p` of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$. Assume: there is a finite extension $F_0/\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ with the preimage under `primeLocalToGlobal q` of its fixing subgroup contained in $S$; a subgroup $U \le G_q$ is given such that every $s \in S$ has some $p$-power $s^{p^n} \in U$, and `cycloChar p` is trivial on the image of $U$; $A$ is a finite-dimensional $\mathbb{Z}/p$-representation of $S$ such that each $a \in A$ is fixed by all $s \in S$ whose image under $r$ fixes some finite extension $F/\mathbb{Q}$ in $\overline{\mathbb{Q}}$, and such that every $s \in S$ lying in $U$ acts trivially on $A$. Let $\mathrm{inv}_S$ be a bijective $\mathbb{Z}/p$-linear map from `continuousH2` of the line `ofChar` $\chi$ (the trivial representation twisted by $\chi$) to $\mathbb{Z}/p$. Let $\varphi$ be the evaluation pairing $A \times A^{\vee}(\chi) \to \mathbb{Z}/p(\chi)$, where $A^{\vee}(\chi) =$ `A.dualTwist` $\chi$ is the dual of $A$ twisted by $\chi$, and let $\theta_0 : A^S \to \mathrm{Dual}\,(\mathrm{continuousH}^2(r, A^{\vee}(\chi)))$, $\theta_1 : \mathrm{continuousH}^1(r,A) \to \mathrm{Dual}\,(\mathrm{continuousH}^1(r,A^{\vee}(\chi)))$ and $\theta_2 : \mathrm{continuousH}^2(r,A) \to \mathrm{Dual}\,((A^{\vee}(\chi))^S)$ be linear maps satisfying `IsTheta0`, `IsTheta1`, `IsTheta2` for $\varphi$ and $\mathrm{inv}_S$, i.e. characterised by: pairing representing (level) cocycles via $\varphi$ — by $\varphi(m)(z(s,t))$ in degrees $(0,2)$, by the cup cochain $(s,t) \mapsto \varphi(f(s))(\rho(s) g(t))$ in degrees $(1,1)$, and by $\varphi(z(s,t))(d)$ in degrees $(2,0)$ — and then applying $\mathrm{inv}_S$ to the resulting class. Here $\mathrm{continuousH}^2(r,M)$ is the quotient of the level 2-cocycles by the level 2-coboundaries and $\mathrm{continuousH}^1(r,M)$ is the image of the level 1-cocycles in $H^1(S,M)$. The conclusion is that $\theta_0$, $\theta_1$ and $\theta_2$ are all bijective.
--
--   This is local Tate duality for finite $p$-torsion Galois modules over $\mathbb{Q}_q$, formulated at the "Sylow level" $S$ of a dévissage: $S$ is cut out by an open condition, the image of $S$ in $\mathrm{GL}(A)$ is a finite $p$-group because every element of $S$ has a $p$-power in $U$ and $U$ acts trivially, and $\mu_p$ is rational over the fixed field of $S$. It is the inductive core from which the duality statements for general open subgroups and for the full local Galois group, [`groupCohomology.bijective_theta_dualTwist_of_isOpen`](thm.html#groupCohomology.bijective_theta_dualTwist_of_isOpen) and [`groupCohomology.bijective_theta_dualTwist_of_primeLocal`](thm.html#groupCohomology.bijective_theta_dualTwist_of_primeLocal), are deduced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_bijective_theta_dualTwist_of_sylowLevel.lean

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

theorem groupCohomology.bijective_theta_dualTwist_of_sylowLevel
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes)
    (S : Subgroup (primeLocalGaloisGroup q))
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S)
    (U : Subgroup (primeLocalGaloisGroup q))
    (hSU : ∀ s : primeLocalGaloisGroup q, s ∈ S → ∃ n : ℕ, s ^ (p ^ n) ∈ U)
    (hχU : ∀ u : primeLocalGaloisGroup q, u ∈ U → (cycloChar p) (primeLocalToGlobal q u) = 1)
    (A : Rep (ZMod p) S) [FiniteDimensional (ZMod p) A]
    (hsmA : ∀ a : A, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : S, ((primeLocalToGlobal q).comp S.subtype) s ∈ F.fixingSubgroup → A.ρ s a = a)
    (hUA : ∀ s : S, (s : primeLocalGaloisGroup q) ∈ U → ∀ a : A, A.ρ s a = a)
    (invS : continuousH2 ((primeLocalToGlobal q).comp S.subtype)
      (ofChar (k := ZMod p) (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) →ₗ[ZMod p] ZMod p)
    (hinvS : Function.Bijective invS)
    (θ₀ : A.ρ.invariants →ₗ[ZMod p] Module.Dual (ZMod p)
      (continuousH2 ((primeLocalToGlobal q).comp S.subtype) (A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))))
    (hθ₀ : IsTheta0 ((primeLocalToGlobal q).comp S.subtype)
      (Module.Dual.eval (ZMod p) A : A →ₗ[ZMod p] A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)
        →ₗ[ZMod p] ofChar (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) invS θ₀)
    (θ₁ : continuousH1 ((primeLocalToGlobal q).comp S.subtype) A →ₗ[ZMod p] Module.Dual (ZMod p)
      (continuousH1 ((primeLocalToGlobal q).comp S.subtype) (A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))))
    (hθ₁ : IsTheta1 ((primeLocalToGlobal q).comp S.subtype)
      (Module.Dual.eval (ZMod p) A : A →ₗ[ZMod p] A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)
        →ₗ[ZMod p] ofChar (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) invS θ₁)
    (θ₂ : continuousH2 ((primeLocalToGlobal q).comp S.subtype) A →ₗ[ZMod p] Module.Dual (ZMod p)
      (A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)).ρ.invariants)
    (hθ₂ : IsTheta2 ((primeLocalToGlobal q).comp S.subtype)
      (Module.Dual.eval (ZMod p) A : A →ₗ[ZMod p] A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)
        →ₗ[ZMod p] ofChar (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) invS θ₂) :
    Function.Bijective θ₀ ∧ Function.Bijective θ₁ ∧ Function.Bijective θ₂ := by sorry

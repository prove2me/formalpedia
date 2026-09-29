-- Prove2me | Theorems.Thm_groupCohomology_bijective_theta_dualTwist_of_isOpen
-- name    : groupCohomology.bijective_theta_dualTwist_of_isOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/5fa8877a-5340-56c0-8071-748c06c1dc86
-- title:
--   Local Tate duality over open subgroups of G_{ℚ_q}
-- statement:
--   Fix a prime $p$ and a prime $q$, and let $S$ be a subgroup of $G_q = \mathrm{Aut}_{\mathbb{Q}_p\text{-alg}}$ of the chosen algebraic closure of $\mathbb{Q}_q$, assumed open in the sense that some finite extension $F_0/\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ has the pullback along `primeLocalToGlobal q` of its fixing subgroup contained in $S$. Let $M$ be a finite-dimensional $\mathbb{Z}/p$-linear representation of $S$ which is smooth in the sense that each $m \in M$ is fixed by all $s \in S$ whose image under the global level map lies in the fixing subgroup of some finite extension $F/\mathbb{Q}$. Write $\chi$ for the mod-$p$ cyclotomic character composed with the global level map, $N$ for the restriction to $S$ of the rank-one representation given by the trivial representation twisted by $\chi$, and $D = M^{\vee}(\chi|_S)$ for the $\chi$-twist of the dual representation; the pairing $M \times D \to N$ is the canonical evaluation `Module.Dual.eval`. Here $H^1_{\mathrm{cts}}$ denotes the image in $H^1$ of the level $1$-cocycles and $H^2_{\mathrm{cts}}$ the quotient of the level $2$-cocycles by the level $2$-coboundaries. Let $\mathrm{inv} \colon H^2_{\mathrm{cts}}(S,N) \to \mathbb{Z}/p$ be a bijective linear map, and let $\theta_0 \colon M^S \to H^2_{\mathrm{cts}}(S,D)^{\vee}$, $\theta_1 \colon H^1_{\mathrm{cts}}(S,M) \to H^1_{\mathrm{cts}}(S,D)^{\vee}$, $\theta_2 \colon H^2_{\mathrm{cts}}(S,M) \to (D^S)^{\vee}$ be linear maps satisfying `IsTheta0`, `IsTheta1`, `IsTheta2` for this pairing and $\mathrm{inv}$: that is, $\theta_0(m)[z] = \mathrm{inv}[e]$ whenever the level $2$-cocycle $e$ of $N$ is the cochain $(s,t) \mapsto \langle m, z(s,t)\rangle$; $\theta_1[f][g] = \mathrm{inv}[e]$ whenever $f,g$ are level-constant $1$-cocycles of $M$, $D$ and $e$ is their cup cochain $(s,t) \mapsto \langle f(s), D(s)g(t)\rangle$; and $\theta_2[z](d) = \mathrm{inv}[e]$ whenever $e$ is the cochain $(s,t)\mapsto \langle z(s,t), d\rangle$. Then $\theta_0$, $\theta_1$ and $\theta_2$ are all bijective.
--
--   This is local Tate duality in the three bidegrees $0,1,2$ for finite smooth $\mathbb{F}_p$-representations of the Galois group of the finite extension of $\mathbb{Q}_q$ cut out by $S$, formulated as the bijectivity of any triple of maps compatible with the evaluation cup pairing and a chosen trivialisation of $H^2_{\mathrm{cts}}(S,\mathbb{F}_p(\chi))$. It feeds the local Euler-characteristic count [`groupCohomology.finrank_continuousClasses_eq_invariants_add_continuousH2_add_finrank_of_primeLocal`](thm.html#groupCohomology.finrank_continuousClasses_eq_invariants_add_continuousH2_add_finrank_of_primeLocal), which supplies the local dimension bookkeeping in the Selmer-group estimates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_bijective_theta_dualTwist_of_isOpen.lean

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

theorem groupCohomology.bijective_theta_dualTwist_of_isOpen
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes)
    (S : Subgroup (primeLocalGaloisGroup q))
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S)
    (M : Rep.{0} (ZMod p) S) [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : S, ((primeLocalToGlobal q).comp S.subtype) s ∈ F.fixingSubgroup → M.ρ s m = m)
    (inv : continuousH2 ((primeLocalToGlobal q).comp S.subtype) (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) →ₗ[ZMod p] ZMod p)
    (hinv : Function.Bijective inv)
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

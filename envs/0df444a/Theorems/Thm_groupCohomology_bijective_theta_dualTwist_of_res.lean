-- Prove2me | Theorems.Thm_groupCohomology_bijective_theta_dualTwist_of_res
-- name    : groupCohomology.bijective_theta_dualTwist_of_res
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/19f48950-8dc9-5824-9dac-3eaabc3daea4
-- title:
--   Descent of local duality along a subgroup of index prime to p
-- statement:
--   Fix a prime $p$ and a prime $q$, and let $G_q$ denote `primeLocalGaloisGroup q`, the group of $\mathbb{Q}_q$-automorphisms of the algebraic closure `PadicAlgCl q`, equipped with the homomorphism $r =$ `primeLocalToGlobal q` to $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ obtained by restricting to the algebraic numbers; write $\chi =$ `cycloChar p` $\circ\, r$ for the mod $p$ cyclotomic character pulled back along $r$, and $N =$ `ofChar` $\chi$ for the one-dimensional $\mathbb{F}_p$-representation given by twisting the trivial representation by $\chi$. Let $S \le G_q$ be a subgroup of finite index whose index is invertible in $\mathbb{Z}/p$, and assume $S$ contains the preimage under $r$ of the fixing subgroup of some finite extension $F_0/\mathbb{Q}$ inside $\overline{\mathbb{Q}}$. Let $M$ be a finite-dimensional $\mathbb{F}_p$-representation of $G_q$ each of whose vectors is fixed by the preimage under $r$ of the fixing subgroup of some finite extension of $\mathbb{Q}$, and let $D = M^{\vee}(\chi) =$ `M.dualTwist` $\chi$ be the dual representation twisted by $\chi$, paired with $M$ into $N$ by the evaluation map `Module.Dual.eval`. Here $H^2_{\mathrm{cts}}(r, -)$ denotes `continuousH2`, the quotient of the module of level $2$-cocycles by those which are level $2$-coboundaries, and $H^1_{\mathrm{cts}}(r, -)$ denotes `continuousH1`, the image in $H^1$ of the level $1$-cocycles. Let $\mathrm{inv} \colon H^2_{\mathrm{cts}}(r, N) \to \mathbb{Z}/p$ be a bijective linear map. Assume the following duality over $S$: for every bijective linear functional $\mathrm{inv}_S$ on $H^2_{\mathrm{cts}}(r|_S, \mathrm{Res}_S N)$ and every triple of maps $\theta_0, \theta_1, \theta_2$ satisfying `IsTheta0`, `IsTheta1`, `IsTheta2` for the restricted data $(\mathrm{Res}_S M, \mathrm{Res}_S D, \text{evaluation}, \mathrm{inv}_S)$, all three are bijective. Then, given maps $\theta_0 \colon M^{G_q} \to H^2_{\mathrm{cts}}(r, D)^{\vee}$, $\theta_1 \colon H^1_{\mathrm{cts}}(r, M) \to H^1_{\mathrm{cts}}(r, D)^{\vee}$ and $\theta_2 \colon H^2_{\mathrm{cts}}(r, M) \to (D^{G_q})^{\vee}$ satisfying `IsTheta0`, `IsTheta1` and `IsTheta2` respectively for the evaluation pairing and $\mathrm{inv}$ — that is, characterised on cocycles by $\theta_0(m)[z] = \mathrm{inv}[\,(s,t) \mapsto \langle m, z(s,t)\rangle\,]$, $\theta_1$ computed through the cup cochain $(s,t) \mapsto \langle f(s), \rho_s g(t)\rangle$ of level-constant $1$-cocycles, and $\theta_2[z](d) = \mathrm{inv}[\,(s,t) \mapsto \langle z(s,t), d\rangle\,]$ — all three of $\theta_0$, $\theta_1$, $\theta_2$ are bijective.
--
--   This is the descent step in the proof of local Tate duality mod $p$ for the Galois group of $\mathbb{Q}_q$: duality for the restriction to a finite-index subgroup $S$ of index prime to $p$ (in practice the fixed group of a $p$-Sylow situation) is transported back to the full local Galois group by coinduction together with the unit and trace maps, whose composite is multiplication by $[G_q : S]$. It is used by [`groupCohomology.bijective_theta_dualTwist_of_primeLocal`](thm.html#groupCohomology.bijective_theta_dualTwist_of_primeLocal), which establishes the duality isomorphisms at the place $q$ used in the local computations of the deformation-theoretic argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_bijective_theta_dualTwist_of_res.lean

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

theorem groupCohomology.bijective_theta_dualTwist_of_res
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes)
    (S : Subgroup (primeLocalGaloisGroup q)) [S.FiniteIndex] (hSp : IsUnit ((S.index : ℕ) : ZMod p))
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S)
    (M : Rep (ZMod p) (primeLocalGaloisGroup q)) [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, primeLocalToGlobal q s ∈ F.fixingSubgroup → M.ρ s m = m)
    (inv : continuousH2 (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) →ₗ[ZMod p] ZMod p)
    (hinv : Function.Bijective inv)
    (hres : ∀ (invS : continuousH2 ((primeLocalToGlobal q).comp S.subtype)
        (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) →ₗ[ZMod p] ZMod p),
      Function.Bijective invS →
      ∀ (θ₀ : (Rep.res S.subtype M).ρ.invariants →ₗ[ZMod p] Module.Dual (ZMod p)
          (continuousH2 ((primeLocalToGlobal q).comp S.subtype) (Rep.res S.subtype (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q)))))),
        IsTheta0 ((primeLocalToGlobal q).comp S.subtype)
          (Module.Dual.eval (ZMod p) M : Rep.res S.subtype M →ₗ[ZMod p]
            Rep.res S.subtype (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q))) →ₗ[ZMod p]
            Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) invS θ₀ →
      ∀ (θ₁ : continuousH1 ((primeLocalToGlobal q).comp S.subtype) (Rep.res S.subtype M) →ₗ[ZMod p] Module.Dual (ZMod p)
          (continuousH1 ((primeLocalToGlobal q).comp S.subtype) (Rep.res S.subtype (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q)))))),
        IsTheta1 ((primeLocalToGlobal q).comp S.subtype)
          (Module.Dual.eval (ZMod p) M : Rep.res S.subtype M →ₗ[ZMod p]
            Rep.res S.subtype (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q))) →ₗ[ZMod p]
            Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) invS θ₁ →
      ∀ (θ₂ : continuousH2 ((primeLocalToGlobal q).comp S.subtype) (Rep.res S.subtype M) →ₗ[ZMod p] Module.Dual (ZMod p)
          (Rep.res S.subtype (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q)))).ρ.invariants),
        IsTheta2 ((primeLocalToGlobal q).comp S.subtype)
          (Module.Dual.eval (ZMod p) M : Rep.res S.subtype M →ₗ[ZMod p]
            Rep.res S.subtype (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q))) →ₗ[ZMod p]
            Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) invS θ₂ →
      Function.Bijective θ₀ ∧ Function.Bijective θ₁ ∧ Function.Bijective θ₂)
    (θ₀ : M.ρ.invariants →ₗ[ZMod p] Module.Dual (ZMod p)
      (continuousH2 (primeLocalToGlobal q) (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q)))))
    (hθ₀ : IsTheta0 (primeLocalToGlobal q)
      (Module.Dual.eval (ZMod p) M : M →ₗ[ZMod p] M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q)) →ₗ[ZMod p]
        ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) inv θ₀)
    (θ₁ : continuousH1 (primeLocalToGlobal q) M →ₗ[ZMod p] Module.Dual (ZMod p)
      (continuousH1 (primeLocalToGlobal q) (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q)))))
    (hθ₁ : IsTheta1 (primeLocalToGlobal q)
      (Module.Dual.eval (ZMod p) M : M →ₗ[ZMod p] M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q)) →ₗ[ZMod p]
        ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) inv θ₁)
    (θ₂ : continuousH2 (primeLocalToGlobal q) M →ₗ[ZMod p] Module.Dual (ZMod p)
      (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q))).ρ.invariants)
    (hθ₂ : IsTheta2 (primeLocalToGlobal q)
      (Module.Dual.eval (ZMod p) M : M →ₗ[ZMod p] M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q)) →ₗ[ZMod p]
        ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) inv θ₂) :
    Function.Bijective θ₀ ∧ Function.Bijective θ₁ ∧ Function.Bijective θ₂ := by sorry

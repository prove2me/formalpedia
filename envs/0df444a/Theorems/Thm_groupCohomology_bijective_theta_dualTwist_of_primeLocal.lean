-- Prove2me | Theorems.Thm_groupCohomology_bijective_theta_dualTwist_of_primeLocal
-- name    : groupCohomology.bijective_theta_dualTwist_of_primeLocal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/03c7639d-1479-51ae-b8ca-383878895934
-- title:
--   Local Tate duality at q in all three degrees
-- statement:
--   Fix a prime $p$ and a prime $q$, and write $G_q$ for `primeLocalGaloisGroup q`, the group of $\mathbb{Q}_p$-algebra automorphisms — for $\mathbb{Q}_{q}$-algebra automorphisms — of the chosen algebraic closure `PadicAlgCl q` of $\mathbb{Q}_{q}$, and $r =$ `primeLocalToGlobal q` for the homomorphism $G_q \to \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ obtained by restricting scalars to $\mathbb{Q}$ and then restricting to the algebraic closure of $\mathbb{Q}$. Let $M$ be a representation of $G_q$ over $\mathbb{Z}/p$, finite-dimensional, and smooth in the sense that each $m \in M$ is fixed by all $s$ with $r(s)$ in the fixing subgroup of some finite extension $F$ of $\mathbb{Q}$ inside $\overline{\mathbb{Q}}$. Write $\chi =$ `cycloChar p` $\circ\, r$ for the mod $p$ cyclotomic character pulled back along $r$, $N =$ `ofChar` $\chi$ for the line $\mathbb{Z}/p$ with $G_q$ acting by $\chi$, and $D = M^{\vee}(\chi) =$ `M.dualTwist` $\chi$ for the linear dual of $M$ with the dual action scaled by $\chi$. Here $H^1_{\mathrm{cts}}(-) =$ `continuousH1` $r\,(-)$ is the image in $H^1$ of the level $1$-cocycles, and $H^2_{\mathrm{cts}}(-) =$ `continuousH2` $r\,(-)$ is the quotient of the level $2$-cocycles by the level $2$-coboundaries among them. Assume given a $\mathbb{Z}/p$-linear $\mathrm{inv} \colon H^2_{\mathrm{cts}}(N) \to \mathbb{Z}/p$ which is bijective, and let $\varphi \colon M \to D \to N$ be the evaluation pairing `Module.Dual.eval`. Let there be given linear maps $\theta_0 \colon M^{G_q} \to H^2_{\mathrm{cts}}(D)^{*}$, $\theta_1 \colon H^1_{\mathrm{cts}}(M) \to H^1_{\mathrm{cts}}(D)^{*}$ and $\theta_2 \colon H^2_{\mathrm{cts}}(M) \to (D^{G_q})^{*}$ satisfying the cocycle-level normalisations `IsTheta0`, `IsTheta1`, `IsTheta2` with respect to $\varphi$ and $\mathrm{inv}$: namely $\theta_0(m)([z]) = \mathrm{inv}([e])$ whenever $e(s,t) = \varphi(m)(z(s,t))$ for all $(s,t)$, with $z$ a level $2$-cocycle in $D$ and $e$ one in $N$; $\theta_1([f])([g]) = \mathrm{inv}([e])$ whenever $e(s,t) = \varphi(f(s))(D.\rho(s)\,g(t))$, for level-constant $1$-cocycles $f$ in $M$ and $g$ in $D$; and $\theta_2([z])(d) = \mathrm{inv}([e])$ whenever $e(s,t) = \varphi(z(s,t))(d)$, for $z$ a level $2$-cocycle in $M$ and $d \in D^{G_q}$. The conclusion is that $\theta_0$, $\theta_1$ and $\theta_2$ are all bijective.
--
--   This is local Tate duality at the place $q$, in degrees $0$, $1$ and $2$ simultaneously, for the continuous cohomology of finite smooth mod $p$ modules as used throughout this development; the pairing is the evaluation pairing against the Cartier dual $M^{\vee}(\chi)$, normalised by an invariant map on $H^2_{\mathrm{cts}}(G_q, \mathbb{Z}/p(\chi))$. It feeds the construction of local duality packages and the computation of local conditions for dual Selmer groups, in particular the surjectivity statements used to compare Selmer groups at bad primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_bijective_theta_dualTwist_of_primeLocal.lean

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

theorem groupCohomology.bijective_theta_dualTwist_of_primeLocal
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes)
    (M : Rep (ZMod p) (primeLocalGaloisGroup q)) [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, primeLocalToGlobal q s ∈ F.fixingSubgroup → M.ρ s m = m)
    (inv : continuousH2 (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) →ₗ[ZMod p] ZMod p)
    (hinv : Function.Bijective inv)
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

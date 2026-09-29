-- Prove2me | Theorems.Thm_groupCohomology_bijective_theta1_of_trivial_line_of_isOpen
-- name    : groupCohomology.bijective_theta1_of_trivial_line_of_isOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/0e71cb29-b1fc-5004-a2e7-31d081e94d83
-- title:
--   Local duality in degree one for a trivial line
-- statement:
--   Let $p$ be a prime and let $q$ be a prime; write $G_q$ for `primeLocalGaloisGroup q`, the Galois group of an algebraic closure of $\mathbb{Q}_q$ over $\mathbb{Q}_q$, and let $\iota =$ `primeLocalToGlobal q` be the homomorphism $G_q \to \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ obtained by restricting scalars to $\mathbb{Q}$ and then restricting to the algebraic closure of $\mathbb{Q}$. Let $S \le G_q$ be a subgroup such that, for some intermediate field $F_0$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ finite over $\mathbb{Q}$, the $\iota$-preimage of the fixing subgroup of $F_0$ lies in $S$, and assume the mod-$p$ cyclotomic character `cycloChar p` takes the value $1$ at $\iota(s)$ for every $s \in S$. Put $r = \iota \circ (S \hookrightarrow G_q)$ and $\chi =$ `cycloChar p` $\circ\, r$. Let $A$ be a representation of $S$ over $\mathbb{Z}/p$ on which $S$ acts trivially and with $\dim_{\mathbb{Z}/p} A = 1$, and let $A^{\vee}(\chi) =$ `A.dualTwist` $\chi$ be the $\mathbb{Z}/p$-dual of $A$ with the dual action multiplied by $\chi$, while `ofChar` $\chi$ is the line $\mathbb{Z}/p$ with $s$ acting by $\chi(s)$. Here $\mathrm{continuousH}^1$ of a representation $M$ denotes the image in $H^1(S,M)$ of the level-constant $1$-cocycles, and $\mathrm{continuousH}^2$ denotes the level $2$-cocycles modulo those that are level coboundaries. Assume given a $\mathbb{Z}/p$-linear bijection $\mathrm{inv}_S$ from $\mathrm{continuousH}^2(r, \mathrm{ofChar}\,\chi)$ to $\mathbb{Z}/p$, and a $\mathbb{Z}/p$-linear map $\theta_1$ from $\mathrm{continuousH}^1(r, A)$ to the dual of $\mathrm{continuousH}^1(r, A^{\vee}(\chi))$ satisfying `IsTheta1` for the evaluation pairing $A \times A^{\vee}(\chi) \to \mathrm{ofChar}\,\chi$ and $\mathrm{inv}_S$: for all level-constant $1$-cocycles $f$ with values in $A$ and $g$ with values in $A^{\vee}(\chi)$, and every level $2$-cocycle $e$ whose underlying function is $(s,t) \mapsto \langle f(s), \rho(s) g(t)\rangle$, the value of $\theta_1[f]$ at $[g]$ equals $\mathrm{inv}_S$ of the class of $e$. Then $\theta_1$ is bijective.
--
--   This is the degree-one case of local Tate duality in the situation of a trivial one-dimensional coefficient module over an open subgroup of a local Galois group on which the mod-$p$ cyclotomic character is trivial, with the cup-product pairing normalised by the given invariant map. It is the base case from which [`groupCohomology.bijective_theta_dualTwist_of_sylowLevel`](thm.html#groupCohomology.bijective_theta_dualTwist_of_sylowLevel) obtains perfectness of the local duality pairing for general coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_bijective_theta1_of_trivial_line_of_isOpen.lean

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

theorem groupCohomology.bijective_theta1_of_trivial_line_of_isOpen {p : ℕ} [Fact p.Prime] (q : Nat.Primes)
    (S : Subgroup (primeLocalGaloisGroup q))
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S)
    (hχS : ∀ s : primeLocalGaloisGroup q, s ∈ S → (cycloChar p) (primeLocalToGlobal q s) = 1)
    (A : Rep (ZMod p) S) (hA : ∀ (s : S) (a : A), A.ρ s a = a) (hA1 : finrank (ZMod p) A = 1)
    (invS : continuousH2 ((primeLocalToGlobal q).comp S.subtype)
      (ofChar (k := ZMod p) (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) →ₗ[ZMod p] ZMod p)
    (hinvS : Function.Bijective invS)
    (θ₁ : continuousH1 ((primeLocalToGlobal q).comp S.subtype) A →ₗ[ZMod p] Module.Dual (ZMod p)
      (continuousH1 ((primeLocalToGlobal q).comp S.subtype) (A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))))
    (hθ₁ : IsTheta1 ((primeLocalToGlobal q).comp S.subtype)
      (Module.Dual.eval (ZMod p) A : A →ₗ[ZMod p] A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)
        →ₗ[ZMod p] ofChar (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) invS θ₁) :
    Function.Bijective θ₁ := by sorry

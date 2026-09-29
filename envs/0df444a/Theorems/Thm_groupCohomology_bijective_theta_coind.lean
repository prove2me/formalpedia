-- Prove2me | Theorems.Thm_groupCohomology_bijective_theta_coind
-- name    : groupCohomology.bijective_theta_coind
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/f4adbdc0-5e3e-50a6-99e0-ce9f247d817c
-- title:
--   Shapiro transport of duality to a coinduced pair
-- statement:
--   Let $k$ be a commutative ring, $G$ a group, $r : G \to \operatorname{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ a homomorphism into the automorphism group of an algebraic closure of $\mathbb Q$, and $U \le G$ a subgroup of finite index such that for some finite-dimensional intermediate field $F_0/\mathbb Q$ inside $\overline{\mathbb Q}$ the $r$-preimage of the fixing subgroup of $F_0$ lies in $U$. Let $N_U, D_U$ be $k$-linear representations of $U$ and $N_\mu$ one of $G$, and let $\varphi_U : N_U \times D_U \to \operatorname{Res}_U N_\mu$ be $k$-bilinear and equivariant, i.e. $\varphi_U(\rho(s)a, \rho(s)b) = \rho(s)\varphi_U(a,b)$ for $s \in U$; assume $D_U$ smooth, in the sense that each $x \in D_U$ is fixed by every $s \in U$ with $r(s)$ in the fixing subgroup of some finite-dimensional intermediate field. Fix $k$-linear functionals $\mathrm{inv}_U$ on $\operatorname{continuousH2}(r|_U, \operatorname{Res}_U N_\mu)$ — the quotient of level $2$-cocycles by level $2$-coboundaries — and $\mathrm{inv}_G$ on $\operatorname{continuousH2}(r, N_\mu)$, and a morphism $\tau : \operatorname{coind}_U^G \operatorname{Res}_U N_\mu \to N_\mu$ of $G$-representations which is compatible with them along evaluation at $1$: whenever a level $2$-cocycle $w$ for $G$ in the coinduced module and a level $2$-cocycle $w_1$ for $U$ in $\operatorname{Res}_U N_\mu$ satisfy $w_1(s,t) = w(s,t)(1)$ for all $s,t \in U$, then $\mathrm{inv}_G$ of the image of $[w]$ under $\operatorname{continuousH2MapHom}\, r\, \tau$ equals $\mathrm{inv}_U[w_1]$. Let $\Psi : \operatorname{coind} N_U \times \operatorname{coind} D_U \to N_\mu$ be $k$-bilinear and such that $\Psi(f,g) = \tau(w)$ whenever $w$ satisfies $w(h) = \varphi_U(f(h), g(h))$ for all $h \in G$. Let $\theta_0, \theta_1, \theta_2$ be the duality maps for $(\varphi_U, \mathrm{inv}_U)$ over $U$: $\theta_0$ sends an invariant $m$ of $N_U$ to the functional $[z] \mapsto \mathrm{inv}_U[e]$ on $\operatorname{continuousH2}(r|_U, D_U)$ whenever $e(s,t) = \varphi_U(m, z(s,t))$; $\theta_1$ sends the class of a level-constant $1$-cocycle $f$ in $N_U$ to the functional on $\operatorname{continuousH1}$ taking the class of a level-constant $1$-cocycle $g$ in $D_U$ to $\mathrm{inv}_U[e]$ whenever $e$ is the cup cochain $(s,t) \mapsto \varphi_U(f(s), \rho(s)g(t))$; and $\theta_2$ sends $[z]$, for $z$ a level $2$-cocycle in $N_U$, to the functional $d \mapsto \mathrm{inv}_U[e]$ on the invariants of $D_U$ whenever $e(s,t) = \varphi_U(z(s,t), d)$. Let $\Theta_0, \Theta_1, \Theta_2$ be the corresponding maps for $(\Psi, \mathrm{inv}_G)$ over $G$ with $\operatorname{coind} N_U$ and $\operatorname{coind} D_U$ in place of $N_U, D_U$. If $\theta_0, \theta_1, \theta_2$ are all bijective, then so are $\Theta_0, \Theta_1, \Theta_2$.
--
--   This is the transport of a perfect duality triple along Shapiro's isomorphism: perfectness of the degree $0,1,2$ duality maps for a pairing over a finite-index subgroup $U$, cut out by a finite-dimensional intermediate field, yields perfectness for the coinduced pairing over $G$. It is used by [`groupCohomology.bijective_theta_dualTwist_of_res`](thm.html#groupCohomology.bijective_theta_dualTwist_of_res) and [`groupCohomology.bijective_theta_dualTwist_of_res_of_isOpen`](thm.html#groupCohomology.bijective_theta_dualTwist_of_res_of_isOpen) to obtain duality for representations over $G$ from duality over a subgroup.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_bijective_theta_coind.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_CupProduct
import Definitions.Def_GroupCohomology_ContinuousDuality

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology

theorem groupCohomology.bijective_theta_coind
    {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (U : Subgroup G) [U.FiniteIndex]
    (hU : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap r ≤ U)
    {NU DU : Rep.{u} k U} {Nμ : Rep.{u} k G}
    (φU : NU →ₗ[k] DU →ₗ[k] Rep.res U.subtype Nμ) (hφU : Rep.IsEquivariantBilinear NU DU (Rep.res U.subtype Nμ) φU)
    (hsmDU : ∀ x : DU, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : U, (r.comp U.subtype) s ∈ F.fixingSubgroup → DU.ρ s x = x)
    (invU : continuousH2 (r.comp U.subtype) (Rep.res U.subtype Nμ) →ₗ[k] k) (invG : continuousH2 r Nμ →ₗ[k] k)
    (τ : Rep.coind U.subtype (Rep.res U.subtype Nμ) ⟶ Nμ)
    (hinv : ∀ (w : levelCocycles₂ r (Rep.coind U.subtype (Rep.res U.subtype Nμ)))
      (w₁ : levelCocycles₂ (r.comp U.subtype) (Rep.res U.subtype Nμ)),
      (∀ s t : U, (w₁ : U × U → Nμ) (s, t)
        = ((w : G × G → Rep.coind U.subtype (Rep.res U.subtype Nμ)) ((s : G), (t : G)) : G → Nμ) 1) →
      invG (continuousH2MapHom r τ (continuousH2π r _ w)) = invU (continuousH2π _ _ w₁))
    (Ψ : Rep.coind U.subtype NU →ₗ[k] Rep.coind U.subtype DU →ₗ[k] Nμ)
    (hΨ : ∀ (f : Rep.coind U.subtype NU) (g : Rep.coind U.subtype DU) (w : Rep.coind U.subtype (Rep.res U.subtype Nμ)),
      (∀ h : G, (w : G → Nμ) h = φU ((f : G → NU) h) ((g : G → DU) h)) → Ψ f g = τ.hom w)
    (θ₀ : NU.ρ.invariants →ₗ[k] Module.Dual k (continuousH2 (r.comp U.subtype) DU)) (hθ₀ : IsTheta0 (r.comp U.subtype) φU invU θ₀)
    (θ₁ : continuousH1 (r.comp U.subtype) NU →ₗ[k] Module.Dual k (continuousH1 (r.comp U.subtype) DU))
    (hθ₁ : IsTheta1 (r.comp U.subtype) φU invU θ₁)
    (θ₂ : continuousH2 (r.comp U.subtype) NU →ₗ[k] Module.Dual k DU.ρ.invariants) (hθ₂ : IsTheta2 (r.comp U.subtype) φU invU θ₂)
    (Θ₀ : (Rep.coind U.subtype NU).ρ.invariants →ₗ[k] Module.Dual k (continuousH2 r (Rep.coind U.subtype DU)))
    (hΘ₀ : IsTheta0 r Ψ invG Θ₀)
    (Θ₁ : continuousH1 r (Rep.coind U.subtype NU) →ₗ[k] Module.Dual k (continuousH1 r (Rep.coind U.subtype DU)))
    (hΘ₁ : IsTheta1 r Ψ invG Θ₁)
    (Θ₂ : continuousH2 r (Rep.coind U.subtype NU) →ₗ[k] Module.Dual k (Rep.coind U.subtype DU).ρ.invariants)
    (hΘ₂ : IsTheta2 r Ψ invG Θ₂)
    (hU' : Function.Bijective θ₀ ∧ Function.Bijective θ₁ ∧ Function.Bijective θ₂) :
    Function.Bijective Θ₀ ∧ Function.Bijective Θ₁ ∧ Function.Bijective Θ₂ := by sorry

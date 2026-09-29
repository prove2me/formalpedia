-- Prove2me | Theorems.Thm_groupCohomology_bijective_theta_of_retract
-- name    : groupCohomology.bijective_theta_of_retract
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/efd93057-6c24-5141-a140-7885dc289936
-- title:
--   Duality maps descend to retracts of dual pairs
-- statement:
--   Let $k$ be a commutative ring, $G$ a group and $r \colon G \to \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ a homomorphism into the automorphism group of `AlgebraicClosure ℚ` over $\mathbb{Q}$, used throughout to define the level ("continuous") subobjects. Let $M, D, M_1, D_1, N$ be $k$-linear representations of $G$, let $\varphi \colon M \times D \to N$ and $\varphi_1 \colon M_1 \times D_1 \to N$ be $k$-bilinear maps, with $\varphi_1$ assumed $G$-equivariant in the sense that $\varphi_1(M_1.\rho\,g\,x, D_1.\rho\,g\,y) = N.\rho\,g\,(\varphi_1(x,y))$ for all $g$. Assume $(M,D,\varphi)$ is a retract of $(M_1,D_1,\varphi_1)$: morphisms $a \colon M \to M_1$, $b \colon M_1 \to M$ with $b \circ a = \mathrm{id}_M$ pointwise, morphisms $a' \colon D_1 \to D$, $b' \colon D \to D_1$ with $a' \circ b' = \mathrm{id}_D$ pointwise, and adjointness $\varphi_1(a m, y) = \varphi(m, a' y)$ and $\varphi(b x, d) = \varphi_1(x, b' d)$. Assume further that $D$ is smooth for $r$: every $x \in D$ is fixed by all $s \in G$ with $r(s)$ in the fixing subgroup of some finite extension $F/\mathbb{Q}$ inside $\overline{\mathbb{Q}}$. Fix a $k$-linear functional $\mathrm{inv}$ on $H^2_{\mathrm{cts}}(r,N)$, the quotient of the level $2$-cocycles by the level $2$-coboundaries. Let $\theta_0 \colon M^G \to H^2_{\mathrm{cts}}(r,D)^\vee$, $\theta_1 \colon H^1_{\mathrm{cts}}(r,M) \to H^1_{\mathrm{cts}}(r,D)^\vee$ (the continuous $H^1$ being the image of the level $1$-cocycles in $H^1$) and $\theta_2 \colon H^2_{\mathrm{cts}}(r,M) \to (D^G)^\vee$ satisfy `IsTheta0`, `IsTheta1`, `IsTheta2` for $\varphi$ and $\mathrm{inv}$, that is: $\theta_0(m)$ of the class of a level $2$-cocycle $z$ equals $\mathrm{inv}$ of the class of any level $2$-cocycle $e$ with $e(s,t) = \varphi(m, z(s,t))$; $\theta_1$ applied to the classes of level-constant $1$-cocycles $f$, $g$ equals $\mathrm{inv}$ of the class of any level $2$-cocycle $e$ with $e(s,t) = \varphi(f(s), D.\rho\,s\,(g(t)))$; and $\theta_2$ of the class of $z$ at $d \in D^G$ equals $\mathrm{inv}$ of the class of any level $2$-cocycle $e$ with $e(s,t) = \varphi(z(s,t), d)$. Let $\Theta_0, \Theta_1, \Theta_2$ satisfy the same three conditions for $\varphi_1$ and the same $\mathrm{inv}$. Then if $\Theta_0$, $\Theta_1$ and $\Theta_2$ are all bijective, so are $\theta_0$, $\theta_1$ and $\theta_2$.
--
--   This is the dévissage step by which a local duality statement for a pair of representations with a pairing is transported to a direct summand, the three duality maps in degrees $0$, $1$, $2$ being retracts of their counterparts in the category of arrows. It is used in the reduction of the duality theorem to the case handled directly, via [`groupCohomology.bijective_theta_dualTwist_of_res`](thm.html#groupCohomology.bijective_theta_dualTwist_of_res) and [`groupCohomology.bijective_theta_dualTwist_of_res_of_isOpen`](thm.html#groupCohomology.bijective_theta_dualTwist_of_res_of_isOpen).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_bijective_theta_of_retract.lean

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

theorem groupCohomology.bijective_theta_of_retract
    {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    {M D M₁ D₁ N : Rep.{u} k G}
    (φ : M →ₗ[k] D →ₗ[k] N)
    (φ₁ : M₁ →ₗ[k] D₁ →ₗ[k] N) (hφ₁ : Rep.IsEquivariantBilinear M₁ D₁ N φ₁)
    (a : M ⟶ M₁) (b : M₁ ⟶ M) (hba : ∀ m : M, b.hom (a.hom m) = m)
    (a' : D₁ ⟶ D) (b' : D ⟶ D₁) (hab' : ∀ x : D, a'.hom (b'.hom x) = x)
    (ha : ∀ (m : M) (y : D₁), φ₁ (a.hom m) y = φ m (a'.hom y))
    (hb : ∀ (x : M₁) (d : D), φ (b.hom x) d = φ₁ x (b'.hom d))
    (hsmD : ∀ x : D, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → D.ρ s x = x)
    (inv : continuousH2 r N →ₗ[k] k)
    (θ₀ : M.ρ.invariants →ₗ[k] Module.Dual k (continuousH2 r D)) (hθ₀ : IsTheta0 r φ inv θ₀)
    (θ₁ : continuousH1 r M →ₗ[k] Module.Dual k (continuousH1 r D)) (hθ₁ : IsTheta1 r φ inv θ₁)
    (θ₂ : continuousH2 r M →ₗ[k] Module.Dual k D.ρ.invariants) (hθ₂ : IsTheta2 r φ inv θ₂)
    (Θ₀ : M₁.ρ.invariants →ₗ[k] Module.Dual k (continuousH2 r D₁)) (hΘ₀ : IsTheta0 r φ₁ inv Θ₀)
    (Θ₁ : continuousH1 r M₁ →ₗ[k] Module.Dual k (continuousH1 r D₁)) (hΘ₁ : IsTheta1 r φ₁ inv Θ₁)
    (Θ₂ : continuousH2 r M₁ →ₗ[k] Module.Dual k D₁.ρ.invariants) (hΘ₂ : IsTheta2 r φ₁ inv Θ₂)
    (h₁ : Function.Bijective Θ₀ ∧ Function.Bijective Θ₁ ∧ Function.Bijective Θ₂) :
    Function.Bijective θ₀ ∧ Function.Bijective θ₁ ∧ Function.Bijective θ₂ := by sorry

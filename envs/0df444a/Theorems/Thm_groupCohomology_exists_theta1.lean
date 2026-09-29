-- Prove2me | Theorems.Thm_groupCohomology_exists_theta1
-- name    : groupCohomology.exists_theta1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/f7d4f9b0-8b23-5c85-85bb-127c5871cd17
-- title:
--   Existence of the bidegree-(1,1) cup-product duality map
-- statement:
--   Let $k$ be a commutative ring, $G$ a group, and $r \colon G \to \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ a group homomorphism into the automorphisms of $\overline{\mathbb{Q}}$ over $\mathbb{Q}$. Let $M$, $D$, $N$ be $k$-linear representations of $G$ and let $\varphi \colon M \to D \to N$ be $k$-bilinear and equivariant in the sense of [`Rep.IsEquivariantBilinear`](def/GroupCohomology_CupProduct.html#L13), i.e. $\varphi(\rho_M(g)a, \rho_D(g)b) = \rho_N(g)\varphi(a,b)$ for all $g \in G$, $a \in M$, $b \in D$. Assume $D$ is smooth for $r$: for every $x \in D$ there is an intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, with $\rho_D(s)x = x$ whenever $r(s)$ lies in the fixing subgroup of $F$. Let $\mathrm{inv}$ be a $k$-linear functional on `continuousH2 r N`, the quotient of the submodule `levelCocycles₂ r N` of $2$-cocycles by its intersection with `levelCoboundaries₂ r N`. Then there exists a $k$-linear map $\theta_1$ from `continuousH1 r M`, the image under `H1π` of the level cocycles `levelCocycles₁ r M` inside $H^1(G,M)$, to the $k$-dual of `continuousH1 r D`, satisfying `IsTheta1 r φ inv`: for all $1$-cocycles $f$ of $M$ and $g$ of $D$ satisfying `IsLevelConstant₁ r`, and every $e \in$ `levelCocycles₂ r N` whose underlying function is the cup cochain $(s,t) \mapsto \varphi(f(s))(\rho_D(s)g(t))$, the value of $\theta_1$ at the class of $f$ evaluated at the class of $g$ equals $\mathrm{inv}$ of the class of $e$.
--
--   This is the existence half of local duality in bidegree $(1,1)$: the cup product followed by an invariant functional on continuous $H^2$ descends to a pairing between the continuous $H^1$ of $M$ and that of $D$. It is the input to the statements asserting bijectivity of the resulting duality maps, such as [`groupCohomology.bijective_theta_dualTwist_of_res`](thm.html#groupCohomology.bijective_theta_dualTwist_of_res) and its variants under openness or Sylow-level hypotheses.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_theta1.lean

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

theorem groupCohomology.exists_theta1
    {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    {M D N : Rep.{u} k G} (φ : M →ₗ[k] D →ₗ[k] N) (hφ : Rep.IsEquivariantBilinear M D N φ)
    (hsmD : ∀ x : D, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → D.ρ s x = x)
    (inv : continuousH2 r N →ₗ[k] k) :
    ∃ θ₁ : continuousH1 r M →ₗ[k] Module.Dual k (continuousH1 r D), IsTheta1 r φ inv θ₁ := by sorry

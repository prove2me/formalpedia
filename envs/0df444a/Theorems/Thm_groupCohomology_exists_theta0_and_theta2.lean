-- Prove2me | Theorems.Thm_groupCohomology_exists_theta0_and_theta2
-- name    : groupCohomology.exists_theta0_and_theta2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/c81c0c02-eb69-5a41-8e75-5c2784c9520f
-- title:
--   Existence of θ⁰ and θ² for an equivariant pairing
-- statement:
--   Fix a universe-$u$ commutative ring $k$ and a group $G$, together with a homomorphism $r \colon G \to \operatorname{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ (used only through the level conditions defining the continuous cochain groups). Let $M$, $D$, $N$ be objects of `Rep k G`, let $\varphi \colon M \to_{k} (D \to_{k} N)$ be a $k$-bilinear map, and assume [`Rep.IsEquivariantBilinear`](def/GroupCohomology_CupProduct.html#L13), i.e. $\varphi(\rho_M(g)a)(\rho_D(g)b) = \rho_N(g)\,\varphi(a)(b)$ for all $g \in G$, $a \in M$, $b \in D$. Let $\mathrm{inv}$ be a $k$-linear functional on `continuousH2 r N`, the quotient of the module of level-constant $2$-cocycles `levelCocycles₂ r N` by the submodule of those that are level-constant $2$-coboundaries. The assertion is a conjunction of two existence statements. First, there is a $k$-linear map $\theta_0 \colon M^{G} \to \operatorname{Dual}_k(\mathtt{continuousH2}\ r\ D)$ satisfying `IsTheta0`: for every invariant $m \in M^{G}$, every $z \in$ `levelCocycles₂ r D` and every $e \in$ `levelCocycles₂ r N` with $e(s,t) = \varphi(m)(z(s,t))$ for all $(s,t) \in G \times G$, one has $\theta_0(m)([z]) = \mathrm{inv}([e])$. Second, there is a $k$-linear map $\theta_2 \colon \mathtt{continuousH2}\ r\ M \to \operatorname{Dual}_k(D^{G})$ satisfying `IsTheta2`: for every $z \in$ `levelCocycles₂ r M`, every $d \in D^{G}$ and every $e \in$ `levelCocycles₂ r N` with $e(s,t) = \varphi(z(s,t))(d)$ for all $(s,t)$, one has $\theta_2([z])(d) = \mathrm{inv}([e])$.
--
--   These are the duality maps in bidegrees $(0,2)$ and $(2,0)$ attached to an equivariant pairing and a chosen functional on continuous $H^2$ of the target; no hypothesis beyond equivariance of the pairing is needed, in contrast with the bidegree-$(1,1)$ map, which requires the cup product to descend to continuous classes. The statement is used by the bijectivity results for the resulting duality maps, including those for twisted coefficients and for restriction to open subgroups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_theta0_and_theta2.lean

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

theorem groupCohomology.exists_theta0_and_theta2
    {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    {M D N : Rep.{u} k G} (φ : M →ₗ[k] D →ₗ[k] N) (hφ : Rep.IsEquivariantBilinear M D N φ)
    (inv : continuousH2 r N →ₗ[k] k) :
    (∃ θ₀ : M.ρ.invariants →ₗ[k] Module.Dual k (continuousH2 r D), IsTheta0 r φ inv θ₀) ∧
    (∃ θ₂ : continuousH2 r M →ₗ[k] Module.Dual k D.ρ.invariants, IsTheta2 r φ inv θ₂) := by sorry

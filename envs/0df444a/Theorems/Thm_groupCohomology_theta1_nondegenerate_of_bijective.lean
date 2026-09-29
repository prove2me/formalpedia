-- Prove2me | Theorems.Thm_groupCohomology_theta1_nondegenerate_of_bijective
-- name    : groupCohomology.theta1_nondegenerate_of_bijective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/fff5847e-36f0-50f5-8100-ce2c013ce85c
-- title:
--   Two-sided nondegeneracy of a bijective pairing into the dual
-- statement:
--   Let $k$ be a field and $G$ a group, both in a fixed universe, and let $r : G \to \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ be a group homomorphism into the automorphism group of `AlgebraicClosure ℚ` over $\mathbb{Q}$. Let $M$ and $D$ be $k$-linear representations of $G$, and write $\mathrm{H}^1_{\mathrm{cont}}(r,M)$ for `continuousH1 r M`, the $k$-submodule of the first group cohomology $\mathrm{H}^1(G,M)$ obtained as the image, under the canonical map `H1π` from one-cocycles to $\mathrm{H}^1(G,M)$, of the submodule `levelCocycles₁ r M` of cocycles attached to $r$; likewise for $D$. Let $\theta : \mathrm{H}^1_{\mathrm{cont}}(r,M) \to \mathrm{Hom}_k(\mathrm{H}^1_{\mathrm{cont}}(r,D),k)$ be a $k$-linear map into the $k$-dual of $\mathrm{H}^1_{\mathrm{cont}}(r,D)$, and assume $\theta$ is bijective. The conclusion is the conjunction of two nondegeneracy statements for the associated pairing $(x,w) \mapsto \theta(x)(w)$: first, any $x \in \mathrm{H}^1_{\mathrm{cont}}(r,M)$ with $\theta(x)(w) = 0$ for all $w \in \mathrm{H}^1_{\mathrm{cont}}(r,D)$ vanishes; second, any $w \in \mathrm{H}^1_{\mathrm{cont}}(r,D)$ with $\theta(x)(w) = 0$ for all $x \in \mathrm{H}^1_{\mathrm{cont}}(r,M)$ vanishes. Nothing beyond the $k$-module structures is used: $r$, $M$ and $D$ serve only to name the two spaces.
--
--   This is the standard passage from a bijective map into a dual space to nondegeneracy of the corresponding bilinear pairing, specialised to the pair of continuous first cohomology groups used in the duality bookkeeping of Greenberg–Wiles type Euler-characteristic formulas; the field hypothesis is what makes the second half hold. It is cited in the identification of the Greenberg–Wiles expression with the unramified local menu, [`groupCohomology.greenbergWiles_eq_unramifiedMenu_extArithLoc`](thm.html#groupCohomology.greenbergWiles_eq_unramifiedMenu_extArithLoc).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_theta1_nondegenerate_of_bijective.lean

import Definitions.Def_GroupCohomology_ContinuousDuality
import Definitions.Def_GroupCohomology_Selmer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Module
universe u

theorem groupCohomology.theta1_nondegenerate_of_bijective {k G : Type u} [Group G] [Field k]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    {M D : Rep.{u} k G}
    (θ : continuousH1 r M →ₗ[k] Module.Dual k (continuousH1 r D))
    (hbij : Function.Bijective θ) :
    (∀ x : continuousH1 r M, (∀ w : continuousH1 r D, θ x w = 0) → x = 0)
    ∧ ∀ w : continuousH1 r D, (∀ x : continuousH1 r M, θ x w = 0) → w = 0 := by sorry

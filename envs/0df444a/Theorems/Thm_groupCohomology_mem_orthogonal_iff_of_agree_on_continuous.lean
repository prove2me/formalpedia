-- Prove2me | Theorems.Thm_groupCohomology_mem_orthogonal_iff_of_agree_on_continuous
-- name    : groupCohomology.mem_orthogonal_iff_of_agree_on_continuous
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/429d535a-ec1b-5ff9-9825-825df7e5ac10
-- title:
--   Orthogonality under a pairing agreeing with θ on continuous classes
-- statement:
--   Fix a field $k$ and a group $G$ in a common universe, together with a homomorphism $r \colon G \to \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ (the automorphism group of `AlgebraicClosure ℚ` over $\mathbb{Q}$), and two $k$-linear representations $M$, $M'$ of $G$. Let `pairing` be a $k$-bilinear map $H^1(G,M) \times H^1(G,M') \to k$, and let $\theta$ be a $k$-linear map from `continuousH1 r M` to the $k$-dual of `continuousH1 r M'`; here `continuousH1 r M` denotes the submodule of $H^1(G,M)$ obtained as the image under the projection `H1π M` of the submodule `levelCocycles₁ r M` of cocycles, and similarly for $M'$. Assume that `pairing` and $\theta$ agree on these submodules: $\mathrm{pairing}(x)(w) = \theta(x)(w)$ for all $x \in$ `continuousH1 r M` and $w \in$ `continuousH1 r M'`. Let $L$ be a $k$-submodule of $H^1(G,M)$ with $L \le$ `continuousH1 r M`, and let $w \in$ `continuousH1 r M'`. Then the image of $w$ in $H^1(G,M')$ lies in `orthogonal pairing L`, that is, in the preimage under the flip of `pairing` of the dual annihilator of $L$, if and only if $\theta(\langle x, hL\,hx\rangle)(w) = 0$ for every $x \in H^1(G,M)$ and every proof $hx$ that $x \in L$, where $x$ is read as a continuous class via the inclusion $L \le$ `continuousH1 r M`.
--
--   This is the elementary compatibility statement saying that, for local conditions $L$ contained in the continuous part of $H^1$, membership in the orthogonal complement of $L$ under a global pairing depends only on the restricted pairing $\theta$ on continuous classes. It is used in the identification [`groupCohomology.greenbergWiles_eq_unramifiedMenu_extArithLoc`](thm.html#groupCohomology.greenbergWiles_eq_unramifiedMenu_extArithLoc), where orthogonal complements of unramified conditions must be computed through the continuous duality.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_mem_orthogonal_iff_of_agree_on_continuous.lean

import Definitions.Def_GroupCohomology_ContinuousDuality
import Definitions.Def_GroupCohomology_Selmer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Module
universe u

theorem groupCohomology.mem_orthogonal_iff_of_agree_on_continuous {k G : Type u} [Group G] [Field k]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    {M M' : Rep.{u} k G}
    (pairing : H1 M →ₗ[k] H1 M' →ₗ[k] k)
    (θ : continuousH1 r M →ₗ[k] Module.Dual k (continuousH1 r M'))
    (hagree : ∀ (x : continuousH1 r M) (w : continuousH1 r M'),
      pairing x w = θ x w)
    (L : Submodule k (H1 M)) (hL : L ≤ continuousH1 r M)
    (w : continuousH1 r M') :
    (w : H1 M') ∈ orthogonal pairing L ↔ ∀ x : H1 M, ∀ hx : x ∈ L, θ ⟨x, hL hx⟩ w = 0 := by sorry

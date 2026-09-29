-- Prove2me | Theorems.Thm_groupCohomology_nonempty_continuous_linearEquiv_of_mulEquiv
-- name    : groupCohomology.nonempty_continuous_linearEquiv_of_mulEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/ca11bfc7-ac8f-549e-9a0e-91e3ac977248
-- title:
--   Invariance of continuous H⁰, H¹, H² under isomorphic data
-- statement:
--   Let $k$ be a commutative ring and let $G$, $H$ be groups, all three in a single universe. Suppose given level maps, i.e. group homomorphisms $r_G \colon G \to (\overline{\mathbb{Q}} \simeq_{\mathrm{alg}[\mathbb{Q}]} \overline{\mathbb{Q}})$ and $r_H \colon H \to (\overline{\mathbb{Q}} \simeq_{\mathrm{alg}[\mathbb{Q}]} \overline{\mathbb{Q}})$ into the group of $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`, a group isomorphism $e \colon G \simeq H$ compatible with them in the sense that $r_H(e(g)) = r_G(g)$ for all $g \in G$, representations $N_G \in \mathrm{Rep}\,k\,G$ and $N_H \in \mathrm{Rep}\,k\,H$, and a $k$-linear equivalence $\varphi \colon N_G \simeq N_H$ of the underlying modules satisfying $\varphi(\rho_{N_G}(g)x) = \rho_{N_H}(e(g))(\varphi(x))$ for all $g \in G$, $x \in N_G$. The conclusion is the conjunction of three nonemptiness assertions: the $k$-modules of invariants $\rho_{N_G}$-invariants and $\rho_{N_H}$-invariants admit a $k$-linear equivalence; the submodule `continuousH1 rG NG` of $H^1(G,N_G)$, defined as the image of `levelCocycles₁ rG NG` under the projection `H1π`, admits a $k$-linear equivalence with `continuousH1 rH NH`; and the quotient `continuousH2 rG NG` of `levelCocycles₂ rG NG` by the preimage in it of `levelCoboundaries₂ rG NG` admits a $k$-linear equivalence with `continuousH2 rH NH`. Only existence of such equivalences is asserted, not a canonical choice.
--
--   This is transport of structure for continuous (level-constant) cohomology in degrees $0$, $1$ and $2$ along an isomorphism of triples (group, level map, module). It is used to identify the continuous cohomology of one and the same group presented in two different ways, and is invoked in the proofs that the comparison maps $\theta_0$, $\theta_1$, $\theta_2$ and the dual-twist map are bijective under an openness hypothesis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_nonempty_continuous_linearEquiv_of_mulEquiv.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory

theorem groupCohomology.nonempty_continuous_linearEquiv_of_mulEquiv {k G H : Type u} [CommRing k] [Group G] [Group H]
    (rG : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (rH : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (e : G ≃* H) (he : ∀ g, rH (e g) = rG g) (NG : Rep.{u} k G) (NH : Rep.{u} k H)
    (φ : NG ≃ₗ[k] NH) (hφ : ∀ (g : G) (x : NG), φ (NG.ρ g x) = NH.ρ (e g) (φ x)) :
    Nonempty (NG.ρ.invariants ≃ₗ[k] NH.ρ.invariants) ∧
    Nonempty (groupCohomology.continuousH1 rG NG ≃ₗ[k] groupCohomology.continuousH1 rH NH) ∧
    Nonempty (groupCohomology.continuousH2 rG NG ≃ₗ[k] groupCohomology.continuousH2 rH NH) := by sorry

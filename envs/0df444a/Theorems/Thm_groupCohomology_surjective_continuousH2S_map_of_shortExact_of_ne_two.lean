-- Prove2me | Theorems.Thm_groupCohomology_surjective_continuousH2S_map_of_shortExact_of_ne_two
-- name    : groupCohomology.surjective_continuousH2S_map_of_shortExact_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/90c3d41d-8bb3-535c-83ca-ae69fffd5552
-- title:
--   Surjectivity of H²_S(N₂)→ H²_S(N₃) for odd p
-- statement:
--   Let $p$ be a prime with $p \neq 2$, let $S$ be a finite set of primes containing $p$, and let $N_1, N_2, N_3$ be representations of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ (with $\overline{\mathbb{Q}}$ the algebraic closure `AlgebraicClosure ℚ`) on finite-dimensional $\mathbb{Z}/p$-vector spaces. Let $f : N_1 \to N_2$ and $g : N_2 \to N_3$ be morphisms of representations with $f$ followed by $g$ zero, such that the resulting short complex is short exact. Assume $N_2$ is smooth, in the sense that every $m \in N_2$ is fixed by the subgroup fixing some finite extension $F/\mathbb{Q}$ inside $\overline{\mathbb{Q}}$, and that $N_2$ is unramified outside $S$: for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$, every element of the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ acts as the identity on $N_2$. Finally let $p_2 : \mathrm{continuousH2S}\,S\,N_2 \to \mathrm{continuousH2S}\,S\,N_3$ be a $\mathbb{Z}/p$-linear map between the quotients of the level-$S$ two-cocycles by the level-$S$ two-coboundaries, assumed compatible with $g$ on representatives: if $z$ and $z'$ are level-$S$ two-cocycles for $N_2$ and $N_3$ with $z'(s,t) = g(z(s,t))$ for all pairs $(s,t)$ of Galois elements, then $p_2$ sends the class of $z$ to the class of $z'$. Then $p_2$ is surjective.
--
--   This is part (c) of the Poitou–Tate theorem in the form $H^3(G_{\mathbb{Q},S}, N_1) = 0$ for odd $p$, i.e. right exactness of degree-two cohomology with ramification restricted to $S$; for $p = 2$ it fails because of the real place. It is used in the computation of the global Euler characteristic, namely by [`groupCohomology.finrank_continuousH2S_add_archimedean_eq_of_shortExact_of_ne_two`](thm.html#groupCohomology.finrank_continuousH2S_add_archimedean_eq_of_shortExact_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_surjective_continuousH2S_map_of_shortExact_of_ne_two.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.surjective_continuousH2S_map_of_shortExact_of_ne_two
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (N1 N2 N3 : Rep.{0} (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    [FiniteDimensional (ZMod p) N1] [FiniteDimensional (ZMod p) N2] [FiniteDimensional (ZMod p) N3]
    (f : N1 ⟶ N2) (g : N2 ⟶ N3) (hfg : f ≫ g = 0)
    (hex : (ShortComplex.mk f g hfg).ShortExact)
    (hsm : ∀ m : N2, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, N2.ρ s m = m)
    (hur : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ s ∈ A.inertiaSubgroupIn ℚ, N2.ρ s = 1)
    (p₂ : continuousH2S S N2 →ₗ[ZMod p] continuousH2S S N3)
    (hp₂ : ∀ (z : levelCocyclesS₂ S N2) (z' : levelCocyclesS₂ S N3),
        (∀ st, (z' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → N3) st = g.hom ((z : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → N2) st)) → p₂ (continuousH2Sπ S N2 z) = continuousH2Sπ S N3 z') :
    Function.Surjective p₂ := by sorry

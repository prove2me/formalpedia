-- Prove2me | Theorems.Thm_groupCohomology_finrank_continuousH2S_add_archimedean_eq_of_shortExact_of_ne_two
-- name    : groupCohomology.finrank_continuousH2S_add_archimedean_eq_of_shortExact_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/f2cd7374-222c-5a21-99c4-67e204785b8e
-- title:
--   End correction of the nine-term sequence, odd p
-- statement:
--   Let $p$ be an odd prime and let $S$ be a finite set of rational primes with $p \in S$. Let $N_1,N_2,N_3$ be finite-dimensional $\mathbb{Z}/p$-linear representations of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ (realised as $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`), and let $f : N_1 \to N_2$, $g : N_2 \to N_3$ be morphisms of representations with $f$ followed by $g$ equal to $0$, such that the resulting short complex is short exact (so $f$ is mono and $g$ is epi). Assume $N_2$ is smooth, in the sense that every $m \in N_2$ is fixed by the subgroup fixing some finite subextension $F/\mathbb{Q}$ of $\overline{\mathbb{Q}}$, and unramified outside $S$, in the sense that for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$, every element of the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ acts as the identity on $N_2$. Assume the degree-two groups $H^2_S(N_2)$ and $H^2_S(N_3)$ — the quotients of the $S$-level $2$-cocycles `levelCocyclesS₂` by the $2$-coboundaries lying in them — are finite-dimensional over $\mathbb{Z}/p$, and let $p_2 : H^2_S(N_2) \to H^2_S(N_3)$ be a $\mathbb{Z}/p$-linear map pinned down by the requirement that, whenever an $S$-level cocycle $z$ for $N_2$ and an $S$-level cocycle $z'$ for $N_3$ satisfy $z'(s,t) = g(z(s,t))$ for all pairs $(s,t)$, then $p_2$ carries the class of $z$ to the class of $z'$. Then $$\dim H^2_S(N_3) + \dim N_2^{G_\infty} = \dim(\mathrm{range}\,p_2) + \dim N_1^{G_\infty} + \dim N_3^{G_\infty},$$ all dimensions over $\mathbb{Z}/p$, where $N^{G_\infty}$ denotes the invariants of $N$ restricted along the inclusion of the archimedean decomposition subgroup `archimedeanDecomposition` (the index `Sum.inl ()` of `extArithLoc`) into the global Galois group.
--
--   This is the end correction of the nine-term Poitou–Tate style exact sequence attached to a short exact sequence of $S$-ramified mod $p$ Galois representations: for odd $p$ it packages the surjectivity of the induced map on $H^2_S$ together with the additivity of the dimensions of invariants at the real place. It feeds the additivity of the Euler defect, [`groupCohomology.eulerDefect_add_of_shortExact_of_ne_two`](thm.html#groupCohomology.eulerDefect_add_of_shortExact_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_finrank_continuousH2S_add_archimedean_eq_of_shortExact_of_ne_two.lean

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

theorem groupCohomology.finrank_continuousH2S_add_archimedean_eq_of_shortExact_of_ne_two
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (N1 N2 N3 : Rep.{0} (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    [FiniteDimensional (ZMod p) N1] [FiniteDimensional (ZMod p) N2] [FiniteDimensional (ZMod p) N3]
    (f : N1 ⟶ N2) (g : N2 ⟶ N3) (hfg : f ≫ g = 0)
    (hex : (ShortComplex.mk f g hfg).ShortExact)
    (hsm : ∀ m : N2, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, N2.ρ s m = m)
    (hur : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ s ∈ A.inertiaSubgroupIn ℚ, N2.ρ s = 1)
    [FiniteDimensional (ZMod p) (continuousH2S S N2)] [FiniteDimensional (ZMod p) (continuousH2S S N3)]
    (p₂ : continuousH2S S N2 →ₗ[ZMod p] continuousH2S S N3)
    (hp₂ : ∀ (z : levelCocyclesS₂ S N2) (z' : levelCocyclesS₂ S N3),
        (∀ st, (z' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → N3) st = g.hom ((z : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → N2) st)) → p₂ (continuousH2Sπ S N2 z) = continuousH2Sπ S N3 z') :
    finrank (ZMod p) (continuousH2S S N3)
      + finrank (ZMod p) (Rep.res (extArithLoc S (Sum.inl ())) N2).ρ.invariants
    = finrank (ZMod p) (LinearMap.range p₂)
      + finrank (ZMod p) (Rep.res (extArithLoc S (Sum.inl ())) N1).ρ.invariants
      + finrank (ZMod p) (Rep.res (extArithLoc S (Sum.inl ())) N3).ρ.invariants := by sorry

-- Prove2me | Theorems.Thm_groupCohomology_finiteDimensional_and_finrank_continuousH1Sr_twist_cycloChar_eq_of_trivial
-- name    : groupCohomology.finiteDimensional_and_finrank_continuousH1Sr_twist_cycloChar_eq_of_trivial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/348064a3-de63-5b72-ac2f-d8c149f609ee
-- title:
--   Tate's Euler-characteristic formula for N(1) at level S
-- statement:
--   Let $p$ be a prime and $S$ a finite set of rational primes containing $p$ (as `pPrime p`). Let $K \le L$ be intermediate fields of $\mathbb{Q}$ in $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, each unramified outside $S$ in the sense of `IsUnramifiedOutside`: finite over $\mathbb{Q}$, and for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$, the image in $\mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ lies in the fixing subgroup of the field. Assume $K$'s fixing subgroup normalises $L$'s (hypothesis `hnorm`), that the relative index of $L.\mathrm{fixingSubgroup}$ in $K.\mathrm{fixingSubgroup}$ is coprime to $p$, that $L$ contains a primitive $p$-th root of unity $\zeta$, and that for $p = 2$ it contains a square root of $-1$. Let $N$ be a finite-dimensional representation of $K.\mathrm{fixingSubgroup}$ over $\mathbb{Z}/p$ which is trivial on those elements of $K.\mathrm{fixingSubgroup}$ that lie in $L.\mathrm{fixingSubgroup}$. Write $M = N(1)$ for `N.twist` by the mod $p$ cyclotomic character `cycloChar p` restricted to $K.\mathrm{fixingSubgroup}$, i.e. the representation $g \mapsto \chi(g)\,N.\rho(g)$. Then the submodule `continuousH1Sr` of $H^1(M)$, the image of the level-$S$ cocycle submodule `levelCocyclesSr₁` under $H^1\pi$, is finite-dimensional over $\mathbb{Z}/p$; the quotient `continuousH2Sr` of `levelCocyclesSr₂` by the coboundaries it contains is finite-dimensional; and $$\dim H^1_S(M) = \dim M^{K.\mathrm{fixingSubgroup}} + \dim H^2_S(M) + \sum_v \dim N^{\mathrm{Stab}(v)},$$ the finite sum being over the orbits of $K.\mathrm{fixingSubgroup}$ on $\mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ modulo the range of `extArithLoc S (Sum.inl ())`, the archimedean decomposition subgroup, with $N$ restricted to the stabiliser of a chosen representative of each orbit.
--
--   This is the global Euler–Poincaré characteristic formula of Tate, at the level of the number field $K$ and for the Tate twist $N(1)$ of a finite-dimensional mod $p$ Galois module trivial on $L$, with the local archimedean term written as a sum over the archimedean places of $K$ of the dimensions of the invariants of $N$ under the corresponding decomposition groups; finiteness of $H^1_S$ and $H^2_S$ is part of the conclusion rather than a hypothesis. It is the base case from which [`groupCohomology.finiteDimensional_continuousH2S_coind_and_finrank_eq`](thm.html#groupCohomology.finiteDimensional_continuousH2S_coind_and_finrank_eq) derives the corresponding statement for modules coinduced from an $S$-level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_finiteDimensional_and_finrank_continuousH1Sr_twist_cycloChar_eq_of_trivial.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation
open scoped Classical

theorem groupCohomology.finiteDimensional_and_finrank_continuousH1Sr_twist_cycloChar_eq_of_trivial
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hK : K.IsUnramifiedOutside S) (hL : L.IsUnramifiedOutside S)
    (hKL : K ≤ L)
    (hnorm : ∀ g ∈ K.fixingSubgroup, ∀ s ∈ L.fixingSubgroup, g * s * g⁻¹ ∈ L.fixingSubgroup)
    (hcop : (L.fixingSubgroup.relIndex K.fixingSubgroup).Coprime p)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) (hζL : ζ ∈ L)
    (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1)
    (N : Rep.{0} (ZMod p) ↥K.fixingSubgroup) [FiniteDimensional (ZMod p) N]
    (htriv : ∀ s : ↥K.fixingSubgroup, (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ L.fixingSubgroup → N.ρ s = 1) :
    FiniteDimensional (ZMod p)
        ↥(continuousH1Sr K.fixingSubgroup.subtype S (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype))) ∧
      FiniteDimensional (ZMod p)
        (continuousH2Sr K.fixingSubgroup.subtype S (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype))) ∧
      Module.finrank (ZMod p)
          ↥(continuousH1Sr K.fixingSubgroup.subtype S (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype))) =
        Module.finrank (ZMod p) (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype)).ρ.invariants +
        Module.finrank (ZMod p)
          (continuousH2Sr K.fixingSubgroup.subtype S (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype))) +
        ∑ᶠ v : Quotient (MulAction.orbitRel ↥K.fixingSubgroup
            ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (extArithLoc S (Sum.inl ())).range)),
          Module.finrank (ZMod p) (Rep.res (MulAction.stabilizer (↥K.fixingSubgroup) v.out).subtype N).ρ.invariants := by sorry

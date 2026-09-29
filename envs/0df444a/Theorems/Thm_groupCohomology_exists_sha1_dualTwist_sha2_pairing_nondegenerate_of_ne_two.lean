-- Prove2me | Theorems.Thm_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two
-- name    : groupCohomology.exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/c3561af3-c259-500e-9c2f-0d8a2f8b5820
-- title:
--   Poitou–Tate pairing between `sha₁` of M^∨(1) and `sha₂` of M
-- statement:
--   Let $p$ be a prime with $p \neq 2$, let $S$ be a finite set of rational primes containing $p$ (the element `pPrime p` of `Nat.Primes`), and let $M$ be a representation of the absolute Galois group $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$, realised as the group of $\mathbb Q$-algebra automorphisms of `AlgebraicClosure ℚ`, on a finite-dimensional $\mathbb F_p =$ `ZMod p` vector space. Two hypotheses constrain the action: smoothness, in the form that every $m \in M$ is fixed by $\rho(s)$ for all $s$ in the fixing subgroup of some intermediate field $F$ of $\overline{\mathbb Q}/\mathbb Q$ that is finite-dimensional over $\mathbb Q$; and unramifiedness outside $S$, in the form that for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$, every element $g$ of the inertia subgroup of $A$ over $\mathbb Q$ (the image in the Galois group of `A.inertiaSubgroup ℚ` under the inclusion of the decomposition subgroup) satisfies $\rho(g) = 1$. The conclusion asserts the existence of an $\mathbb F_p$-bilinear map $B$ from `sha₁ S (M.dualTwist (cycloChar p))` to the space of $\mathbb F_p$-linear maps from `sha₂ S M` to $\mathbb F_p$, where `M.dualTwist (cycloChar p)` is the dual representation $M^\vee$ twisted by the mod-$p$ cyclotomic character `cycloChar p`, such that $B$ is non-degenerate on both sides: any $y$ with $B\,y\,x = 0$ for all $x$ vanishes, and any $x$ with $B\,y\,x = 0$ for all $y$ vanishes. Here `sha₁` and `sha₂` are the degree-one and degree-two objects attached to $S$ and a representation.
--
--   This is the Poitou–Tate duality statement for the Tate–Shafarevich-type groups of a finite Galois module over $\mathbb Q$, in the form of a pairing $Ш^1_S(M^\vee(1)) \times Ш^2_S(M) \to \mathbb F_p$ non-degenerate on both sides, restricted to odd residue characteristic, which is all that the route to Fermat's Last Theorem requires. It is the source of the two injectivity statements [`groupCohomology.exists_injective_sha1_dualTwist_to_dual_sha2_of_ne_two`](thm.html#groupCohomology.exists_injective_sha1_dualTwist_to_dual_sha2_of_ne_two) and [`TWNum.exists_injective_sha2_to_dual_sha1_dualTwist_of_ne_two`](thm.html#TWNum.exists_injective_sha2_to_dual_sha1_dualTwist_of_ne_two), used in controlling deformation rings and Selmer groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two.lean

import Definitions.Def_GroupCohomology_ContinuousUnramified

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s m = m)
    (hMur : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ, M.ρ g = 1) :
    ∃ B : sha₁ S (M.dualTwist (cycloChar p)) →ₗ[ZMod p] sha₂ S M →ₗ[ZMod p] ZMod p,
      (∀ y, (∀ x, B y x = 0) → y = 0) ∧ (∀ x, (∀ y, B y x = 0) → x = 0) := by sorry

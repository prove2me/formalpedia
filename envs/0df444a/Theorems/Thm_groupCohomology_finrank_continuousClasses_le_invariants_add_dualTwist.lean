-- Prove2me | Theorems.Thm_groupCohomology_finrank_continuousClasses_le_invariants_add_dualTwist
-- name    : groupCohomology.finrank_continuousClasses_le_invariants_add_dualTwist
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/b16eba62-1a54-5320-af18-35a2f17b400b
-- title:
--   Upper bound for continuous H¹ at q ≠ p
-- statement:
--   Fix a prime $p$ and a prime $q$ with $q \ne p$ as natural numbers, and write $G_q$ for `primeLocalGaloisGroup q`, the group of $\mathbb{Q}_q$-algebra automorphisms of the chosen algebraic closure `PadicAlgCl q` of $\mathbb{Q}_q$, together with the homomorphism `primeLocalToGlobal q` into $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ obtained by restricting scalars to $\mathbb{Q}$ and then restricting the resulting automorphism to `AlgebraicClosure ℚ`. Let $M$ be a representation of $G_q$ on a finite-dimensional $\mathbb{Z}/p$-vector space which is smooth in the following sense: for every $m \in M$ there is an intermediate field $F$ of $\mathbb{Q}$ in `AlgebraicClosure ℚ`, finite over $\mathbb{Q}$, such that every $s \in G_q$ whose image in $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ lies in the fixing subgroup of $F$ acts trivially on $m$. Let $\mathrm{adm}_1$ be a finite-dimensional $\mathbb{Z}/p$-submodule of $H^1(G_q, M)$ consisting exactly of the classes represented by a $1$-cocycle $c$ that is right-invariant at some finite level, that is, for which there is an intermediate field $F$ of $\mathbb{Q}$ in `AlgebraicClosure ℚ`, finite over $\mathbb{Q}$, with $c(g s) = c(g)$ for all $g, s \in G_q$ such that the image of $s$ lies in the fixing subgroup of $F$. Then the $\mathbb{Z}/p$-dimension of $\mathrm{adm}_1$ is at most the dimension of $M^{G_q}$ plus the dimension of the invariants of the dual of $M$ twisted by the mod $p$ cyclotomic character `cycloChar p` composed with `primeLocalToGlobal q`, i.e. of $(M^{\vee}(1))^{G_q}$.
--
--   This is the inequality half of the local Euler characteristic computation at a prime $q \ne p$: the continuous part of $H^1(G_q, M)$ is bounded by $h^0(M) + h^0(M^{\vee}(1))$, with no unramifiedness hypothesis on $M$. It is the direction used to bound Selmer groups from above in the Greenberg–Wiles method, and it feeds both the corresponding equality statement at $q \ne p$ and the bound on the strict Selmer group in terms of the set of Taylor–Wiles primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_finrank_continuousClasses_le_invariants_add_dualTwist.lean

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.finrank_continuousClasses_le_invariants_add_dualTwist
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes) (hne : (q : ℕ) ≠ p)
    (M : Rep (ZMod p) (primeLocalGaloisGroup q))
    [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ),
      FiniteDimensional ℚ F ∧
        ∀ s, primeLocalToGlobal q s ∈ F.fixingSubgroup → M.ρ s m = m)
    (adm₁ : Submodule (ZMod p) (H1 M)) [FiniteDimensional (ZMod p) adm₁]
    (hadm₁ : ∀ x, x ∈ adm₁ ↔ ∃ c : cocycles₁ M,
      (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ (g s : primeLocalGaloisGroup q),
          primeLocalToGlobal q s ∈ F.fixingSubgroup → c.val (g * s) = c.val g)
      ∧ (H1π M).hom c = x) :
    finrank (ZMod p) adm₁
      ≤ finrank (ZMod p) M.ρ.invariants
        + finrank (ZMod p)
            (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q))).ρ.invariants := by sorry

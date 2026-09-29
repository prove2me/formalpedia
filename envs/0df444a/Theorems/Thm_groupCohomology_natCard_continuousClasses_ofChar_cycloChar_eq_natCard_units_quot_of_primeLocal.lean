-- Prove2me | Theorems.Thm_groupCohomology_natCard_continuousClasses_ofChar_cycloChar_eq_natCard_units_quot_of_primeLocal
-- name    : groupCohomology.natCard_continuousClasses_ofChar_cycloChar_eq_natCard_units_quot_of_primeLocal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/c09f31fb-755c-5128-8aac-e05594006b86
-- title:
--   Continuous H¹(ℚₚ,μₚ) counted by ℚₚ^×/(ℚₚ^×)ᵖ
-- statement:
--   Fix a prime $p$ and a prime $q$ with $q = p$ as natural numbers. Let $\Gamma_q$ denote `primeLocalGaloisGroup q`, the group of $\mathbb{Q}_q$-algebra automorphisms of the algebraic closure `PadicAlgCl q`, and let `primeLocalToGlobal q` be the homomorphism $\Gamma_q \to \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ obtained by restricting scalars to $\mathbb{Q}$ and then restricting to the normal subextension $\overline{\mathbb{Q}}$. Consider the one-dimensional representation `ofChar` of $\Gamma_q$ over $\mathbb{Z}/p$ attached to the character $(\mathrm{cycloChar}\ p)\circ(\mathrm{primeLocalToGlobal}\ q)$, that is, the trivial representation on $\mathbb{Z}/p$ twisted so that $g$ acts by the mod $p$ cyclotomic character of $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ evaluated at the image of $g$. Let $\mathrm{adm}_1$ be a $\mathbb{Z}/p$-submodule of the first cohomology $H^1$ of this representation whose members are exactly the classes $x$ admitting a $1$-cocycle $c$ representing $x$ (under the projection `H1π` from cocycles to $H^1$) for which there is an intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, with $c(gs) = c(g)$ for all $g, s \in \Gamma_q$ such that the image of $s$ fixes $F$ pointwise. Then the cardinality of $\mathrm{adm}_1$ equals that of $\mathbb{Q}_p^\times$ modulo the image of the $p$-th power homomorphism, i.e. of $\mathbb{Q}_p^\times/(\mathbb{Q}_p^\times)^p$.
--
--   This is the local Kummer-theoretic count of the continuous (level-constant) part of $H^1(\mathbb{Q}_p,\mu_p)$, the submodule of classes trivialised on the Galois group of a finite layer coming from a number field. It feeds the local Euler-characteristic bookkeeping: it is used by [`groupCohomology.finrank_continuousClasses_ofChar_cycloChar_eq_two_of_primeLocal`](thm.html#groupCohomology.finrank_continuousClasses_ofChar_cycloChar_eq_two_of_primeLocal), which converts this cardinality into the dimension statement $\dim_{\mathbb{F}_p} = 2$ for odd $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_natCard_continuousClasses_ofChar_cycloChar_eq_natCard_units_quot_of_primeLocal.lean

import Definitions.Def_ExtEndgame_ProductionDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.natCard_continuousClasses_ofChar_cycloChar_eq_natCard_units_quot_of_primeLocal
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes) (hq : (q : ℕ) = p)
    (adm₁ : Submodule (ZMod p) (H1 (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))))
    (hadm₁ : ∀ x, x ∈ adm₁ ↔
      ∃ c : cocycles₁ (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))),
        (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ (g s : primeLocalGaloisGroup q),
            primeLocalToGlobal q s ∈ F.fixingSubgroup → c.val (g * s) = c.val g)
        ∧ (H1π _).hom c = x) :
    Nat.card adm₁ = Nat.card ((ℚ_[p])ˣ ⧸ (powMonoidHom p : (ℚ_[p])ˣ →* (ℚ_[p])ˣ).range) := by sorry

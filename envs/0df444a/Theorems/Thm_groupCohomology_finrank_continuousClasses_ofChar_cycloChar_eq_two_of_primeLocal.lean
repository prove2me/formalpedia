-- Prove2me | Theorems.Thm_groupCohomology_finrank_continuousClasses_ofChar_cycloChar_eq_two_of_primeLocal
-- name    : groupCohomology.finrank_continuousClasses_ofChar_cycloChar_eq_two_of_primeLocal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/80a657ab-dac9-5c80-8171-88e7fbf15bbb
-- title:
--   dim_{𝔽_p} H¹_{cont}(ℚₚ,μₚ)=2 for odd p
-- statement:
--   Let $p$ be a prime with $p \neq 2$, and let $q$ be a prime whose underlying natural number equals $p$. Write $\Gamma_q$ for `primeLocalGaloisGroup q`, the group of $\mathbb{Q}_p$-algebra automorphisms of the algebraic closure `PadicAlgCl` of $\mathbb{Q}_p$, and let `primeLocalToGlobal q` be the homomorphism $\Gamma_q \to \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ obtained by restricting scalars to $\mathbb{Q}$ and then restricting the resulting automorphism to the algebraic closure of $\mathbb{Q}$ inside it. Let $M$ be the representation `ofChar` attached to the composite of this homomorphism with the mod $p$ cyclotomic character `cycloChar p`, that is, the one-dimensional $\mathbb{Z}/p$-vector space on which $\sigma \in \Gamma_q$ acts by the scalar $\chi_p(\sigma)$. Let $\mathrm{adm}_1$ be a $\mathbb{Z}/p$-submodule of $H^1(\Gamma_q, M)$, assumed to consist of exactly those classes $x$ admitting a $1$-cocycle representative $c$ with $(H1\pi)(c) = x$ for which there is a finite extension $F$ of $\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ with $c(gs) = c(g)$ for all $g, s \in \Gamma_q$ such that the image of $s$ fixes $F$ pointwise. Then $\mathrm{adm}_1$ is a finite $\mathbb{Z}/p$-module and its rank is $2$.
--
--   This is the local computation $\dim_{\mathbb{F}_p} H^1_{\mathrm{cont}}(\mathbb{Q}_p, \mu_p) = 2$ at the residual prime $p$, for $p$ odd, the submodule $\mathrm{adm}_1$ being characterised as the classes represented by cocycles that factor through a finite level. It supplies both the finite-dimensionality and the dimension input at $v = p$ to the local Euler-characteristic bookkeeping used in [`GaloisRepAdic.exists_submodule_finrank_le_invariants_add_one_mem_of_isStrictOrdinaryAt`](thm.html#GaloisRepAdic.exists_submodule_finrank_le_invariants_add_one_mem_of_isStrictOrdinaryAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_finrank_continuousClasses_ofChar_cycloChar_eq_two_of_primeLocal.lean

import Definitions.Def_ExtEndgame_ProductionDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.finrank_continuousClasses_ofChar_cycloChar_eq_two_of_primeLocal
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (q : Nat.Primes) (hq : (q : ℕ) = p)
    (adm₁ : Submodule (ZMod p) (H1 (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))))
    (hadm₁ : ∀ x, x ∈ adm₁ ↔
      ∃ c : cocycles₁ (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))),
        (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ (g s : primeLocalGaloisGroup q),
            primeLocalToGlobal q s ∈ F.fixingSubgroup → c.val (g * s) = c.val g)
        ∧ (H1π _).hom c = x) :
    Module.Finite (ZMod p) adm₁ ∧ finrank (ZMod p) adm₁ = 2 := by sorry

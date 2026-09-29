-- Prove2me | Theorems.Thm_groupCohomology_finrank_finiteQuotientH1_eq_invariants_add_dualTwist_add_finrank_of_primeLocal
-- name    : groupCohomology.finrank_finiteQuotientH1_eq_invariants_add_dualTwist_add_finrank_of_primeLocal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/5db0eb17-4842-531e-8d6e-360bc0d12d88
-- title:
--   Local Euler characteristic at p, with H² folded by duality
-- statement:
--   Let $p$ be a prime and let $q$ be a prime with $q = p$ as natural numbers. Let $M$ be a finite-dimensional representation over $\mathbb{Z}/p$ of `primeLocalGaloisGroup q`, the group of $\mathbb{Q}_q$-algebra automorphisms of `PadicAlgCl q`, and write `primeLocalToGlobal q` for the homomorphism from this local group to $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ obtained by restricting scalars to $\mathbb{Q}$ and then restricting to the algebraic closure of $\mathbb{Q}$. Assume $M$ is smooth in the sense that for every $m \in M$ there is a finite extension $F/\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ such that $M.\rho(s)m = m$ whenever the global image of $s$ lies in the fixing subgroup of $F$. Let $\mathrm{adm}_1$ be a finite-dimensional $\mathbb{Z}/p$-submodule of $H^1(M)$ whose elements are exactly the classes $(H1\pi\,M)(c)$ of those $1$-cocycles $c$ for which there is a finite extension $F/\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ with $c(gs) = c(g)$ for all $g$ and all $s$ whose global image lies in the fixing subgroup of $F$. Then the $\mathbb{Z}/p$-dimension of $\mathrm{adm}_1$ equals $\dim M^{\rho} + \dim (M^{\vee} \otimes \chi)^{\rho} + \dim M$, where $M^{\vee} \otimes \chi$ is the dual representation of $M$ multiplied by the mod-$p$ cyclotomic character `cycloChar p` pulled back along `primeLocalToGlobal q`.
--
--   This is Tate's local Euler characteristic formula at the place above $p$, with $H^2$ eliminated by local duality: the dimension of the continuous (locally constant) $H^1$ is expressed as $h^0(M) + h^0(M^\vee(1)) + \dim M$, the last term reflecting $[\mathbb{Q}_p : \mathbb{Q}_p] = 1$. It feeds the local dimension count in the Greenberg–Wiles accounting of Selmer groups used in the modularity-lifting argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_finrank_finiteQuotientH1_eq_invariants_add_dualTwist_add_finrank_of_primeLocal.lean

import Definitions.Def_ExtEndgame_ProductionDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.finrank_finiteQuotientH1_eq_invariants_add_dualTwist_add_finrank_of_primeLocal
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes) (hq : (q : ℕ) = p)
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
      = finrank (ZMod p) M.ρ.invariants
        + finrank (ZMod p)
            (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q))).ρ.invariants
        + finrank (ZMod p) M := by sorry

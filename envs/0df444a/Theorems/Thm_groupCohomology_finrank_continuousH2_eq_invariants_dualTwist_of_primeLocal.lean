-- Prove2me | Theorems.Thm_groupCohomology_finrank_continuousH2_eq_invariants_dualTwist_of_primeLocal
-- name    : groupCohomology.finrank_continuousH2_eq_invariants_dualTwist_of_primeLocal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/d5585ec5-32ca-5cc6-b34c-593226d2133a
-- title:
--   Local duality in degrees 2 and 0: dimension form
-- statement:
--   Let $p$ be a prime and let $q$ be a prime with $(q:\mathbb{N}) = p$. Let $M$ be a representation over $\mathbb{Z}/p$ of `primeLocalGaloisGroup q`, the group of $\mathbb{Q}_q$-algebra automorphisms of the chosen algebraic closure `PadicAlgCl q` of $\mathbb{Q}_q$, and assume $M$ is finite-dimensional over $\mathbb{Z}/p$. Assume further the smoothness hypothesis `hsm`: for every $m \in M$ there is an intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite over $\mathbb{Q}$, such that every $s$ whose image $\mathrm{primeLocalToGlobal}\,q\,(s)$ (restriction of scalars to $\mathbb{Q}$, followed by restriction to $\overline{\mathbb{Q}}$) lies in the fixing subgroup of $F$ satisfies $M.\rho(s)m = m$. Assume finally that `continuousH2 (primeLocalToGlobal q) M`, the quotient of the level-$2$ cocycles taken relative to `primeLocalToGlobal q` by the level-$2$ coboundaries they contain, is finite-dimensional over $\mathbb{Z}/p$. Then its $\mathbb{Z}/p$-dimension equals the dimension of the space of invariants of the representation $M^{\vee}$ twisted by the character $\sigma \mapsto (\mathrm{cycloChar}\,p)(\mathrm{primeLocalToGlobal}\,q\,(\sigma))$, i.e. of $\mathrm{Hom}(M,\mu_p)$.
--
--   This is the dimension form of Tate local duality in degrees $2$ and $0$ for a finite $\mathbb{F}_p$-representation of the local Galois group at $q$: $\dim H^2(\mathbb{Q}_q, M) = \dim H^0(\mathbb{Q}_q, \mathrm{Hom}(M,\mu_p))$. It feeds the local dimension counts used downstream, being cited by [`groupCohomology.finrank_cocycles_level_le_two_of_finrank_eq_one_of_not_cyclotomic`](thm.html#groupCohomology.finrank_cocycles_level_le_two_of_finrank_eq_one_of_not_cyclotomic) and by [`groupCohomology.finrank_finiteQuotientH1_eq_invariants_add_dualTwist_add_finrank_of_primeLocal`](thm.html#groupCohomology.finrank_finiteQuotientH1_eq_invariants_add_dualTwist_add_finrank_of_primeLocal).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_finrank_continuousH2_eq_invariants_dualTwist_of_primeLocal.lean

import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.finrank_continuousH2_eq_invariants_dualTwist_of_primeLocal
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes) (hq : (q : ℕ) = p)
    (M : Rep (ZMod p) (primeLocalGaloisGroup q))
    [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ),
      FiniteDimensional ℚ F ∧
        ∀ s, primeLocalToGlobal q s ∈ F.fixingSubgroup → M.ρ s m = m)
    [FiniteDimensional (ZMod p) (continuousH2 (primeLocalToGlobal q) M)] :
    finrank (ZMod p) (continuousH2 (primeLocalToGlobal q) M)
      = finrank (ZMod p)
          (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q))).ρ.invariants := by sorry

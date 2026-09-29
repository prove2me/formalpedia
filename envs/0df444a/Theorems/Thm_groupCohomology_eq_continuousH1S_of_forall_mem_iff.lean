-- Prove2me | Theorems.Thm_groupCohomology_eq_continuousH1S_of_forall_mem_iff
-- name    : groupCohomology.eq_continuousH1S_of_forall_mem_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/95dea5a0-43f7-551e-900b-6b90956be55e
-- title:
--   Locally constant classes unramified outside S give H¹(G_S,M)
-- statement:
--   Let $k$ be a commutative ring, $S$ a finite set of rational primes, and $M$ a $k$-linear representation of $\Gamma = \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, realised as the group of $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`. Assume $M$ is unramified outside $S$ in the following sense: for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$ (the predicate [`ValuationSubring.LiesOverPrime`](def/FLTPrelim_Ramification.html#L16)), every $g$ in `A.inertiaSubgroupIn ℚ` — the image in $\Gamma$ of the inertia subgroup of $A$ over $\mathbb{Q}$ under the inclusion of the decomposition subgroup — satisfies $\rho_M(g) = 1$. Let $\mathrm{adm}$ be a $k$-submodule of $H^1(\Gamma, M)$ which is characterised by the property that a class $x$ lies in $\mathrm{adm}$ precisely when $x = H^1\pi(c)$ for some $1$-cocycle $c \in$ `cocycles₁ M` whose underlying function $\Gamma \to M$ is locally constant and which is a coboundary locally outside $S$: for each prime $q \notin S$ and each valuation subring $A$ lying over $q$ there exists $m \in M$ with $c(g) = \rho_M(g)m - m$ for all $g$ in `A.inertiaSubgroupIn ℚ`. The conclusion is that $\mathrm{adm}$ equals `continuousH1S S M`, the image under $H^1\pi$ of the submodule `levelCocyclesS₁ S M` of $1$-cocycles.
--
--   This identifies the admissible submodule of $H^1(\Gamma,M)$ cut out by local coboundary conditions at the primes outside $S$ with the restricted-ramification group $H^1(G_S,M)$ in the form `continuousH1S`, whose cocycles are right-invariant under the fixing subgroup of a finite subextension of $\overline{\mathbb{Q}}/\mathbb{Q}$ that absorbs all inertia above primes outside $S$. It is used when the Greenberg–Wiles formula and the Poitou–Tate style selmer-group computations over $\mathbb{Q}$ are applied to Taylor–Wiles systems, for instance by [`groupCohomology.greenbergWiles_eq_unramifiedMenu_extArithLoc`](thm.html#groupCohomology.greenbergWiles_eq_unramifiedMenu_extArithLoc) and by the construction of Taylor–Wiles primes bounding the rank of the space of dual-number classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_eq_continuousH1S_of_forall_mem_iff.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.eq_continuousH1S_of_forall_mem_iff
    {k : Type} [CommRing k] (S : Finset Nat.Primes)
    (M : Rep k (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hMur : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ, M.ρ g = 1)
    (adm : Submodule k (H1 M))
    (hadm : ∀ x : H1 M, x ∈ adm ↔
      ∃ c : cocycles₁ M, IsLocallyConstant ⇑c ∧
        (∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
          A.LiesOverPrime (q : ℕ) → ∃ m : M, ∀ g ∈ A.inertiaSubgroupIn ℚ, c g = M.ρ g m - m) ∧
        H1π M c = x) :
    adm = continuousH1S S M := by sorry

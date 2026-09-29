-- Prove2me | Theorems.Thm_groupCohomology_exists_level_sylow_of_primeLocal
-- name    : groupCohomology.exists_level_sylow_of_primeLocal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/c9309ca0-de78-516a-ad25-38f56735dcae
-- title:
--   Level and Sylow data for a smooth local 𝔽ₚ-representation
-- statement:
--   Fix a prime $p$ (as a `Fact`) and a prime $q$, and write $G_q$ for `primeLocalGaloisGroup q`, the group of $\mathbb{Q}_q$-algebra automorphisms of a fixed algebraic closure `PadicAlgCl q` of $\mathbb{Q}_q$, together with the homomorphism $r_q =$ `primeLocalToGlobal q` to $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) = (\mathrm{AlgebraicClosure}\,\mathbb{Q} \simeq_{\mathbb{Q}} \mathrm{AlgebraicClosure}\,\mathbb{Q})$ obtained by restricting scalars to $\mathbb{Q}$ and then restricting the resulting automorphism to the normal subextension $\overline{\mathbb{Q}}$. Let $M$ be a representation of $G_q$ over $\mathbb{Z}/p$ that is finite-dimensional over $\mathbb{Z}/p$, and assume smoothness in the pointwise form: for each $m \in M$ there is an intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite over $\mathbb{Q}$, with $M.\rho(s)m = m$ for every $s \in G_q$ such that $r_q(s)$ lies in the fixing subgroup of $F$. The conclusion asserts the existence of subgroups $U \le S$ of $G_q$ such that: $U$ is normal in $G_q$; there is an intermediate field $F_0$, finite over $\mathbb{Q}$, whose fixing subgroup pulls back along $r_q$ into $U$; $S$ has finite index and $[G_q:S]$ is a unit in $\mathbb{Z}/p$; every $s \in S$ satisfies $s^{p^n} \in U$ for some $n \in \mathbb{N}$; $U$ acts trivially on $M$; and $(\mathrm{cycloChar}\,p)(r_q(u)) = 1$ for every $u \in U$, where `cycloChar p` is the mod-$p$ cyclotomic character of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ given by the modular cyclotomic character.
--
--   This packages the standard reduction data for the cohomology of a finite smooth $\mathbb{F}_p$-representation of the local Galois group at $q$: an open normal subgroup $U$ acting trivially on $M$ and on the $p$-th roots of unity, sitting inside a subgroup $S$ of index prime to $p$ with $S/U$ a finite $p$-group, so that restriction–corestriction and a dévissage over $S/U$ become available. It is used in the proof of [`groupCohomology.bijective_theta_dualTwist_of_primeLocal`](thm.html#groupCohomology.bijective_theta_dualTwist_of_primeLocal), the local Tate duality input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_level_sylow_of_primeLocal.lean

import Definitions.Def_ExtEndgame_ProductionDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.exists_level_sylow_of_primeLocal
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes)
    (M : Rep (ZMod p) (primeLocalGaloisGroup q)) [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, primeLocalToGlobal q s ∈ F.fixingSubgroup → M.ρ s m = m) :
    ∃ (U S : Subgroup (primeLocalGaloisGroup q)),
      U ≤ S ∧ U.Normal ∧
      (∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
        F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ U) ∧
      S.FiniteIndex ∧ IsUnit ((S.index : ℕ) : ZMod p) ∧
      (∀ s : primeLocalGaloisGroup q, s ∈ S → ∃ n : ℕ, s ^ (p ^ n) ∈ U) ∧
      (∀ u : primeLocalGaloisGroup q, u ∈ U → ∀ m : M, M.ρ u m = m) ∧
      (∀ u : primeLocalGaloisGroup q, u ∈ U → (cycloChar p) (primeLocalToGlobal q u) = 1) := by sorry

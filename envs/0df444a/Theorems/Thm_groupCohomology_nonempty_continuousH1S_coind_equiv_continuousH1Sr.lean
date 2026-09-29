-- Prove2me | Theorems.Thm_groupCohomology_nonempty_continuousH1S_coind_equiv_continuousH1Sr
-- name    : groupCohomology.nonempty_continuousH1S_coind_equiv_continuousH1Sr
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/c8c26fe9-6423-5fda-8d63-626c3baf5c61
-- title:
--   Shapiro's lemma for H¹ with ramification restricted to S
-- statement:
--   Fix a prime $p$ and a finite set $S$ of rational primes. Let $K$ be an intermediate field of $\overline{\mathbb{Q}}/\mathbb{Q}$ (inside `AlgebraicClosure ℚ`) which is unramified outside $S$ in the sense of [`IntermediateField.IsUnramifiedOutside`](def/GroupCohomology_ContinuousUnramified.html#L16): $K$ is finite-dimensional over $\mathbb{Q}$, and for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ in the nonunits of $A$, the image in $\mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ over $\mathbb{Q}$ is contained in the fixing subgroup $\Gamma_K = K.\mathrm{fixingSubgroup}$. Let $N$ be a representation of $\Gamma_K$ on a finite-dimensional $\mathbb{Z}/p$-vector space, and assume that every vector $n \in N$ is stabilised by an open subgroup of $S$-level type: there is an intermediate field $F$, unramified outside $S$ in the same sense, such that every $s \in \Gamma_K$ whose underlying automorphism lies in $F.\mathrm{fixingSubgroup}$ satisfies $\rho(s)\,n = n$. The conclusion asserts that a certain type is nonempty, namely that there exists a $\mathbb{Z}/p$-linear isomorphism between `continuousH1S S` applied to the representation of $\mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ coinduced from $N$ along the inclusion $\Gamma_K \hookrightarrow \mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ — that is, the image under `H1π` of the submodule of $1$-cocycles cut out by `levelCocyclesS₁ S` — and `continuousH1Sr` for that same inclusion, $S$ and $N$, the image under `H1π` of the submodule of $1$-cocycles cut out by `levelCocyclesSr₁`. No isomorphism is named; only its existence is asserted.
--
--   This is Shapiro's lemma in degree one, adapted to cohomology with ramification restricted to $S$: the $S$-restricted $H^1$ of a coinduced module over the absolute group agrees with the $S$-restricted $H^1$ of the subgroup $\Gamma_K$ acting on $N$. It feeds the corresponding dimension count in degree two, [`groupCohomology.finiteDimensional_continuousH2S_coind_and_finrank_eq`](thm.html#groupCohomology.finiteDimensional_continuousH2S_coind_and_finrank_eq), and hence the Euler-characteristic bookkeeping for the restricted-ramification cohomology groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_nonempty_continuousH1S_coind_equiv_continuousH1Sr.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Module groupCohomology

theorem groupCohomology.nonempty_continuousH1S_coind_equiv_continuousH1Sr
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (hK : K.IsUnramifiedOutside S)
    (N : Rep.{0} (ZMod p) ↥K.fixingSubgroup) [FiniteDimensional (ZMod p) N]
    (hN : ∀ n : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
      ∀ s : ↥K.fixingSubgroup, (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ F.fixingSubgroup → N.ρ s n = n) :
    Nonempty (continuousH1S S (Rep.coind K.fixingSubgroup.subtype N)
      ≃ₗ[ZMod p] continuousH1Sr K.fixingSubgroup.subtype S N) := by sorry

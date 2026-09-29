-- Prove2me | Theorems.Thm_groupCohomology_nonempty_continuousH2S_coind_equiv_continuousH2Sr
-- name    : groupCohomology.nonempty_continuousH2S_coind_equiv_continuousH2Sr
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/771d1e0f-f040-5c07-a3a1-dc07431afd24
-- title:
--   Degree-two Shapiro isomorphism for S-level cohomology
-- statement:
--   Let $p$ be a prime, let $S$ be a finite set of rational primes, and let $K$ be an intermediate field of $\mathbb{Q}$ in $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` which is unramified outside $S$ in the sense of [`IntermediateField.IsUnramifiedOutside`](def/GroupCohomology_ContinuousUnramified.html#L16), namely $K/\mathbb{Q}$ is finite-dimensional and, for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ over $\mathbb{Q}$ (transported from the decomposition subgroup by its inclusion) lies in the fixing subgroup of $K$. Let $N$ be a representation of the fixing subgroup $\Gamma_K$ of $K$ over $\mathbb{Z}/p$, finite-dimensional over $\mathbb{Z}/p$, and assume that every vector $n$ of $N$ is an $S$-level vector: there is an intermediate field $F$, unramified outside $S$ in the same sense, such that every $s \in \Gamma_K$ whose underlying automorphism of $\overline{\mathbb{Q}}$ fixes $F$ pointwise satisfies $N.\rho(s)\,n = n$. The conclusion asserts that the type of $\mathbb{Z}/p$-linear equivalences between `continuousH2S S (Rep.coind K.fixingSubgroup.subtype N)` — the quotient of the submodule `levelCocyclesS₂ S` of the coinduced representation of the full group $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ by the part of it lying in `levelCoboundariesS₂ S` — and the corresponding level carrier `continuousH2Sr K.fixingSubgroup.subtype S N` for $N$ along the inclusion $\Gamma_K \hookrightarrow \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ is nonempty; no particular isomorphism is named.
--
--   This is the degree-two case of Shapiro's lemma for cohomology with ramification restricted to $S$, identifying the $S$-level $H^2$ of a coinduced module over the absolute Galois group of $\mathbb{Q}$ with the $S$-level $H^2$ of the original module over the fixing subgroup of $K$. It is used by [`groupCohomology.finiteDimensional_continuousH2S_coind_and_finrank_eq`](thm.html#groupCohomology.finiteDimensional_continuousH2S_coind_and_finrank_eq), in the computation of the global Euler characteristic that underlies the Greenberg–Wiles style dimension counts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_nonempty_continuousH2S_coind_equiv_continuousH2Sr.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Module groupCohomology

theorem groupCohomology.nonempty_continuousH2S_coind_equiv_continuousH2Sr
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (hK : K.IsUnramifiedOutside S)
    (N : Rep.{0} (ZMod p) ↥K.fixingSubgroup) [FiniteDimensional (ZMod p) N]
    (hN : ∀ n : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
      ∀ s : ↥K.fixingSubgroup, (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ F.fixingSubgroup → N.ρ s n = n) :
    Nonempty (continuousH2S S (Rep.coind K.fixingSubgroup.subtype N)
      ≃ₗ[ZMod p] continuousH2Sr K.fixingSubgroup.subtype S N) := by sorry

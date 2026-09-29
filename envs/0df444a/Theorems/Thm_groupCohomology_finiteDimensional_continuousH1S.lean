-- Prove2me | Theorems.Thm_groupCohomology_finiteDimensional_continuousH1S
-- name    : groupCohomology.finiteDimensional_continuousH1S
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/5b8cd7f1-91f3-5578-9fe9-f6152e7d472e
-- title:
--   Finite-dimensionality of H¹ with restricted ramification
-- statement:
--   Let $p$ be a prime, so that $\mathbb{Z}/p$ is a field, and let $S$ be a finite set of prime numbers. Let $M$ be an object of `Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)`, that is, a $\mathbb{Z}/p$-linear representation of the absolute Galois group of $\mathbb{Q}$ taken concretely as the group of $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`, and assume that $M$ is finite-dimensional over $\mathbb{Z}/p$. Assume moreover the smoothness hypothesis `hsm`: for every vector $m \in M$ there is an intermediate field $F$ with $\mathbb{Q} \subseteq F \subseteq \overline{\mathbb{Q}}$ which is finite-dimensional over $\mathbb{Q}$ and such that $\rho(s)m = m$ for every $s$ in the fixing subgroup of $F$, i.e. $m$ is fixed by $\mathrm{Gal}(\overline{\mathbb{Q}}/F)$. The conclusion is that the $\mathbb{Z}/p$-submodule `continuousH1S S M` of $H^1(M)$ is finite-dimensional over $\mathbb{Z}/p$; by definition this submodule is the image, under the projection `H1π M` from one-cocycles to $H^1$, of the submodule `levelCocyclesS₁ S M` of those one-cocycles of $M$ that are of finite level and unramified outside $S$.
--
--   This is the degree-one finiteness statement for Galois cohomology with restricted ramification over $\mathbb{Q}$ (as in Neukirch–Schmidt–Wingberg, Theorem 8.3.20 in degree one), for a finite smooth $\mathbb{F}_p$-representation. It underlies the counting arguments used to produce Taylor–Wiles primes, and the corresponding finiteness in degree two.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_finiteDimensional_continuousH1S.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.finiteDimensional_continuousH1S
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s m = m) :
    FiniteDimensional (ZMod p) (continuousH1S S M) := by sorry

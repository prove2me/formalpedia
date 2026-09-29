-- Prove2me | Theorems.Thm_groupCohomology_finiteDimensional_continuousH1_and_continuousH2_of_isOpen_of_primeLocal
-- name    : groupCohomology.finiteDimensional_continuousH1_and_continuousH2_of_isOpen_of_primeLocal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/7318cf3a-4c84-5ca7-b2dc-ec0a4ed8fcdb
-- title:
--   Finiteness of continuous H¹ and H² for local Galois groups
-- statement:
--   Fix a prime $p$ and a prime $q$. Write $G_q$ for the group `primeLocalGaloisGroup q` of $\mathbb{Q}_q$-algebra automorphisms of the algebraic closure `PadicAlgCl` $q$ of $\mathbb{Q}_q$, and let `primeLocalToGlobal` $q$ be the homomorphism $G_q \to \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ obtained by restricting scalars to $\mathbb{Q}$ and then restricting an automorphism to the normal subextension $\overline{\mathbb{Q}}$. The assertion is universally quantified: for every subgroup $S \le G_q$ such that there is an intermediate field $F_0$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, whose fixing subgroup pulls back along `primeLocalToGlobal` $q$ into $S$; and for every representation $N$ of $S$ over $\mathbb{Z}/p$ (an object of `Rep.{0} (ZMod p) S`) such that each vector $n \in N$ admits a finite-dimensional intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ with $\rho(s)n = n$ for all $s \in S$ whose image under $r :=$ `primeLocalToGlobal` $q$ composed with the inclusion of $S$ lies in the fixing subgroup of $F$, and such that $N$ is finite-dimensional over $\mathbb{Z}/p$: both the submodule `continuousH1 r N` of $H^1(S,N)$, namely the image of the level-one cocycles `levelCocycles₁ r N` under the projection to $H^1$, and the quotient `continuousH2 r N` of `levelCocycles₂ r N` by the level-two coboundaries intersected with it, are finite-dimensional over $\mathbb{Z}/p$.
--
--   This is the local finiteness statement for continuous cohomology in degrees one and two of a smooth finite $\mathbb{F}_p$-representation of an open subgroup of a local Galois group, packaged with the quantifiers and premises in exactly the shape required as an input hypothesis elsewhere. It is used by [`groupCohomology.finrank_continuousClasses_eq_invariants_add_continuousH2_add_finrank_of_primeLocal`](thm.html#groupCohomology.finrank_continuousClasses_eq_invariants_add_continuousH2_add_finrank_of_primeLocal), the local Euler–Poincaré identity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_finiteDimensional_continuousH1_and_continuousH2_of_isOpen_of_primeLocal.lean

import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.finiteDimensional_continuousH1_and_continuousH2_of_isOpen_of_primeLocal
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes) :
    ∀ (S : Subgroup (primeLocalGaloisGroup q)),
      (∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
        F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S) →
      ∀ (N : Rep.{0} (ZMod p) S),
        (∀ n : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ s : S, ((primeLocalToGlobal q).comp S.subtype) s ∈ F.fixingSubgroup → N.ρ s n = n) →
        FiniteDimensional (ZMod p) N →
        FiniteDimensional (ZMod p) (continuousH1 ((primeLocalToGlobal q).comp S.subtype) N) ∧
          FiniteDimensional (ZMod p) (continuousH2 ((primeLocalToGlobal q).comp S.subtype) N) := by sorry

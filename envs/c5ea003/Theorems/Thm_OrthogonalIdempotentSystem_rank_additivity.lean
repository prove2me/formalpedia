-- Prove2me | Theorems.Thm_OrthogonalIdempotentSystem_rank_additivity
-- name    : OrthogonalIdempotentSystem.rank_additivity
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:34:40.306889+00:00
-- url     : https://prove2.me/theorems/775547ea-d2ab-4061-a901-d6800c8c0082
-- title:
--   Rank additivity
-- statement:
--   Formal statement of `OrthogonalIdempotentSystem.rank_additivity` from the Aether Catalog (Geometry). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem OrthogonalIdempotentSystem.rank_additivity{n : ℕ} (S : OrthogonalIdempotentSystem F V n)
--       [FiniteDimensional F V] :
--       finrank F V = ∑ i : Fin n, finrank F (S.gradedPiece i) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/NeuralCoding/StandardConjectures.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/NeuralCoding/StandardConjectures.lean#L112

-- Thm stub generated from Geometry/NeuralCoding/StandardConjectures.lean
import Mathlib
import Definitions.Def_Geometry_NeuralCoding_StandardConjectures
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Algebraic Skeleton of Grothendieck's Standard Conjectures

This file formalizes the linear-algebraic framework underlying Grothendieck's standard
conjectures on algebraic cycles. The key insight is that many consequences of the
conjectures — rank additivity, Hodge index, weight filtration purity — can be proved
unconditionally using only linear algebra, without geometric input.

## Main Definitions

* `OrthogonalIdempotentSystem` — A system of pairwise orthogonal idempotent linear
  endomorphisms summing to the identity. Models Künneth projectors.

* `LefschetzOperator` — A nilpotent linear operator modeling the action of a hyperplane
  class on cohomology.

* `SignedInnerProductSpace` — A finite-dimensional real inner product space with a
  decomposition into positive and negative definite subspaces, modeling the Hodge
  index theorem.

* `WeightFiltration` — An ascending filtration on a vector space modeling the weight
  filtration on mixed Hodge structures / mixed motives.

## Main Results

* `rank_additivity` — For an orthogonal idempotent system, rank is additive:
  `∑ rank(πᵢ) = dim(V)`.

* `hodge_index_signature_bound` — The Hodge index theorem: a nondegenerate
  symmetric bilinear form on a Lefschetz module has signature constrained by
  the Hard Lefschetz property.

* `lefschetz_kernel_filtration` — The kernels of powers of a Lefschetz operator
  form a strictly increasing filtration until stabilizing.

* `weight_purity_of_direct_sum` — Weight filtration respects direct sums.

## References

* Grothendieck, "Standard Conjectures on Algebraic Cycles" (1969)
* Kleiman, "The Standard Conjectures" (1994)
* André, "Une introduction aux motifs" (2004)
-/

noncomputable section

open Finset BigOperators LinearMap Module

/-! ## Part I: Orthogonal Idempotent Systems (Künneth Projectors) -/


open OrthogonalIdempotentSystem

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]


/-
**Idempotent Range Characterization.**
The range of an idempotent is exactly its fixed-point set.
-/

/-
**Direct Sum Decomposition.**
The graded pieces form a direct sum: the sum of any two distinct pieces
intersects trivially.
-/

/-
**Rank Additivity Theorem (Künneth).**
For a finite-dimensional vector space with an orthogonal idempotent system,
the dimension equals the sum of the ranks of the projectors.

This is the formal skeleton of the Künneth decomposition: the total Betti
number equals the sum of the individual Betti numbers. In the motivic setting,
this proves that the Künneth projectors account for all of cohomology.
-/

theorem OrthogonalIdempotentSystem.rank_additivity{n : ℕ} (S : OrthogonalIdempotentSystem F V n)
    [FiniteDimensional F V] :
    finrank F V = ∑ i : Fin n, finrank F (S.gradedPiece i) := by sorry

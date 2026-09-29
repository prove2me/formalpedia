-- Prove2me | Definitions.Def_Geometry_AbstractAlgebra_BallaEquiangular
-- name    : Geometry_AbstractAlgebra_BallaEquiangular
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T23:32:56.221705+00:00
-- url     : https://prove2.me/theorems/be467e9b-35ef-4c0e-b8af-5fcbc7bc94ac
-- title:
--   Aether Catalog definitions — Geometry_AbstractAlgebra_BallaEquiangular
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.AbstractAlgebra.BallaEquiangular`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/AbstractAlgebra/BallaEquiangular.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Balla's bound `N ≤ d²` for equiangular line systems

A family of `N` unit vectors in `ℝ^d` is *equiangular* with common angle `α` when
`|⟨vᵢ, vⱼ⟩| = α` for all `i ≠ j`.  This file proves the classical bound that such a
family can have at most `d²` members.

The argument is the **tensor-square lift**.  To each unit vector `v ∈ ℝ^d` we
associate its tensor square `tsq v ∈ ℝ^{d²}`, whose coordinates are the products
`vₐ·v_b`.  The fundamental property is
`⟨tsq u, tsq v⟩ = ⟨u, v⟩²` (`tsq_inner`),
so the Gram matrix of the lifted vectors has constant diagonal `1` and constant
off-diagonal `α²`.

Rather than diagonalising this Gram matrix, we use the elementary **quadratic-form
identity** for constant-pattern matrices
`∑ᵢⱼ xᵢ Gᵢⱼ xⱼ = (1 - c)·∑ᵢ xᵢ² + c·(∑ᵢ xᵢ)²`  (`constPattern_quadForm`),
from which positive-definiteness (`constPattern_posDef`) is immediate when
`0 ≤ c < 1`.  Positive-definiteness of the Gram form forces the lifted vectors to be
linearly independent, and the rank bound in `ℝ^{d²}` yields `N ≤ d²`.
-/

open scoped RealInnerProductSpace

namespace BallaEquiangular

variable {d : ℕ}

/-- The **tensor square** of a vector `v ∈ ℝ^d`: the vector in `ℝ^{d²}` whose
coordinate at `p` is `v_a · v_b`, where `(a, b)` is the pair corresponding to `p`
under `finProdFinEquiv`. -/
noncomputable def tsq (v : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin (d * d)) :=
  (WithLp.equiv 2 (Fin (d * d) → ℝ)).symm
    (fun p => v (finProdFinEquiv.symm p).1 * v (finProdFinEquiv.symm p).2)


/-! ## Stage 1 — The tensor-square inner product -/



/-! ## Stage 2 — Off-diagonal Gram entries -/


/-! ## Stage 3 — Quadratic form of constant-pattern matrices -/



/-! ## Stage 4 — Balla's bound -/


end BallaEquiangular



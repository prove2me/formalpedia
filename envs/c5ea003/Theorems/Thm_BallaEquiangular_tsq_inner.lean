-- Prove2me | Theorems.Thm_BallaEquiangular_tsq_inner
-- name    : BallaEquiangular.tsq_inner
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:04:45.843609+00:00
-- url     : https://prove2.me/theorems/2813861e-6250-421d-8de9-44acbbdb1952
-- title:
--   Tensor-square inner product.
-- statement:
--   **Tensor-square inner product.**  `⟨tsq u, tsq v⟩ = ⟨u, v⟩²`.
--
--   ```lean
--   theorem BallaEquiangular.tsq_inner(u v : EuclideanSpace ℝ (Fin d)) : ⟪tsq u, tsq v⟫ = ⟪u, v⟫ ^ 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/AbstractAlgebra/BallaEquiangular.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/AbstractAlgebra/BallaEquiangular.lean#L44

-- Thm stub generated from Geometry/AbstractAlgebra/BallaEquiangular.lean
import Mathlib
import Definitions.Def_Geometry_AbstractAlgebra_BallaEquiangular
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

open BallaEquiangular

variable {d : ℕ}



/-! ## Stage 1 — The tensor-square inner product -/

theorem BallaEquiangular.tsq_inner(u v : EuclideanSpace ℝ (Fin d)) : ⟪tsq u, tsq v⟫ = ⟪u, v⟫ ^ 2 := by sorry

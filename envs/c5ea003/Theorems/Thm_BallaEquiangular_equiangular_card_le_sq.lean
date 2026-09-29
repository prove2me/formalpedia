-- Prove2me | Theorems.Thm_BallaEquiangular_equiangular_card_le_sq
-- name    : BallaEquiangular.equiangular_card_le_sq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:04:50.197905+00:00
-- url     : https://prove2.me/theorems/95df01c6-0a5f-4b64-a6bd-1f297712ba9c
-- title:
--   Balla's bound.
-- statement:
--   **Balla's bound.**  A family of `N` unit vectors in `ℝ^d` that is equiangular
--   with common angle `α` (so `|⟨vᵢ, vⱼ⟩| = α` for `i ≠ j`), with `0 ≤ α < 1`, satisfies
--   `N ≤ d²`.
--
--   ```lean
--   theorem BallaEquiangular.equiangular_card_le_sq{N : ℕ} (v : Fin N → EuclideanSpace ℝ (Fin d))
--       {α : ℝ} (hunit : ∀ i, ‖v i‖ = 1) (hα0 : 0 ≤ α) (hα1 : α < 1)
--       (hang : ∀ i j, i ≠ j → |⟪v i, v j⟫| = α) : N ≤ d * d := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/AbstractAlgebra/BallaEquiangular.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/AbstractAlgebra/BallaEquiangular.lean#L129

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



/-! ## Stage 2 — Off-diagonal Gram entries -/


/-! ## Stage 3 — Quadratic form of constant-pattern matrices -/



/-! ## Stage 4 — Balla's bound -/

theorem BallaEquiangular.equiangular_card_le_sq{N : ℕ} (v : Fin N → EuclideanSpace ℝ (Fin d))
    {α : ℝ} (hunit : ∀ i, ‖v i‖ = 1) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hang : ∀ i j, i ≠ j → |⟪v i, v j⟫| = α) : N ≤ d * d := by sorry

-- Prove2me | Theorems.Thm_BallaEquiangular_constPattern_quadForm
-- name    : BallaEquiangular.constPattern_quadForm
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:04:38.698481+00:00
-- url     : https://prove2.me/theorems/19503d8f-a63e-4d3c-90f6-14bab4ed7e4e
-- title:
--   Quadratic form of a constant-pattern matrix.
-- statement:
--   **Quadratic form of a constant-pattern matrix.**  If `G` has diagonal `1` and
--   off-diagonal `c`, then for every `x`,
--   `∑ᵢⱼ xᵢ Gᵢⱼ xⱼ = (1 - c)·∑ᵢ xᵢ² + c·(∑ᵢ xᵢ)²`.
--
--   ```lean
--   theorem BallaEquiangular.constPattern_quadForm{N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (c : ℝ)
--       (hdiag : ∀ i, G i i = 1) (hoff : ∀ i j, i ≠ j → G i j = c) (x : Fin N → ℝ) :
--       ∑ i, ∑ j, x i * G i j * x j = (1 - c) * ∑ i, (x i) ^ 2 + c * (∑ i, x i) ^ 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/AbstractAlgebra/BallaEquiangular.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/AbstractAlgebra/BallaEquiangular.lean#L79

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

theorem BallaEquiangular.constPattern_quadForm{N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (c : ℝ)
    (hdiag : ∀ i, G i i = 1) (hoff : ∀ i j, i ≠ j → G i j = c) (x : Fin N → ℝ) :
    ∑ i, ∑ j, x i * G i j * x j = (1 - c) * ∑ i, (x i) ^ 2 + c * (∑ i, x i) ^ 2 := by sorry
